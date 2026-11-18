import GraphChoices.ResidualAdjacency
import GraphChoices.ShapePatterns

/-! From an injective vertex enumeration with parent edges to a counted
pattern event. The parent-before-child inequalities prove that edge labels
cannot repeat, even when consecutive tree edges reverse bipartite direction.
Constructing the canonical enumeration of every finite tree remains separate.
-/
namespace GraphChoices
open Finset

theorem menuValid_of_pointwise {V : Type*} [Fintype V] [DecidableEq V]
    (menu : (k : ℕ) → (Fin k → V) → Finset V) (n : ℕ) (f : Fin n → V)
    (h : ∀ i : Fin n, f i ∈ menu i.val (fun j => f ⟨j.val, by omega⟩)) :
    MenuValid menu n f := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · apply ih (Fin.init f)
      intro i
      exact h i.castSucc
    · exact h (Fin.last n)

end GraphChoices

namespace GraphChoices.Patterns
open Finset
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [DecidableEq C]
  {T m : ℕ}

theorem edgeData_labels_injective (p : ParentPattern C m) (encode : E → Arrival L R C)
    (f : Fin (m+1) → L ⊕ R) (g : Fin m → E)
    (hf : Function.Injective f) (he : EdgeData p encode f g) : Function.Injective g := by
  intro i j hij
  have hi := (he i).2
  have hj := (he j).2
  rw [hij] at hi
  have hpi := (p.parent i).isLt
  have hpj := (p.parent j).isLt
  cases hsi : p.childLeft i <;> cases hsj : p.childLeft j <;>
    simp only [hsi, hsj, Bool.false_eq_true, if_false, if_true] at hi hj
  · have hidx := congrArg Fin.val (hf (hi.2.trans hj.2.symm))
    apply Fin.ext
    simpa only [childIndex] using Nat.add_right_cancel hidx
  · have hidx1 := congrArg Fin.val (hf (hi.1.trans hj.1.symm))
    have hidx2 := congrArg Fin.val (hf (hi.2.trans hj.2.symm))
    simp only [childIndex, parentIndex] at hidx1 hidx2
    omega
  · have hidx1 := congrArg Fin.val (hf (hi.1.trans hj.1.symm))
    have hidx2 := congrArg Fin.val (hf (hi.2.trans hj.2.symm))
    simp only [childIndex, parentIndex] at hidx1 hidx2
    omega
  · have hidx := congrArg Fin.val (hf (hi.1.trans hj.1.symm))
    apply Fin.ext
    simpa only [childIndex] using Nat.add_right_cancel hidx

theorem edgeData_mem_assignments (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C)
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (f : Fin (m+1) → L ⊕ R) (g : Fin m → E)
    (hroot : ∃ v, f ⟨0, by omega⟩ = Sum.inr v) (he : EdgeData p encode f g) :
    f ∈ patternAssignments p H := by
  classical
  apply (mem_menuAssignments_iff _ _ _).mpr
  apply menuValid_of_pointwise
  intro k
  cases k with
  | mk k hk =>
    cases k with
    | zero =>
      obtain ⟨v, hv⟩ := hroot
      simp only [patternMenu, hv]
      exact mem_image.mpr ⟨v, mem_univ _, rfl⟩
    | succ k =>
      have hkm : k < m := by omega
      let i : Fin m := ⟨k, hkm⟩
      have hs : ((encode (g i)).left, (encode (g i)).right) ∈ H (p.cls i) := by
        rw [← (he i).1]
        exact hsource _
      have hed := (he i).2
      cases hi : p.childLeft i
      · simp only [hi, Bool.false_eq_true, if_false] at hed
        change f (childIndex i) ∈ patternMenu p H (k+1) _
        simp only [patternMenu, dif_pos hkm]
        change f (childIndex i) ∈ if p.childLeft i then _ else _
        rw [hi]
        simp only [Bool.false_eq_true, if_false]
        change f (childIndex i) ∈ match f (parentIndex p i) with
          | Sum.inl u => (Peeling.leftNeighbors (H (p.cls i)) u).image Sum.inr
          | Sum.inr _ => ∅
        rw [hed.1, hed.2]
        exact mem_image.mpr ⟨_, by simpa [Peeling.leftNeighbors] using hs, rfl⟩
      · simp only [hi, if_true] at hed
        change f (childIndex i) ∈ patternMenu p H (k+1) _
        simp only [patternMenu, dif_pos hkm]
        change f (childIndex i) ∈ if p.childLeft i then _ else _
        rw [hi]
        simp only [if_true]
        change f (childIndex i) ∈ match f (parentIndex p i) with
          | Sum.inl _ => ∅
          | Sum.inr v => (Peeling.rightNeighbors (H (p.cls i)) v).image Sum.inl
        rw [hed.2, hed.1]
        exact mem_image.mpr ⟨_, by simpa [Peeling.rightNeighbors] using hs, rfl⟩

/-- Geometric vertex data and actual residual occurrences imply membership
in the exact pattern event whose probability was already bounded. -/
theorem mem_residualPatternEvent_of_data (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ)
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (ω : Fin T → E) (f : Fin (m+1) → L ⊕ R) (g : Fin m → E)
    (hf : Function.Injective f) (hroot : ∃ v, f ⟨0, by omega⟩ = Sum.inr v)
    (he : EdgeData p encode f g)
    (hres : ∀ i, ∃ t : Fin T, ω t = g i ∧ residualTime α encode ω t) :
    ω ∈ residualPatternEvent p H encode α T := by
  classical
  apply mem_biUnion.mpr
  refine ⟨(f,g), mem_filter.mpr ⟨mem_univ _, ?_, hf, he⟩, ?_⟩
  · exact edgeData_mem_assignments p H encode hsource f g hroot he
  · exact (mem_fixedResidualEvent_iff α encode g (edgeData_labels_injective p encode f g hf he) ω).mpr hres

end GraphChoices.Patterns
