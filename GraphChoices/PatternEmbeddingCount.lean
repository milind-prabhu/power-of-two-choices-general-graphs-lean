import GraphChoices.AssignmentCount
import GraphChoices.Peeling
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators

/-! Rooted class-labelled patterns in parent-before-child order, and a bound on
their graph assignments. Inconsistent bipartite side annotations simply have
no assignments. Injective embeddings form a subset of these assignments. -/
namespace GraphChoices.Patterns
open Finset
variable {L R C : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

structure ParentPattern (C : Type*) (m : ℕ) where
  parent : (i : Fin m) → Fin (i.val+1)
  cls : Fin m → C
  childLeft : Fin m → Bool

noncomputable def patternMenu {m : ℕ} (p : ParentPattern C m)
    (H : C → Peeling.Graph L R) : (k : ℕ) → (Fin k → L ⊕ R) → Finset (L ⊕ R)
  | 0, _ => univ.image Sum.inr
  | k+1, f => if hk : k < m then
      let i : Fin m := ⟨k,hk⟩
      if p.childLeft i then
        match f (p.parent i) with
        | Sum.inl _ => ∅
        | Sum.inr v => (Peeling.rightNeighbors (H (p.cls i)) v).image Sum.inl
      else
        match f (p.parent i) with
        | Sum.inl u => (Peeling.leftNeighbors (H (p.cls i)) u).image Sum.inr
        | Sum.inr _ => ∅
    else ∅

def branchBound {m : ℕ} (p : ParentPattern C m) (D : ℕ) (DR : C → ℕ) : ℕ → ℕ
  | 0 => Fintype.card R
  | k+1 => if hk : k < m then if p.childLeft ⟨k,hk⟩ then DR (p.cls ⟨k,hk⟩) else D else 0

 theorem patternMenu_card_le {m : ℕ} (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (D : ℕ) (DR : C → ℕ)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (k : ℕ) (f : Fin k → L ⊕ R) :
    (patternMenu p H k f).card ≤ branchBound (R := R) p D DR k := by
  cases k with
  | zero =>
    simpa only [patternMenu, branchBound, card_univ] using
      (card_image_le (s := (univ : Finset R)) (f := (Sum.inr : R → L ⊕ R)))
  | succ k =>
    by_cases hk : k < m
    · cases hs : p.childLeft ⟨k,hk⟩
      · cases hv : f (p.parent ⟨k,hk⟩) with
        | inl u =>
          simp only [patternMenu, branchBound, dif_pos hk, hs, Bool.false_eq_true, if_false, hv]
          exact card_image_le.trans (hL _ _)
        | inr v => simp [patternMenu, branchBound, hk, hs, hv]
      · cases hv : f (p.parent ⟨k,hk⟩) with
        | inl u => simp [patternMenu, branchBound, hk, hs, hv]
        | inr v =>
          simp only [patternMenu, branchBound, dif_pos hk, hs, if_true, hv]
          exact card_image_le.trans (hR _ _)
    · simp [patternMenu, branchBound, hk]

noncomputable def patternAssignments {m : ℕ} (p : ParentPattern C m) (H : C → Peeling.Graph L R) :
    Finset (Fin (m+1) → L ⊕ R) := GraphChoices.menuAssignments (patternMenu p H) (m+1)

/-- The fixed-pattern embedding count underlying Equation (8), before grouping
left vertices with equal edge classes. The right root has at most |R| choices. -/
 theorem patternAssignments_card_le {m : ℕ} (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (D : ℕ) (DR : C → ℕ)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c) :
    (patternAssignments p H).card ≤ Fintype.card R *
      ∏ i : Fin m, if p.childLeft i then DR (p.cls i) else D := by
  have hh := GraphChoices.menuAssignments_card_le (patternMenu p H)
    (branchBound (R := R) p D DR) (m+1) (fun k _ f => patternMenu_card_le p H D DR hL hR k f)
  unfold patternAssignments
  apply hh.trans_eq
  rw [prod_range_succ']
  rw [← Fin.prod_univ_eq_prod_range (fun k => branchBound (R := R) p D DR (k+1)) m]
  simp only [branchBound, Fin.isLt, dif_pos]
  rw [mul_comm]

end GraphChoices.Patterns
