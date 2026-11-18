import GraphChoices.PatternEmbeddingCount
import GraphChoices.ResidualTreeBound

/-! Combines the fixed-pattern assignment count with the actual residual-tree
probability bound. Embeddings carry real base-edge labels; uniqueness follows
from the base graph having at most one label per bipartite endpoint pair. -/
namespace GraphChoices.Patterns
open Finset
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [DecidableEq C]
  {T m : ℕ}

def childIndex (i : Fin m) : Fin (m+1) := ⟨i.val+1,by omega⟩

def parentIndex (p : ParentPattern C m) (i : Fin m) : Fin (m+1) :=
  ⟨(p.parent i).val,by have := (p.parent i).isLt; have := i.isLt; omega⟩

def EdgeData (p : ParentPattern C m) (encode : E → Arrival L R C)
    (f : Fin (m+1) → L ⊕ R) (g : Fin m → E) : Prop :=
  ∀ i, (encode (g i)).cls = p.cls i ∧
    if p.childLeft i then
      f (childIndex i) = Sum.inl (encode (g i)).left ∧
      f (parentIndex p i) = Sum.inr (encode (g i)).right
    else
      f (parentIndex p i) = Sum.inl (encode (g i)).left ∧
      f (childIndex i) = Sum.inr (encode (g i)).right

noncomputable def embeddingSet (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) :
    Finset ((Fin (m+1) → L ⊕ R) × (Fin m → E)) := by
  classical
  exact univ.filter fun fg => fg.1 ∈ patternAssignments p H ∧ Function.Injective fg.1 ∧ EdgeData p encode fg.1 fg.2

 theorem embedding_projection_inj (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right)) :
    Set.InjOn (fun fg : ((Fin (m+1) → L ⊕ R) × (Fin m → E)) => fg.1)
      (↑(embeddingSet p H encode) : Set _) := by
  classical
  intro a ha b hb hab
  change a.1 = b.1 at hab
  have hA := (mem_filter.mp ha).2.2.2
  have hB := (mem_filter.mp hb).2.2.2
  apply Prod.ext hab
  funext i
  apply hsimple
  have hx := (hA i).2
  have hy := (hB i).2
  rw [hab] at hx
  cases hs : p.childLeft i <;> simp only [hs, Bool.false_eq_true, if_false, if_true] at hx hy
  · exact Prod.ext (Sum.inl.inj (hx.1.symm.trans hy.1)) (Sum.inr.inj (hx.2.symm.trans hy.2))
  · exact Prod.ext (Sum.inl.inj (hx.1.symm.trans hy.1)) (Sum.inr.inj (hx.2.symm.trans hy.2))

 theorem embeddingSet_card_le (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right)) :
    (embeddingSet p H encode).card ≤ (patternAssignments p H).card := by
  classical
  exact card_le_card_of_injOn Prod.fst
    (fun fg hfg => (mem_filter.mp hfg).2.1) (embedding_projection_inj p H encode hsimple)

abbrev LeftChildren (p : ParentPattern C m) := {i : Fin m // p.childLeft i = true}

 theorem embedding_left_buckets_distinct (p : ParentPattern C m) (encode : E → Arrival L R C)
    (f : Fin (m+1) → L ⊕ R) (g : Fin m → E) (hf : Function.Injective f) (he : EdgeData p encode f g) :
    Function.Injective (fun j : LeftChildren p => ((encode (g j.val)).left,p.cls j.val)) := by
  intro j k hjk
  have hj := (he j.val).2
  have hk := (he k.val).2
  simp only [j.property, k.property, if_true] at hj hk
  have hl := congrArg Prod.fst hjk
  have hc : childIndex j.val = childIndex k.val := hf (hj.1.trans ((congrArg Sum.inl hl).trans hk.1.symm))
  apply Subtype.ext
  apply Fin.ext
  have hv := congrArg Fin.val hc
  simp only [childIndex] at hv
  omega

noncomputable def patternProbabilityFactor (p : ParentPattern C m) (α : C → ℕ)
    (DL : C → ℕ) (T : ℕ) : ℝ :=
  ((T:ℝ) / Fintype.card E)^m * ∏ j : LeftChildren p,
    (Real.exp 1 * T * (DL (p.cls j.val) : ℝ) / Fintype.card E / α (p.cls j.val))^(α (p.cls j.val))

 theorem embedding_probability_le (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (DL : C → ℕ)
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (fg : (Fin (m+1) → L ⊕ R) × (Fin m → E)) (hfg : fg ∈ embeddingSet p H encode) :
    eventProbability (fixedResidualEvent α encode T m fg.2) ≤ patternProbabilityFactor (E := E) p α DL T := by
  classical
  have hf := (mem_filter.mp hfg).2.2.1
  have he := (mem_filter.mp hfg).2.2.2
  have hp := fixedResidual_probability_le (T := T) (J := LeftChildren p) α encode fg.2
    (fun j => (encode (fg.2 j.val)).left) (fun j => p.cls j.val) (fun j => j.val)
    (fun j => ⟨rfl,(he j.val).1⟩) (embedding_left_buckets_distinct p encode fg.1 fg.2 hf he)
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply prod_le_prod
  · intro j _; positivity
  · intro j _
    apply pow_le_pow_left₀ (by positivity) _
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast hDL (encode (fg.2 j.val)).left (p.cls j.val)

noncomputable def residualPatternEvent (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (T : ℕ) : Finset (Fin T → E) :=
  (embeddingSet p H encode).biUnion fun fg => fixedResidualEvent α encode T m fg.2

/-- Fixed-pattern union bound combining the concrete embedding count and raw
residual-tree probability. Threshold parameter simplification is still separate. -/
 theorem residualPattern_probability_le (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (DL DR : C → ℕ) (D : ℕ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c) :
    eventProbability (residualPatternEvent p H encode α T) ≤
      (Fintype.card R * (∏ i : Fin m, if p.childLeft i then DR (p.cls i) else D) : ℕ) *
        patternProbabilityFactor (E := E) p α DL T := by
  classical
  have hP : 0 ≤ patternProbabilityFactor (E := E) p α DL T := by unfold patternProbabilityFactor; positivity
  calc
    _ ≤ ∑ fg ∈ embeddingSet p H encode, eventProbability (fixedResidualEvent α encode T m fg.2) := witness_union_bound _ _
    _ ≤ ∑ _fg ∈ embeddingSet p H encode, patternProbabilityFactor (E := E) p α DL T :=
      sum_le_sum fun fg hfg => embedding_probability_le p H encode α DL hDL fg hfg
    _ = (embeddingSet p H encode).card * patternProbabilityFactor (E := E) p α DL T := by simp
    _ ≤ (Fintype.card R * (∏ i : Fin m, if p.childLeft i then DR (p.cls i) else D) : ℕ) *
        patternProbabilityFactor (E := E) p α DL T := by
      apply mul_le_mul_of_nonneg_right _ hP
      exact_mod_cast (embeddingSet_card_le p H encode hsimple).trans (patternAssignments_card_le p H D DR hL hR)

end GraphChoices.Patterns
