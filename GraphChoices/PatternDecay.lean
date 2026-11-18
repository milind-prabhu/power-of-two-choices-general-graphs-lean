import GraphChoices.PatternEventBound
import GraphChoices.BalancedProduct

/-! Cancellation of branching factors against threshold-witness probabilities
for a left-heavy fixed pattern. Local numerical hypotheses are explicit; the
paper's chosen thresholds must still be shown to satisfy them. -/
namespace GraphChoices.Patterns
open Finset
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [DecidableEq C]
  {T m : ℕ}

 theorem weighted_branch_identity (p : ParentPattern C m) (D z : ℝ) (DR γ : C → ℝ) :
    (∏ i : Fin m, if p.childLeft i then DR (p.cls i) else D) *
      (z^m * ∏ j : LeftChildren p, γ (p.cls j.val)) =
    ∏ i : Fin m, if p.childLeft i then DR (p.cls i)*z*γ (p.cls i) else D*z := by
  classical
  rw [GraphChoices.subtype_product_as_ite (fun i : Fin m => p.childLeft i = true) (fun i => γ (p.cls i))]
  have hz : z^m = ∏ _i : Fin m, z := by simp
  rw [hz, ← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  cases h : p.childLeft i <;> simp [h, mul_assoc]

noncomputable def bucketDecay (α : C → ℕ) (DL : C → ℕ) (T : ℕ) (c : C) : ℝ :=
  (Real.exp 1 * T * (DL c : ℝ) / Fintype.card E / α c)^(α c)

/-- A fixed left-heavy pattern has geometric probability decay when the local
threshold tails beat their right branching factors. This combines actual
execution witnesses and the concrete graph-embedding count. -/
 theorem residualPattern_probability_decay (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (DL DR : C → ℕ) (D : ℕ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (b r : ℝ) (hb : 0 ≤ b) (hr : 0 ≤ r) (hbr : b ≤ r)
    (hpair : (D : ℝ)*((T:ℝ)/Fintype.card E)*b ≤ r^2)
    (hlocal : ∀ c, (DR c : ℝ)*((T:ℝ)/Fintype.card E)*bucketDecay (E := E) α DL T c ≤ b)
    (hheavy : m ≤ 2*(univ.filter fun i : Fin m => p.childLeft i = true).card) :
    eventProbability (residualPatternEvent p H encode α T) ≤ (Fintype.card R : ℝ)*r^m := by
  classical
  have hp := residualPattern_probability_le (T := T) p H encode α DL DR D hsimple hDL hL hR
  have heq :
      ((Fintype.card R * (∏ i : Fin m, if p.childLeft i then DR (p.cls i) else D) : ℕ) : ℝ) *
        patternProbabilityFactor (E := E) p α DL T =
      (Fintype.card R : ℝ) * (∏ i : Fin m, if p.childLeft i then
        (DR (p.cls i) : ℝ)*((T:ℝ)/Fintype.card E)*bucketDecay (E := E) α DL T (p.cls i)
        else (D:ℝ)*((T:ℝ)/Fintype.card E)) := by
    simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_ite, patternProbabilityFactor]
    rw [mul_assoc]
    exact congrArg (fun x : ℝ => (Fintype.card R : ℝ)*x)
      (weighted_branch_identity p (D:ℝ) ((T:ℝ)/Fintype.card E)
        (fun c => (DR c : ℝ)) (bucketDecay (E := E) α DL T))
  rw [heq] at hp
  calc
    _ ≤ _ := hp
    _ ≤ (Fintype.card R : ℝ) * (∏ i : Fin m, if p.childLeft i then b else (D:ℝ)*((T:ℝ)/Fintype.card E)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply prod_le_prod
      · intro i _
        split_ifs <;> (try dsimp only [bucketDecay]) <;> positivity
      · intro i _
        split_ifs
        · exact hlocal _
        · exact le_rfl
    _ ≤ (Fintype.card R : ℝ) * r^m := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [Fintype.card_fin] using GraphChoices.two_class_product_bound (fun i : Fin m => p.childLeft i = true)
        _ b r (by positivity) hb hr hpair hbr (by simpa using hheavy)

end GraphChoices.Patterns
