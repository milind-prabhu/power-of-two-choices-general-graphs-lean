import GraphChoices.Uniform

/-! Exact coordinate independence and the finite witness union bound used in
Section 4.2.2. These are probability primitives, not the paper's still-open
pattern-counting theorem. -/
namespace GraphChoices
open Finset

noncomputable def eventProbability {Ω : Type*} [Fintype Ω] (A : Finset Ω) : ℝ :=
  A.card / (Fintype.card Ω : ℝ)

 theorem eventProbability_nonneg {Ω : Type*} [Fintype Ω] (A : Finset Ω) :
    0 ≤ eventProbability A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

 theorem eventProbability_mono {Ω : Type*} [Fintype Ω] {A B : Finset Ω} (h : A ⊆ B) :
    eventProbability A ≤ eventProbability B := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card h

/-- Probability of a union is at most the sum of probabilities, with no
independence requirement on the witness events. -/
 theorem witness_union_bound {Ω W : Type*} [Fintype Ω] [DecidableEq Ω]
    (W₀ : Finset W) (events : W → Finset Ω) :
    eventProbability (W₀.biUnion events) ≤ ∑ w ∈ W₀, eventProbability (events w) := by
  unfold eventProbability
  have hc : ((W₀.biUnion events).card : ℝ) ≤ ∑ w ∈ W₀, ((events w).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  calc
    _ ≤ (∑ w ∈ W₀, ((events w).card : ℝ)) / Fintype.card Ω :=
      div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)
    _ = _ := by simp [div_eq_mul_inv, sum_mul]

/-- Product sampling has exact independence, including empty allowed sets.
A coordinate allows every edge label if it is unconstrained. -/
 theorem probability_coordinate_constraints {E : Type*} [Fintype E]
    [DecidableEq E] (T : ℕ) (allowed : Fin T → Finset E) :
    eventProbability (Fintype.piFinset allowed) =
      ∏ t : Fin T, ((allowed t).card : ℝ) / Fintype.card E := by
  simp only [eventProbability, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_prod, Nat.cast_pow, prod_div_distrib, prod_const, card_univ]

/-- A finite family of per-coordinate witness restrictions can be union-bounded
by the corresponding products of marginal probabilities. -/
 theorem witness_coordinate_union_bound {E W : Type*} [Fintype E] [DecidableEq E]
    (T : ℕ) (W₀ : Finset W) (allowed : W → Fin T → Finset E) :
    eventProbability (W₀.biUnion fun w => Fintype.piFinset (allowed w)) ≤
      ∑ w ∈ W₀, ∏ t : Fin T, ((allowed w t).card : ℝ) / Fintype.card E := by
  simpa only [probability_coordinate_constraints] using
    witness_union_bound W₀ (fun w => Fintype.piFinset (allowed w))

end GraphChoices
