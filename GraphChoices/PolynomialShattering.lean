import GraphChoices.ComponentTreeEvents

/-! Explicit logarithmic cutoffs, inverse-polynomial failure probabilities,
and the expected-load consequence. The canonical-coverage containment remains
an explicit premise, so these are not unconditional shattering theorems. -/
namespace GraphChoices

def polynomialCutoff (N c : ℕ) : ℕ := (c+1)*(Nat.log 2 N+1)

theorem polynomialCutoff_pos (N c : ℕ) : 0 < polynomialCutoff N c := by
  unfold polynomialCutoff
  positivity

theorem polynomialCutoff_power (N c : ℕ) : N^(c+1) ≤ 2^polynomialCutoff N c := by
  have hN := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le
  calc
    _ ≤ (2^(Nat.log 2 N+1))^(c+1) := Nat.pow_le_pow_left hN _
    _ = _ := by rw [← pow_mul]; congr 1; unfold polynomialCutoff; ring

theorem geometric_tail_le_polynomial (N c k A : ℕ) (hN : 0 < N) (hA : A ≤ N)
    (hk : polynomialCutoff N c ≤ k) (r : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1/2) :
    (A:ℝ)*r^k ≤ 1/(N:ℝ)^c := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hexp : (N:ℝ)^(c+1) ≤ (2:ℝ)^k := by
    exact_mod_cast (polynomialCutoff_power N c).trans (Nat.pow_le_pow_right (by decide : 0 < 2) hk)
  calc
    _ ≤ (A:ℝ)*((1:ℝ)/2)^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrsmall k) (Nat.cast_nonneg _)
    _ = (A:ℝ)/(2:ℝ)^k := by rw [div_pow]; ring
    _ ≤ (N:ℝ)/(2:ℝ)^k := div_le_div_of_nonneg_right (by exact_mod_cast hA) (by positivity)
    _ ≤ (N:ℝ)/(N:ℝ)^(c+1) := div_le_div_of_nonneg_left hNr.le (by positivity) hexp
    _ = _ := by rw [pow_succ]; field_simp

end GraphChoices

namespace GraphChoices.Patterns
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

/-- Conditional component shattering with exact cutoff and failure constant.
The source of the remaining coverage assumption is stated in the module header. -/
theorem largeComponent_polynomial_tail_of_coverage (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (T D k B N c : ℕ)
    (hN : 0 < N) (hL : Fintype.card L ≤ N) (hR : Fintype.card R ≤ N)
    (hD : polynomialCutoff N c ≤ D+1) (hk : polynomialCutoff N c ≤ k)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(D+1) ≤ 1/2)
    (hcoverage : largeHeavyTreeEvent encode α T k ⊆ largeShapeEvent H encode α T k B)
    (hshape : ∀ j ≤ B, eventProbability (heavyShapeEvent H encode α T (k+j)) ≤
      (Fintype.card R : ℝ)/2^(k+j)) :
    eventProbability (largeComponentEvent encode α T ((D+1)*(k+1))) ≤ 3/(N:ℝ)^c := by
  have h := largeComponent_tail_of_canonical_coverage H encode α T D k B (1/2) hmean hcoverage hshape
  have hd := geometric_tail_le_polynomial N c (D+1) (Fintype.card L) hN hL hD (1/2) (by norm_num) le_rfl
  have hr := geometric_tail_le_polynomial N c k (Fintype.card R) hN hR hk (1/2) (by norm_num) le_rfl
  have heq : (Fintype.card R : ℝ)*((1:ℝ)/2)^k = (Fintype.card R : ℝ)/2^k := by
    rw [div_pow]; ring
  rw [heq] at hr
  calc
    _ ≤ _ := h
    _ = (Fintype.card L : ℝ)*((1:ℝ)/2)^(D+1) + 2*((Fintype.card R : ℝ)/2^k) := by ring
    _ ≤ 1/(N:ℝ)^c + 2*(1/(N:ℝ)^c) := add_le_add hd (mul_le_mul_of_nonneg_left hr (by norm_num))
    _ = _ := by ring

/-- The fully explicit expectation reduction from a canonical-coverage proof.
No main competitive result is claimed while that premise remains open. -/
theorem expected_load_polynomial_of_coverage (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (T D k B N c : ℕ)
    (hN : 0 < N) (hL : Fintype.card L ≤ N) (hR : Fintype.card R ≤ N)
    (hD : polynomialCutoff N c ≤ D+1) (hk : polynomialCutoff N c ≤ k)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(D+1) ≤ 1/2)
    (hcoverage : largeHeavyTreeEvent encode α T k ⊆ largeShapeEvent H encode α T k B)
    (hshape : ∀ j ≤ B, eventProbability (heavyShapeEvent H encode α T (k+j)) ≤
      (Fintype.card R : ℝ)/2^(k+j)) :
    expectedTotalMaxLoad encode α T ≤ (∑ c, (α c : ℝ)) +
      (2*(Nat.log 2 ((D+1)*(k+1))+1) : ℕ)*expectedReplayOpt encode T +
      3*T/(N:ℝ)^c := by
  have ht := largeComponent_polynomial_tail_of_coverage H encode α T D k B N c hN hL hR hD hk
    hmean hcoverage hshape
  have h := expected_load_of_component_tail encode α T _ _ ht
  convert h using 1 <;> ring

end GraphChoices.Patterns
