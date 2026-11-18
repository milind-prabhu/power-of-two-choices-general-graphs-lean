import GraphChoices.ThresholdGreedy
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! The threshold-load calculation in Section 4.2, with integer rounding.
Starting the scale index at zero only increases the bound, giving a factor 2
in front of the logarithmic term. -/
namespace GraphChoices.ThresholdGreedy
open Finset

 theorem finite_half_geometric (h : ℕ) :
    ∑ i ∈ range h, ((1:ℝ)/2)^i = 2 * (1 - ((1:ℝ)/2)^h) := by
  induction h with
  | zero => simp
  | succ h ih => rw [sum_range_succ, ih, pow_succ]; ring

 theorem inverse_powers_sum_le_two (h : ℕ) :
    ∑ i ∈ range h, (1:ℝ)/2^i ≤ 2 := by
  simp_rw [← one_div_pow]
  rw [finite_half_geometric]
  have : (0:ℝ) ≤ (1/2)^h := by positivity
  linarith

noncomputable def roundedThreshold (K L : ℝ) (i : ℕ) : ℕ :=
  ⌈K * (L / 2^i + 1)⌉₊

/-- An explicit version of sum alpha_i = O(K (L+h)), including ceil errors. -/
 theorem rounded_threshold_budget (K L : ℝ) (h : ℕ) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    (∑ i ∈ range h, (roundedThreshold K L i : ℝ)) ≤ K * (2*L+h) + h := by
  have hround (i : ℕ) : (roundedThreshold K L i : ℝ) ≤ K * (L / 2^i + 1) + 1 := by
    exact (Nat.ceil_lt_add_one (mul_nonneg hK (by positivity))).le
  calc
    _ ≤ ∑ i ∈ range h, (K * (L / 2^i + 1) + 1) := sum_le_sum fun i _ => hround i
    _ = K * (L * (∑ i ∈ range h, (1:ℝ)/2^i) + h) + h := by
      have heq (i : ℕ) : K * (L / 2^i + 1) + 1 = K*L*((1:ℝ)/2^i) + (K+1) := by ring
      simp_rw [heq]
      rw [sum_add_distrib, ← mul_sum]
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring
    _ ≤ K * (2*L+h) + h := by
      have hh := mul_le_mul_of_nonneg_left (inverse_powers_sum_le_two h) hL
      nlinarith

end GraphChoices.ThresholdGreedy
