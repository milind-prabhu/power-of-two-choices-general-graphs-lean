import GraphChoices.ExplicitThresholds
import GraphChoices.SkewDecomposition
import GraphChoices.ThresholdBudget

/-! Quantitative budget for the concrete sufficient thresholds at doubly
exponential scales. The logarithmic numerical condition is derived from a
multiplicative right-branching bound, rather than assumed as a conclusion.
-/
namespace GraphChoices
open Finset

theorem sufficientThreshold_upper (mean f z A B : ℝ)
    (hfm : 0 ≤ f*mean) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbase : f*mean ≤ A) (hlog : z ≤ B) :
    (sufficientThreshold mean f z : ℝ) ≤ A+B+2 := by
  have hnonneg : 0 ≤ max (f*mean) z := hfm.trans (le_max_left _ _)
  have hc := Nat.ceil_lt_add_one hnonneg
  have hm : max (f*mean) z ≤ A+B := max_le
    (hbase.trans (le_add_of_nonneg_right hB))
    (hlog.trans (le_add_of_nonneg_left hA))
  simp only [sufficientThreshold, Nat.cast_add, Nat.cast_one]
  linarith

theorem log_branching_bound (x f L σ K : ℝ)
    (hx : 0 ≤ x) (hf : 1 < f) (hL : 1 ≤ L) (hσ : 0 ≤ σ) (hK : 1 ≤ K)
    (hbranch : x ≤ K*(f*L)^(2*σ)) :
    Real.log x ≤ Real.log K + 2*σ*(Real.log f + Real.log L) := by
  have hfpos : 0 < f := by linarith
  have hLpos : 0 < L := by linarith
  have hKpos : 0 < K := by linarith
  by_cases hxpos : 0 < x
  · have h := Real.log_le_log hxpos hbranch
    rwa [Real.log_mul hKpos.ne' (Real.rpow_pos_of_pos (mul_pos hfpos hLpos) _).ne',
      Real.log_rpow (mul_pos hfpos hLpos), Real.log_mul hfpos.ne' hLpos.ne'] at h
  · have hxzero : x = 0 := by linarith
    rw [hxzero, Real.log_zero]
    exact add_nonneg (Real.log_nonneg hK)
      (mul_nonneg (by positivity) (add_nonneg (Real.log_pos hf).le (Real.log_nonneg hL)))

theorem log_branching_requirement (x f L σ K : ℝ)
    (hx : 0 ≤ x) (hf : 1 < f) (hL : 1 ≤ L) (hσ : 0 ≤ σ) (hK : 1 ≤ K)
    (hbranch : x ≤ K*(f*L)^(2*σ)) :
    Real.log x / Real.log f ≤ 2*σ + (Real.log K + 2*σ*Real.log L)/Real.log f := by
  have hlog := Real.log_pos hf
  apply (div_le_iff₀ hlog).mpr
  have h := log_branching_bound x f L σ K hx hf hL hσ hK hbranch
  have heq : (2*σ + (Real.log K + 2*σ*Real.log L)/Real.log f) * Real.log f =
      Real.log K + 2*σ*(Real.log f + Real.log L) := by
    field_simp
    ring
  rwa [heq]

theorem scale_log (i : ℕ) :
    Real.log (Peeling.scaleNat i : ℝ) = (2:ℝ)^(i+1)*Real.log 2 := by
  simp [Peeling.scaleNat, Real.log_pow]

theorem inverse_shifted_powers_sum_le_one (h : ℕ) :
    ∑ i ∈ range h, (1:ℝ)/2^(i+1) ≤ 1 := by
  have heq : (∑ i ∈ range h, (1:ℝ)/2^(i+1)) =
      (1/2:ℝ)*(∑ i ∈ range h, (1:ℝ)/2^i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  rw [heq]
  have hsum := ThresholdGreedy.inverse_powers_sum_le_two h
  linarith

theorem inverse_scale_logs_sum_le (h : ℕ) :
    ∑ i ∈ range h, (1:ℝ)/Real.log (Peeling.scaleNat i : ℝ) ≤ 1/Real.log 2 := by
  have hp : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have heq : (∑ i ∈ range h, (1:ℝ)/Real.log (Peeling.scaleNat i : ℝ)) =
      (1/Real.log 2)*(∑ i ∈ range h, (1:ℝ)/2^(i+1)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [scale_log]
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_left (inverse_shifted_powers_sum_le_one h) (by positivity)).trans_eq (by ring)

/-- At each scale, mu is the binomial-tail base mean including the factor e,
and x is the right branching factor divided by the desired decay target.
The total budget is explicit, including both ceiling and increment errors. -/
theorem sufficientThreshold_scale_budget (h : ℕ) (mean x : ℕ → ℝ) (A L σ K : ℝ)
    (hmean : ∀ i < h, 0 ≤ mean i) (hx : ∀ i < h, 0 ≤ x i)
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hσ : 0 ≤ σ) (hK : 1 ≤ K)
    (hbase : ∀ i < h, (Peeling.scaleNat i : ℝ)*mean i ≤ A)
    (hbranch : ∀ i < h, x i ≤ K*((Peeling.scaleNat i : ℝ)*L)^(2*σ)) :
    (∑ i ∈ range h, (sufficientThreshold (mean i) (Peeling.scaleNat i)
      (Real.log (x i)/Real.log (Peeling.scaleNat i)) : ℝ)) ≤
      h*(A+2*σ+2) + (Real.log K + 2*σ*Real.log L)/Real.log 2 := by
  have hq : 0 ≤ Real.log K + 2*σ*Real.log L :=
    add_nonneg (Real.log_nonneg hK) (mul_nonneg (by positivity) (Real.log_nonneg hL))
  have hlocal (i : ℕ) (hi : i < h) :
      (sufficientThreshold (mean i) (Peeling.scaleNat i)
        (Real.log (x i)/Real.log (Peeling.scaleNat i)) : ℝ) ≤
      A+2*σ+2 + (Real.log K + 2*σ*Real.log L)/Real.log (Peeling.scaleNat i : ℝ) := by
    have hf : (1:ℝ) < Peeling.scaleNat i := by
      have hh := Peeling.scaleNat_ge_two i
      exact_mod_cast (by omega : 1 < Peeling.scaleNat i)
    have hlog := log_branching_requirement (x i) _ L σ K (hx i hi) hf hL hσ hK (hbranch i hi)
    have hB : 0 ≤ 2*σ + (Real.log K + 2*σ*Real.log L)/Real.log (Peeling.scaleNat i : ℝ) := by
      exact add_nonneg (by positivity) (div_nonneg hq (Real.log_pos hf).le)
    have ht := sufficientThreshold_upper (mean i) (Peeling.scaleNat i)
      (Real.log (x i)/Real.log (Peeling.scaleNat i)) A _
      (mul_nonneg (by positivity) (hmean i hi)) hA hB (hbase i hi) hlog
    linarith
  calc
    _ ≤ ∑ i ∈ range h, (A+2*σ+2 + (Real.log K + 2*σ*Real.log L)/Real.log (Peeling.scaleNat i : ℝ)) :=
      sum_le_sum fun i hi => hlocal i (mem_range.mp hi)
    _ = h*(A+2*σ+2) + (Real.log K + 2*σ*Real.log L)*
        (∑ i ∈ range h, (1:ℝ)/Real.log (Peeling.scaleNat i : ℝ)) := by
      rw [sum_add_distrib, mul_sum]
      simp only [sum_const, card_range, nsmul_eq_mul, mul_one_div]
    _ ≤ h*(A+2*σ+2) + (Real.log K + 2*σ*Real.log L)*(1/Real.log 2) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (inverse_scale_logs_sum_le h) hq) _
    _ = _ := by ring

/-- Specialization to the real degree bounds provided by the structural
decomposition. z is the expected number of occurrences per base-edge label.
The result includes all ceiling errors and does not assume a log bound. -/
theorem decomposition_threshold_budget (h : ℕ) (DL DR : ℕ → ℕ) (B z b L σ : ℝ)
    (hB : 0 < B) (hz : 0 ≤ z) (hb : 0 < b) (hL : 1 ≤ L) (hσ : 0 ≤ σ)
    (hK : 1 ≤ 16*B*z/b)
    (hDL : ∀ i < h, (DL i : ℝ) ≤ 16*B/(Peeling.scaleNat i : ℝ))
    (hDR : ∀ i < h, (DR i : ℝ) ≤ 16*B*((Peeling.scaleNat i : ℝ)*L)^(2*σ)) :
    (∑ i ∈ range h, (sufficientThreshold (Real.exp 1*z*(DL i : ℝ)) (Peeling.scaleNat i)
      (Real.log ((DR i : ℝ)*z/b)/Real.log (Peeling.scaleNat i)) : ℝ)) ≤
      h*(16*Real.exp 1*B*z+2*σ+2) +
        (Real.log (16*B*z/b) + 2*σ*Real.log L)/Real.log 2 := by
  apply sufficientThreshold_scale_budget h (fun i => Real.exp 1*z*(DL i : ℝ))
    (fun i => (DR i : ℝ)*z/b) (16*Real.exp 1*B*z) L σ (16*B*z/b)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (by positivity) hL hσ hK
  · intro i hi
    have hpos : (0:ℝ) < Peeling.scaleNat i := by exact_mod_cast Peeling.scaleNat_pos i
    have hd := (le_div_iff₀ hpos).mp (hDL i hi)
    calc
      _ = (Real.exp 1*z)*((DL i : ℝ)*(Peeling.scaleNat i : ℝ)) := by ring
      _ ≤ (Real.exp 1*z)*(16*B) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by ring
  · intro i hi
    calc
      _ = (DR i : ℝ)*(z/b) := by ring
      _ ≤ (16*B*((Peeling.scaleNat i : ℝ)*L)^(2*σ))*(z/b) :=
        mul_le_mul_of_nonneg_right (hDR i hi) (div_nonneg hz hb.le)
      _ = _ := by ring

end GraphChoices
