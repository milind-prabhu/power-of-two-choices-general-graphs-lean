import GraphChoices.SubgraphOccupancy
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Explicit numerical thresholds for the block proof of log-skewness.
The denominator's log-squared factor pays for the number of blocks. -/
namespace GraphChoices

theorem skew_denominator_ge_log {δ d n : ℝ} (hδ : 0 < δ) (hd : 0 < d)
    (hn : 2 ≤ Real.log n) (hdeg : δ ≤ d*Real.log n) :
    Real.log n ≤ d*(Real.log n)^2/δ := by
  apply (le_div_iff₀ hδ).mpr
  nlinarith [mul_le_mul_of_nonneg_right hdeg (by linarith : 0 ≤ Real.log n)]

theorem skew_threshold_le_log {a b δ d n : ℝ} (ha : 0 < a) (hb : 1 ≤ b)
    (han : a ≤ n) (hδ : 0 < δ) (hd : 0 < d) (hn : 2 ≤ Real.log n)
    (hdeg : δ ≤ d*Real.log n) (k : ℕ)
    (hk : 2*(k:ℝ) ≤ localLogSkewness a b δ d n) : (k:ℝ) ≤ Real.log n := by
  let q := d*(Real.log n)^2/δ
  have hq : Real.log n ≤ q := skew_denominator_ge_log hδ hd hn hdeg
  have hq2 : 2 ≤ q := hn.trans hq
  have hlogq : 1/2 ≤ Real.log q := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hq2
    linarith [Real.log_two_gt_d9]
  have hratio : a/b ≤ n := by
    apply (div_le_iff₀ (by linarith : 0 < b)).mpr
    nlinarith
  have hlogratio := Real.log_le_log (div_pos ha (by linarith : 0 < b)) hratio
  have hk' : 2*(k:ℝ)*Real.log q ≤ Real.log (a/b) :=
    (le_div_iff₀ (by linarith : 0 < Real.log q)).mp hk
  nlinarith [mul_le_mul_of_nonneg_left hlogq (Nat.cast_nonneg k)]

theorem skew_block_population {a b δ d n : ℝ}
    (ha : 0 < a) (hb : 1 ≤ b) (han : a ≤ n) (hδ : 0 < δ) (hd : 0 < d)
    (hn : 2 ≤ Real.log n) (hdeg : δ ≤ d*Real.log n)
    (k : ℕ) (hk : 0 < k) (hks : 2*(k:ℝ) ≤ localLogSkewness a b δ d n) :
    b ≤ a*((min 1 (δ/d)/(k:ℝ))/2)^k := by
  let q := d*(Real.log n)^2/δ
  let rate := min 1 (δ/d)
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hrate : 0 < rate := lt_min (by norm_num) (div_pos hδ hd)
  have hqlog : Real.log n ≤ q := skew_denominator_ge_log hδ hd hn hdeg
  have hq2 : 2 ≤ q := hn.trans hqlog
  have hqpos : 0 < q := by linarith
  have hklog : (k:ℝ) ≤ Real.log n := skew_threshold_le_log ha hb han hδ hd hn hdeg k hks
  have hscale : 2*(k:ℝ)/rate ≤ q^2 := by
    apply (div_le_iff₀ hrate).mpr
    by_cases hδd : 1 ≤ δ/d
    · have hl : rate = 1 := min_eq_left hδd
      rw [hl]
      nlinarith
    · have hl : rate = δ/d := min_eq_right (le_of_not_ge hδd)
      have heq : q*rate = (Real.log n)^2 := by dsimp [q]; rw [hl]; field_simp
      have hh : q*rate ≤ q^2*rate := by nlinarith [mul_nonneg hrate.le (by nlinarith : 0 ≤ q^2-q)]
      nlinarith
  have hpow : (2*(k:ℝ)/rate)^k ≤ a/b := by
    apply (Real.log_le_log_iff (pow_pos (div_pos (by positivity) hrate) _) (div_pos ha (by linarith))).mp
    rw [Real.log_pow]
    have hlogscale := Real.log_le_log (div_pos (by positivity : 0 < 2*(k:ℝ)) hrate) hscale
    rw [Real.log_pow] at hlogscale
    have hk' : 2*(k:ℝ)*Real.log q ≤ Real.log (a/b) :=
      (le_div_iff₀ (Real.log_pos (by linarith : 1 < q))).mp hks
    nlinarith [mul_le_mul_of_nonneg_left hlogscale hkpos.le]
  have hpowerpos : 0 < (2*(k:ℝ)/rate)^k := pow_pos (div_pos (by positivity) hrate) _
  have hprod : ((rate/(k:ℝ))/2)^k * (2*(k:ℝ)/rate)^k = 1 := by
    rw [← mul_pow]
    have heq : ((rate/(k:ℝ))/2) * (2*(k:ℝ)/rate) = 1 := by field_simp
    rw [heq, one_pow]
  change b ≤ a*((rate/(k:ℝ))/2)^k
  apply (mul_le_mul_right hpowerpos).mp
  rw [mul_assoc, hprod, mul_one]
  have hh := (le_div_iff₀ (by linarith : 0 < b)).mp hpow
  nlinarith

theorem block_length_mean (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    (δ d m : ℝ) (hδ : 0 ≤ δ) (hd : 0 < d) (hm : 0 < m)
    (haverage : 2*m = (N:ℝ)*d) :
    min 1 (δ/d)/(k:ℝ) ≤ ((N/k : ℕ):ℝ)*(δ/m) := by
  have hs : 1 ≤ N/k := Nat.div_pos hkN hk
  have hN : N < (N/k)*k+k := Nat.lt_div_mul_add hk
  have hnk : k ≤ (N/k)*k := by nlinarith
  have hfloor : (N:ℝ) ≤ 2*((N/k : ℕ):ℝ)*(k:ℝ) := by exact_mod_cast (by nlinarith : N ≤ 2*(N/k)*k)
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  apply le_trans (div_le_div_of_nonneg_right (min_le_right _ _) hkpos.le)
  apply (div_le_iff₀ hkpos).mpr
  apply (div_le_iff₀ hd).mpr
  have hh : (N:ℝ)*δ ≤ 2*((N/k : ℕ):ℝ)*(k:ℝ)*δ :=
    mul_le_mul_of_nonneg_right hfloor hδ
  apply (le_of_mul_le_mul_right (a := m) ?_ hm)
  field_simp
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hfloor)]

end GraphChoices
