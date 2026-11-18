import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The logarithmic-to-multiplicative rearrangement in the proof of Lemma 3.7.
All positivity hypotheses are explicit; logarithms with zero/negative
arguments or nonpositive denominators cannot silently enter the argument. -/
namespace GraphChoices

noncomputable def localLogSkewness (a b d D n : ℝ) : ℝ :=
  Real.log (a/b) / Real.log (D * (Real.log n)^2 / d)

 theorem log_ratio_bound_iff {a b q σ : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 1 < q) :
    Real.log (a/b) / Real.log q ≤ σ ↔ a ≤ b * q^σ := by
  rw [div_le_iff₀ (Real.log_pos hq)]
  rw [mul_comm σ, Real.log_le_iff_le_exp (div_pos ha hb)]
  rw [← Real.rpow_def_of_pos (lt_trans zero_lt_one hq)]
  rw [div_le_iff₀ hb, mul_comm]

/-- A local skewness bound implies the neighborhood expansion inequality.
The parameter q is the denominator's argument in Definition 3.2. -/
 theorem expansion_of_log_skew {a b q Q σ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hq : 1 < q) (hQ : q ≤ Q) (hσ : 0 ≤ σ)
    (hskew : Real.log (a/b) / Real.log q ≤ σ) :
    a ≤ b * Q^σ := by
  exact ((log_ratio_bound_iff ha hb hq).mp hskew).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hQ hσ) (le_of_lt hb))

/-- The exact scale substitution used for b_i in Lemma 3.7. -/
 theorem expansion_at_scale {a b d D n f σ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hf : 0 < f) (hn : 0 < Real.log n) (hσ : 0 ≤ σ)
    (hdegree : D / f^2 ≤ d)
    (hdenom : 1 < D * (Real.log n)^2 / d)
    (hskew : localLogSkewness a b d D n ≤ σ) :
    a ≤ b * (f * Real.log n)^(2*σ) := by
  have hf2 : 0 < f^2 := sq_pos_of_pos hf
  have hDle : D ≤ d * f^2 := (div_le_iff₀ hf2).mp hdegree
  have hq : D * (Real.log n)^2 / d ≤ (f * Real.log n)^2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right hDle (sq_nonneg (Real.log n))]
  have hh := expansion_of_log_skew ha hb hdenom hq hσ hskew
  have hp : 0 ≤ f * Real.log n := le_of_lt (mul_pos hf hn)
  have heq : ((f * Real.log n)^2 : ℝ)^σ = (f * Real.log n)^(2*σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp]
    norm_num
  simpa [heq] using hh

end GraphChoices
