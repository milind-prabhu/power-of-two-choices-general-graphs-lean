import GraphChoices.DecomposedAlgorithm
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The exact automatic threshold budget has the expected bilinear growth in
reference density, log-skewness and the log-log scale. Explicit constants are
kept throughout; no asymptotic or benchmark comparison is assumed. -/
namespace GraphChoices.Patterns

theorem log_reference_branch_bound (B h : ℕ) (z : ℝ)
    (hB : 0 < B) (hh : 0 < h) (hz : 0 < z) :
    Real.log (16*(B:ℝ)*z/branchTarget (4*B) h z) ≤ 10+5*((B:ℝ)*z)+2*h := by
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hhr : (0:ℝ) < h := by exact_mod_cast hh
  have hne : (h:ℝ) ≠ 0 := hhr.ne'
  have hden : (4*(B:ℝ)*z+1) ≠ 0 := ne_of_gt (by positivity)
  have heq : 16*(B:ℝ)*z/branchTarget (4*B) h z =
      1024*((B:ℝ)*z)*(4*((B:ℝ)*z)+1)*(h:ℝ)^2 := by
    unfold branchTarget shapeRate
    push_cast
    field_simp
    ring
  rw [heq]
  have hM : 0 < (B:ℝ)*z := mul_pos hBr hz
  have hlog : Real.log (1024*((B:ℝ)*z)*(4*((B:ℝ)*z)+1)*(h:ℝ)^2) =
      Real.log 1024 + Real.log ((B:ℝ)*z) + Real.log (4*((B:ℝ)*z)+1) + 2*Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hM.ne']
    norm_num
  rw [hlog]
  have hconst : Real.log 1024 ≤ 10 := by
    have he : (1024:ℝ) = 2^10 := by norm_num
    rw [he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have hm := Real.log_le_sub_one_of_pos hM
  have hm' := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 4*((B:ℝ)*z)+1)
  have hhh := Real.log_le_sub_one_of_pos hhr
  linarith

theorem scalar_budget_le (h M σ l K : ℝ) (hh : 1 ≤ h) (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hl : 0 ≤ l) (hK : 0 ≤ K) (hKbound : K ≤ 10+5*M+2*h) :
    h*(16*Real.exp 1*M+2*σ+2)+(K+2*σ*l)/Real.log 2 ≤
      64*(M+σ+1)*(h+l+1) := by
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hlog : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnum : 0 ≤ K+2*σ*l := by positivity
  have hdiv : (K+2*σ*l)/Real.log 2 ≤ 2*(K+2*σ*l) := by
    calc
      _ ≤ (K+2*σ*l)/((1:ℝ)/2) := div_le_div_of_nonneg_left hnum (by norm_num) hlog
      _ = _ := by ring
  have heM := mul_le_mul_of_nonneg_right he hM
  have hhead : h*(16*Real.exp 1*M+2*σ+2) ≤ h*(48*M+2*σ+2) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have hMh := mul_nonneg hM (show 0 ≤ h by linarith)
  have hσh := mul_nonneg hσ (show 0 ≤ h by linarith)
  have hMl := mul_nonneg hM hl
  have hσl := mul_nonneg hσ hl
  nlinarith

end GraphChoices.Patterns

namespace GraphChoices.Peeling
open Patterns
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  {G : Graph L R} {B N : ℕ} {d : ℝ} [Nonempty G]

theorem PreparedDecomposition.budget_simplified (P : PreparedDecomposition G B N d)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    P.budget N ≤ 64*((B:ℝ)*((N:ℝ)/Fintype.card G)+graphLogSkewness G d (N:ℝ)+1)*
      (P.pieces.length+Real.log (Real.log (N:ℝ))+1) := by
  have hz : 0 < (N:ℝ)/Fintype.card G := div_pos
    (by exact_mod_cast P.vertex_count_pos) (by exact_mod_cast Fintype.card_pos)
  have hh := P.class_count_pos
  have hhr : (1:ℝ) ≤ P.pieces.length := by exact_mod_cast hh
  have hb := branchTarget_pos (4*B) P.pieces.length _ hh hz.le
  have hb1 := (branchTarget_le_rate (4*B) P.pieces.length _ hh hz.le).trans (shapeRate_le_one _ hh)
  have hmass := P.mass_at_vertex_horizon haverage
  have hK : 1 ≤ 16*(B:ℝ)*((N:ℝ)/Fintype.card G)/branchTarget (4*B) P.pieces.length ((N:ℝ)/Fintype.card G) := by
    apply (le_div_iff₀ hb).mpr
    simpa only [one_mul] using hb1.trans hmass
  have hl : 0 ≤ Real.log (Real.log (N:ℝ)) := Real.log_nonneg P.large_log.le
  have hbound := log_reference_branch_bound B P.pieces.length ((N:ℝ)/Fintype.card G) P.reference_cap_pos hh hz
  have hs := scalar_budget_le (P.pieces.length : ℝ) ((B:ℝ)*((N:ℝ)/Fintype.card G))
    (graphLogSkewness G d (N:ℝ)) (Real.log (Real.log (N:ℝ))) _ hhr (by positivity)
    (graphLogSkewness_nonneg G d (N:ℝ)) hl (Real.log_nonneg hK) hbound
  convert hs using 1 <;> unfold PreparedDecomposition.budget <;> ring

end GraphChoices.Peeling
