import GraphChoices.SkewHorizonLower
import GraphChoices.LeftEndpointPolicy

/-! The same decomposition policy at the actual arrival rate, with vertex
bound N separate from horizon T. -/
namespace GraphChoices.Peeling
open Finset ThresholdGreedy Patterns
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  {G : Graph L R} {B N : ℕ} {d : ℝ} [Nonempty G]

theorem PreparedDecomposition.mass_at_horizon (P : PreparedDecomposition G B N d) (T : ℕ)
    (haverage : 2*(G.card : ℝ) = (T:ℝ)*d) :
    1 ≤ 16*(B:ℝ)*((T:ℝ)/Fintype.card G) := by
  have hE : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hE).mpr
  have hp := mul_le_mul_of_nonneg_left P.average_cap (Nat.cast_nonneg T : (0:ℝ) ≤ T)
  have heq : (Fintype.card G : ℝ) = G.card := by rw [Fintype.card_coe]
  rw [heq]
  nlinarith


theorem PreparedDecomposition.budget_simplified_horizon (P : PreparedDecomposition G B N d) (T : ℕ) (hT : 0 < T)
    (haverage : 2*(G.card : ℝ) = (T:ℝ)*d) :
    P.budget T ≤ 64*((B:ℝ)*((T:ℝ)/Fintype.card G)+graphLogSkewness G d (N:ℝ)+1)*
      (P.pieces.length+Real.log (Real.log (N:ℝ))+1) := by
  have hz : 0 < (T:ℝ)/Fintype.card G := div_pos
    (by exact_mod_cast hT) (by exact_mod_cast Fintype.card_pos)
  have hh := P.class_count_pos
  have hhr : (1:ℝ) ≤ P.pieces.length := by exact_mod_cast hh
  have hb := branchTarget_pos (4*B) P.pieces.length _ hh hz.le
  have hb1 := (branchTarget_le_rate (4*B) P.pieces.length _ hh hz.le).trans (shapeRate_le_one _ hh)
  have hmass := P.mass_at_horizon T haverage
  have hK : 1 ≤ 16*(B:ℝ)*((T:ℝ)/Fintype.card G)/branchTarget (4*B) P.pieces.length ((T:ℝ)/Fintype.card G) := by
    apply (le_div_iff₀ hb).mpr
    simpa only [one_mul] using hb1.trans hmass
  have hl : 0 ≤ Real.log (Real.log (N:ℝ)) := Real.log_nonneg P.large_log.le
  have hbound := log_reference_branch_bound B P.pieces.length ((T:ℝ)/Fintype.card G) P.reference_cap_pos hh hz
  have hs := scalar_budget_le (P.pieces.length : ℝ) ((B:ℝ)*((T:ℝ)/Fintype.card G))
    (graphLogSkewness G d (N:ℝ)) (Real.log (Real.log (N:ℝ))) _ hhr (by positivity)
    (graphLogSkewness_nonneg G d (N:ℝ)) hl (Real.log_nonneg hK) hbound
  convert hs using 1 <;> unfold PreparedDecomposition.budget <;> ring


theorem PreparedDecomposition.budget_loglog_horizon (P : PreparedDecomposition G B N d) (T : ℕ) (hT : 0 < T)
    (hB : B ≤ N^2) (haverage : 2*(G.card : ℝ) = (T:ℝ)*d) :
    P.budget T ≤ 320*((B:ℝ)*((T:ℝ)/Fintype.card G)+graphLogSkewness G d (N:ℝ)+1)*(iteratedLog N : ℝ) := by
  have hn : P.pieces.length ≤ iteratedLog N+2 := by
    rw [P.count]
    exact numberRounds_le_iteratedLog B N P.vertex_count_pos hB
  have hnr : (P.pieces.length : ℝ) ≤ (iteratedLog N : ℝ)+2 := by exact_mod_cast hn
  have hQ : (1:ℝ) ≤ iteratedLog N := by exact_mod_cast iteratedLog_pos N
  have hl := real_loglog_le_iteratedLog N P.large_log
  have hs := graphLogSkewness_nonneg G d (N:ℝ)
  have hfactor : (P.pieces.length : ℝ)+Real.log (Real.log (N:ℝ))+1 ≤ 5*(iteratedLog N : ℝ) := by linarith
  calc
    _ ≤ _ := P.budget_simplified_horizon T hT haverage
    _ ≤ 64*((B:ℝ)*((T:ℝ)/Fintype.card G)+graphLogSkewness G d (N:ℝ)+1)*(5*(iteratedLog N : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring


theorem PreparedDecomposition.component_tail_horizon (P : PreparedDecomposition G B N d)
    (T c : ℕ) (hT : 0 < T) (hc : 5 ≤ c)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card:ℝ) = (T:ℝ)*d) :
    eventProbability (largeComponentEvent P.encode (P.thresholds T) T
      (3*(polynomialCutoff N c+1)^2)) ≤ 3/(N:ℝ)^c := by
  have hv : Fintype.card L+Fintype.card R ≤ N := by simpa only [Fintype.card_sum] using hvertices
  apply log_squared_component_tail P.pieces.get P.encode P.DL P.DR (4*B)
    (maxLeftDegree G) T N c (fun i => scaleNat i.val) P.simple P.source P.bucket_bound
    P.piece_left_cap P.piece_right_cap P.global_bucket_bound hT P.scale_gt_one
    P.vertex_count_pos (by omega) (by omega)
  have hm : (T:ℝ)*(maxLeftDegree G:ℝ)/G.card ≤ 2*Real.log (N:ℝ) := by
    have he : (0:ℝ) < G.card := by exact_mod_cast (show 0 < G.card by simpa only [← Fintype.card_coe] using Fintype.card_pos (α := G))
    apply (div_le_iff₀ he).mpr
    have hh := mul_le_mul_of_nonneg_left P.max_degree_preprocessing (Nat.cast_nonneg T : (0:ℝ) ≤ T)
    rw [← mul_assoc, ← haverage] at hh
    nlinarith
  have hh := preprocessed_mean_below_cutoff N c ((T:ℝ)*(maxLeftDegree G:ℝ)/G.card)
    P.vertex_count_pos hc (by positivity) hm
  rw [Fintype.card_coe]
  convert hh using 1 <;> ring

theorem PreparedDecomposition.expected_cost_horizon (P : PreparedDecomposition G B N d)
    (T : ℕ) (hT : 0 < T) (hTN : T ≤ N)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card:ℝ) = (T:ℝ)*d) (hB : B ≤ N^2) :
    expectedCost (graphBase G) (onlineOrientation (T := T) (P.policy T)) ≤
      320*((B:ℝ)*((T:ℝ)/G.card)+graphLogSkewness G d (N:ℝ)+1)*(iteratedLog N:ℝ)+
        20*(iteratedLog N:ℝ)*expectedOpt (graphBase G) T+3 := by
  have ht := P.component_tail_horizon T 5 hT (by decide) hvertices haverage
  have hh := expected_load_of_component_tail P.encode (P.thresholds T) T _ _ ht
  rw [expectedTotalMaxLoad_eq_expectedCost, expectedReplayOpt_eq_expectedOpt] at hh
  change expectedCost (graphBase G) (onlineOrientation (T := T) (P.policy T)) ≤
    (∑ i, (P.thresholds T i:ℝ))+
      (2*(Nat.log 2 (3*(polynomialCutoff N 5+1)^2)+1):ℕ)*expectedOpt (graphBase G) T+
        T*(3/(N:ℝ)^5) at hh
  have hb := (P.threshold_budget T (P.mass_at_horizon T haverage)).trans
    (P.budget_loglog_horizon T hT hB haverage)
  rw [Fintype.card_coe] at hb
  have hg : (((2*(Nat.log 2 (3*(polynomialCutoff N 5+1)^2)+1):ℕ):ℝ)) ≤ 20*(iteratedLog N:ℝ) := by
    exact_mod_cast greedy_multiplier_le_iteratedLog N
  have hgm := mul_le_mul_of_nonneg_right hg (expectedOpt_nonneg (graphBase G) T)
  have he : (T:ℝ)*(3/(N:ℝ)^5) ≤ 3 := by
    apply le_trans _ (exceptional_error_le_three N P.vertex_count_pos)
    have htr : (T:ℝ) ≤ N := by exact_mod_cast hTN
    have hmul := mul_le_mul_of_nonneg_right htr (show 0 ≤ 3/(N:ℝ)^5 by positivity)
    convert hmul using 1 <;> ring
  linarith

end GraphChoices.Peeling
