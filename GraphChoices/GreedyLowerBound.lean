import GraphChoices.LowerOfflineOptimum
import GraphChoices.LowerGraphDegrees
import GraphChoices.GreedyCoinMarginals

/-! Theorem 1.2, with explicit integer parameters, actual vertex horizon,
independent fair random tie-breaking, a high-probability load lower bound,
an expected offline upper bound and the stated mild degree irregularity. -/
namespace GraphChoices.LowerBound
open Finset

theorem family_greedy_lower (b : ℕ) (hb : 16 ≤ b) :
    letI := family_edges_nonempty b hb
    (b:ℝ)/2 ≤ RandomGreedy.expectedLoad (graph b (branching b) (width b)) (size b) := by
  letI := family_edges_nonempty b hb
  have hp := family_parameter_bounds b hb
  have hh := expectedGreedy_lower b (branching b) (width b) (batchLength b) (by have := hp.2.1; omega)
  rw [← size_eq_batches b (by omega)] at hh
  have he := family_propagation_error b hb
  have hNr : (16:ℝ) ≤ size b := by exact_mod_cast (show 16 ≤ size b by have := hp.2.2.2.2.1; omega)
  have hhalf : 1/(size b:ℝ)^2 ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  nlinarith [mul_nonneg (Nat.cast_nonneg b : (0:ℝ) ≤ b) (sub_nonneg.mpr (he.trans hhalf))]

theorem family_optimum_bound (b : ℕ) (hb : 16 ≤ b) :
    letI := family_edges_nonempty b hb
    expectedOpt (graph b (branching b) (width b)) (size b) ≤ 500*Real.log ((b:ℝ)+1) := by
  letI := family_edges_nonempty b hb
  have hp := family_parameter_bounds b hb
  have hh := family_offline_bound b hb
  have hk := densityThreshold_upper (branching b) (by have := hp.1; omega)
  obtain ⟨hl,_,ht⟩ := family_elementary_logs b hb
  linarith

theorem family_optimum_loglog (b : ℕ) (hb : 16 ≤ b) :
    letI := family_edges_nonempty b hb
    expectedOpt (graph b (branching b) (width b)) (size b) ≤ 500*Real.log (Real.log (size b:ℝ)) := by
  letI := family_edges_nonempty b hb
  have hlog := Real.log_le_log (show (0:ℝ)<(b:ℝ)+1 by positivity) (family_log_bounds b hb).1
  exact (family_optimum_bound b hb).trans (by linarith)

theorem eventProbability_pullback {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    [DecidableEq Ω] [DecidableEq Ω'] (e : Ω ≃ Ω') (A : Finset Ω') :
    eventProbability (univ.filter fun ω => e ω ∈ A) = eventProbability A := by
  rw [← average_unit_indicator,← average_unit_indicator A]
  have hh := average_equiv e (fun ω => if ω ∈ A then (1:ℝ) else 0)
  simpa only [mem_filter,mem_univ,true_and] using hh

theorem family_greedy_high_probability (b : ℕ) (hb : 16 ≤ b) :
    letI := family_edges_nonempty b hb
    eventProbability (univ.filter fun ω : Fin (size b) → Edges b (branching b) (width b) × Bool =>
      maxLoad ((RandomGreedy.coinGraph (graph b (branching b) (width b))).sample ω)
        (onlineOrientation (RandomGreedy.policy (graph b (branching b) (width b))) ω) < b) ≤
      1/(size b:ℝ)^2 := by
  classical
  letI := family_edges_nonempty b hb
  have hp := family_parameter_bounds b hb
  rw [size_eq_batches b (by omega)]
  rw [← eventProbability_pullback (blockFlatten b (batchLength b))]
  simp only [mem_filter,mem_univ,true_and]
  have hsub : (univ.filter fun ω : Fin b → Fin (batchLength b) → Edges b (branching b) (width b) × Bool =>
      maxLoad ((RandomGreedy.coinGraph (graph b (branching b) (width b))).sample (blockFlatten b (batchLength b) ω))
        (onlineOrientation (RandomGreedy.policy (graph b (branching b) (width b))) (blockFlatten b (batchLength b) ω)) < b) ⊆
        badBatches b (branching b) (width b) (batchLength b) := by
    intro ω hω
    have hh := (mem_filter.mp hω).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,fun hg => ?_⟩
    have hl := goodBatches_maxLoad b (branching b) (width b) (batchLength b)
      (by have := hp.2.1; omega) ω hg
    omega
  apply (eventProbability_mono hsub).trans
  apply (badBatches_probability b (branching b) (width b) (batchLength b)).trans
  rw [← size_eq_batches b (by omega)]
  exact family_propagation_error b hb

theorem family_competitive_gap (b : ℕ) (hb : 16 ≤ b) :
    letI := family_edges_nonempty b hb
    (1/30000:ℝ)*Real.log (size b:ℝ)/(Real.log (Real.log (size b:ℝ)))^2*
      expectedOpt (graph b (branching b) (width b)) (size b) ≤
        RandomGreedy.expectedLoad (graph b (branching b) (width b)) (size b) := by
  letI := family_edges_nonempty b hb
  let A := Real.log (size b:ℝ)
  let D := Real.log A
  let l := Real.log ((b:ℝ)+1)
  let O := expectedOpt (graph b (branching b) (width b)) (size b)
  have hl : 1 ≤ l := (family_elementary_logs b hb).1
  have hD : l ≤ D := Real.log_le_log (by positivity) (family_log_bounds b hb).1
  have hA : A ≤ 26*(b:ℝ)*l := (family_log_bounds b hb).2
  have hO : O ≤ 500*l := family_optimum_bound b hb
  have hO0 : 0 ≤ O := expectedOpt_nonneg _ _
  have hprod : A*O ≤ 13000*(b:ℝ)*l^2 := by
    have h1 := mul_le_mul_of_nonneg_right hA hO0
    have h2 := mul_le_mul_of_nonneg_left hO (show 0 ≤ 26*(b:ℝ)*l by positivity)
    nlinarith
  have hsq : l^2 ≤ D^2 := by nlinarith
  have hprod' : A*O ≤ 13000*(b:ℝ)*D^2 := hprod.trans
    (mul_le_mul_of_nonneg_left hsq (by positivity))
  apply le_trans _ (family_greedy_lower b hb)
  change (1/30000:ℝ)*A/D^2*O ≤ (b:ℝ)/2
  have hDpos : 0 < D := by linarith
  apply (le_of_mul_le_mul_right (a := D^2) ?_ (sq_pos_of_pos hDpos))
  have heq : ((1/30000:ℝ)*A/D^2*O)*D^2 = A*O/30000 := by field_simp
  rw [heq]
  nlinarith [mul_nonneg (Nat.cast_nonneg b : (0:ℝ) ≤ b) (sq_nonneg D)]

theorem family_log_load_threshold (b : ℕ) (hb : 16 ≤ b) :
    Real.log (size b:ℝ)/(26*Real.log (Real.log (size b:ℝ))) ≤ (b:ℝ) := by
  have hl := (family_elementary_logs b hb).1
  have hD := Real.log_le_log (show (0:ℝ)<(b:ℝ)+1 by positivity) (family_log_bounds b hb).1
  have hA := (family_log_bounds b hb).2
  apply (div_le_iff₀ (by linarith : 0 < 26*Real.log (Real.log (size b:ℝ)))).mpr
  have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ 26*(b:ℝ) by positivity)
  nlinarith

/-- Lemma 5.1 in the literal log N / log log N scale, with failure N⁻². -/
theorem family_greedy_logarithmic_high_probability (b : ℕ) (hb : 16 ≤ b) :
    letI := family_edges_nonempty b hb
    eventProbability (univ.filter fun ω : Fin (size b) → Edges b (branching b) (width b) × Bool =>
      (maxLoad ((RandomGreedy.coinGraph (graph b (branching b) (width b))).sample ω)
        (onlineOrientation (RandomGreedy.policy (graph b (branching b) (width b))) ω):ℝ) <
          Real.log (size b:ℝ)/(26*Real.log (Real.log (size b:ℝ)))) ≤ 1/(size b:ℝ)^2 := by
  letI := family_edges_nonempty b hb
  apply le_trans _ (family_greedy_high_probability b hb)
  apply eventProbability_mono
  intro ω hω
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have hh := ((mem_filter.mp hω).2).trans_le (family_log_load_threshold b hb)
  exact_mod_cast hh

/-- An explicit infinite family witnesses the Greedy competitive lower
bound, including the precise degree interval asserted in Theorem 1.2. -/
theorem greedyLowerBound :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ b : ℕ, ∃ hb : 16 ≤ b,
      M ≤ size b ∧ (graph b (branching b) (width b)).IsSimple ∧
      (∀ v, Real.sqrt (size b:ℝ) ≤ (baseDegree (graph b (branching b) (width b)) v:ℝ) ∧
        (baseDegree (graph b (branching b) (width b)) v:ℝ) ≤
          Real.sqrt (size b:ℝ)*(Real.log (size b:ℝ))^3) ∧
      (letI := family_edges_nonempty b hb
       c*Real.log (size b:ℝ)/(Real.log (Real.log (size b:ℝ)))^2*
         expectedOpt (graph b (branching b) (width b)) (size b) ≤
           RandomGreedy.expectedLoad (graph b (branching b) (width b)) (size b)) := by
  refine ⟨1/30000,by norm_num,fun M => ?_⟩
  let b := max 16 M
  have hb : 16 ≤ b := le_max_left _ _
  refine ⟨b,hb,(le_max_right _ _).trans (family_parameter_bounds b hb).2.2.2.2.1,
    graph_isSimple _ _ _,family_degree_range b hb,?_⟩
  exact family_competitive_gap b hb

end GraphChoices.LowerBound
