import GraphChoices.ShortHorizonGreedy

namespace GraphChoices

theorem expected_total_arrivals_bound {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Nonempty E] (G : BaseGraph V E) (T N : ℕ)
    (hvertices : Fintype.card V ≤ N) : (T:ℝ) ≤ (N:ℝ)*expectedOpt G T := by
  have hh := expected_density_lower_bound G Finset.univ T
  have hm : (Fintype.card E:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [BaseGraph.internalEdges, Finset.mem_univ, and_self, Finset.filter_true,
    Finset.card_univ, mul_div_cancel_right₀ _ hm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hvertices) (expectedOpt_nonneg G T))

theorem loglogFactor_square_bound (N M : ℕ) (hN : 2 ≤ N) (hM : M ≤ N^2) :
    loglogFactor M ≤ 2*loglogFactor N := by
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hMr : (M:ℝ) ≤ (N:ℝ)^2 := by exact_mod_cast hM
  have hmax : max 2 (M:ℝ) ≤ (N:ℝ)^2 := max_le (by nlinarith) hMr
  have hlog := Real.log_le_log (by have := le_max_left (2:ℝ) (M:ℝ); linarith) hmax
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by linarith)
  have hlogM : 0 ≤ Real.log (max 2 (M:ℝ)) := Real.log_nonneg (by have := le_max_left (2:ℝ) (M:ℝ); linarith)
  have hh := Real.log_le_log (by linarith : 0 < 1+Real.log (max 2 (M:ℝ)))
    (show 1+Real.log (max 2 (M:ℝ)) ≤ 2*(1+Real.log (N:ℝ)) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hh
  have hh' : 0 ≤ Real.log (1+Real.log (N:ℝ)) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  unfold loglogFactor
  rw [max_eq_right hNr]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

end GraphChoices

namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- All arrival horizons on every left-degree-bounded bipartite graph.
The rate-adapted proof needs no auxiliary random clique augmentation. -/
theorem exists_bipartite_policy_all_horizons (G : Graph L R) [Nonempty G] (N T : ℕ)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (hD : ∀ u, leftDegree G u ≤ 4*(graphBase G).referenceCap) :
    ∃ p : OnlinePolicy G, expectedCost (graphBase G) (onlineOrientation (T := T) p) ≤
      30000*loglogFactor N*expectedOpt (graphBase G) T := by
  have hfactor := loglogFactor_ge_one N
  have ho := expectedOpt_nonneg (graphBase G) T
  have htotal := expected_total_arrivals_bound (graphBase G) T N hvertices
  by_cases hT0 : T = 0
  · refine ⟨fun _ _ => true, (expectedCost_le_horizon (graphBase G) T _).trans ?_⟩
    rw [hT0, Nat.cast_zero]
    have hh := expectedOpt_nonneg (graphBase G) 0
    have hf : 0 ≤ loglogFactor N := by linarith
    positivity
  have hT : 0 < T := Nat.pos_of_ne_zero hT0
  have hopt := expectedOpt_ge_one (graphBase G) T hT
  by_cases hlog : 2 ≤ Real.log (N:ℝ)
  · have hN : 2 ≤ N := by
      by_contra hn
      have hz : N = 0 ∨ N = 1 := by omega
      rcases hz with rfl | rfl <;> norm_num at hlog
    have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    by_cases hshort : (T:ℝ) ≤ Real.log (N:ℝ)
    · refine ⟨simpleGreedyPolicy G, (short_horizon_policy G N T hT hlog hshort).trans ?_⟩
      have hh : 0 ≤ loglogFactor N*expectedOpt (graphBase G) T := by positivity
      nlinarith
    by_cases hlong : (N:ℝ)*Real.log (N:ℝ) < T
    · refine ⟨fun _ _ => true, (allLeft_reference_bound G T N hvertices hD).trans ?_⟩
      have hlower : Real.log (N:ℝ) ≤ expectedOpt (graphBase G) T := by nlinarith
      have hm : expectedOpt (graphBase G) T ≤ loglogFactor N*expectedOpt (graphBase G) T := by nlinarith
      nlinarith
    let M := max N T
    have hTM : T ≤ M := le_max_right _ _
    have hNM : N ≤ M := le_max_left _ _
    have hverticesM : Fintype.card (L ⊕ R) ≤ M := hvertices.trans hNM
    have hlogM : 2 ≤ Real.log (M:ℝ) := hlog.trans (Real.log_le_log hNr (by exact_mod_cast hNM))
    have hlogMT : Real.log (M:ℝ) ≤ T := by
      by_cases hTN : T ≤ N
      · rw [show M = N by exact max_eq_left hTN]
        exact le_of_not_ge hshort
      · rw [show M = T by exact max_eq_right (le_of_not_ge hTN)]
        exact (Real.log_le_sub_one_of_pos (by exact_mod_cast hT)).trans (by linarith)
    have hMsquare : M ≤ N^2 := by
      have hNN : N ≤ N^2 := by nlinarith
      apply max_le hNN
      have hlogN := Real.log_le_sub_one_of_pos hNr
      have hbound : (T:ℝ) ≤ (N:ℝ)^2 := by
        have hh : (T:ℝ) ≤ (N:ℝ)*Real.log (N:ℝ) := le_of_not_gt hlong
        nlinarith
      exact_mod_cast hbound
    let d : ℝ := 2*(G.card:ℝ)/T
    have hMpos : (0:ℝ) < G.card := by
      exact_mod_cast (show 0 < G.card by simpa only [← Fintype.card_coe] using Fintype.card_pos (α := G))
    have hTr : (0:ℝ) < T := by exact_mod_cast hT
    have hd : 0 < d := by dsimp [d]; positivity
    have havg : 2*(G.card:ℝ) = (T:ℝ)*d := by dsimp [d]; field_simp
    by_cases hleft : ∀ u, (leftDegree G u:ℝ) ≤ d*Real.log (M:ℝ)
    · obtain ⟨p,hp⟩ := exists_rate_competitive_policy G M T d hT hd hlogM hlogMT hTM hleft hD hverticesM havg
      refine ⟨p, hp.trans ?_⟩
      have hh := mul_le_mul_of_nonneg_right (loglogFactor_square_bound N M hN hMsquare)
        (show 0 ≤ 15000*expectedOpt (graphBase G) T by positivity)
      nlinarith
    · push_neg at hleft
      obtain ⟨u,hu⟩ := hleft
      have hmax : d*Real.log (M:ℝ) ≤ (maxLeftDegree G:ℝ) := hu.le.trans (by exact_mod_cast leftDegree_le_max G u)
      have hdmax : (maxLeftDegree G:ℝ) ≤ 4*(graphBase G).referenceCap := by exact_mod_cast maxLeftDegree_le G _ hD
      have hz : 0 ≤ (T:ℝ)/G.card := by positivity
      have hm := mul_le_mul_of_nonneg_right hmax hz
      have hm' := mul_le_mul_of_nonneg_right hdmax hz
      have heq : d*((T:ℝ)/G.card) = 2 := by dsimp [d]; field_simp
      have href := expected_reference_cap_bound (graphBase G) T
      rw [Fintype.card_coe] at href
      have hmul : d*Real.log (M:ℝ)*((T:ℝ)/G.card) = 2*Real.log (M:ℝ) := by
        calc
          _ = (d*((T:ℝ)/G.card))*Real.log (M:ℝ) := by ring
          _ = _ := by rw [heq]
      rw [hmul] at hm
      have hlogopt : Real.log (M:ℝ) ≤ 6*expectedOpt (graphBase G) T := by nlinarith
      refine ⟨fun _ _ => true, (allLeft_reference_bound G T M hverticesM hD).trans ?_⟩
      have hh : expectedOpt (graphBase G) T ≤ loglogFactor N*expectedOpt (graphBase G) T := by nlinarith
      nlinarith
  · refine ⟨fun _ _ => true, (expectedCost_le_horizon (graphBase G) T _).trans ?_⟩
    have hN8 : (N:ℝ) ≤ 8 := by exact_mod_cast small_log_vertex_bound N (lt_of_not_ge hlog)
    have hh : expectedOpt (graphBase G) T ≤ loglogFactor N*expectedOpt (graphBase G) T := by nlinarith
    nlinarith

end GraphChoices.Peeling
