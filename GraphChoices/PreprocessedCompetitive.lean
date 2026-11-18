import GraphChoices.SkewLowerBound
import GraphChoices.RealLoglogComparison

/-! The end-to-end competitive guarantee for the preprocessed graph at
the vertex horizon. Skewness is now proved bounded by the benchmark, and
small sizes use the deterministic horizon bound. -/
namespace GraphChoices

theorem loglogFactor_ge_one (N : ℕ) : 1 ≤ loglogFactor N := by
  unfold loglogFactor
  have hh : 0 ≤ Real.log (max 2 (N:ℝ)) := Real.log_nonneg (by have := le_max_left (2:ℝ) (N:ℝ); linarith)
  have hh' : 0 ≤ Real.log (1+Real.log (max 2 (N:ℝ))) := Real.log_nonneg (by linarith)
  linarith

theorem small_log_vertex_bound (N : ℕ) (hlog : Real.log (N:ℝ) < 2) : N ≤ 8 := by
  by_cases hN : N = 0
  · omega
  have hNr : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hh := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hNr] at hh
  have he : Real.exp 2 = (Real.exp 1)^2 := by simpa using Real.exp_nat_mul 1 2
  have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hepos := Real.exp_pos 1
  have he9 : (Real.exp 1)^2 < 9 := by nlinarith
  have hn9 : (N:ℝ) < 9 := by rw [he] at hh; linarith
  have hn : N < 9 := by exact_mod_cast hn9
  omega

theorem expectedCost_le_horizon {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [Nonempty E] (G : BaseGraph V E) (T : ℕ)
    (a : (Fin T → E) → Orientation T) : expectedCost G a ≤ T := by
  rw [← average_const (Ω := Fin T → E) (T:ℝ)]
  apply average_mono
  intro ω
  exact_mod_cast maxLoad_le_length (G.sample ω) (a ω)

end GraphChoices

namespace GraphChoices.Peeling
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  {G : Graph L R} {B N : ℕ} {d : ℝ} [Nonempty G]

/-- The constructed Threshold-Greedy policy is O(log log N)-competitive
under the graph preprocessing conditions, with no unproved skewness premise. -/
theorem PreparedDecomposition.expected_cost_competitive (P : PreparedDecomposition G B N d)
    (hB : B = (graphBase G).referenceCap) (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card:ℝ) = (N:ℝ)*d) :
    expectedCost (graphBase G) (onlineOrientation (T := N) (P.policy N)) ≤
      37800*loglogFactor N*expectedOpt (graphBase G) N := by
  have hfactor := loglogFactor_ge_one N
  by_cases hlog : 2 ≤ Real.log (N:ℝ)
  · have hs := graphLogSkewness_le_eight_expectedOpt G N d P.positive_average hlog
      P.preprocessing hvertices haverage
    have hh := P.real_competitive_of_skew_lower_bound hB hvertices haverage 8 hs
    norm_num at hh
    exact hh
  · have hN8 := small_log_vertex_bound N (lt_of_not_ge hlog)
    have hopt := expectedOpt_ge_one (graphBase G) N P.vertex_count_pos
    apply (expectedCost_le_horizon (graphBase G) N _).trans
    have hNr : (N:ℝ) ≤ 8 := by exact_mod_cast hN8
    have hh : 1 ≤ loglogFactor N*expectedOpt (graphBase G) N := by nlinarith
    nlinarith

/-- A graph-level competitive theorem at T=N. The remaining assumptions
are solely concrete preprocessing, vertex-count and average-degree facts. -/
theorem exists_preprocessed_competitive_policy (G : Graph L R) [Nonempty G]
    (N : ℕ) (d : ℝ) (hd : 0 < d)
    (hleft : ∀ u, (leftDegree G u:ℝ) ≤ d*Real.log (N:ℝ))
    (hD : ∀ u, leftDegree G u ≤ 4*(graphBase G).referenceCap)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card:ℝ) = (N:ℝ)*d) :
    ∃ p : OnlinePolicy G, expectedCost (graphBase G) (onlineOrientation (T := N) p) ≤
      37800*loglogFactor N*expectedOpt (graphBase G) N := by
  have hN : 0 < N := by
    have hm : (0:ℝ) < G.card := by
      have hh : 0 < G.card := by simpa only [← Fintype.card_coe] using Fintype.card_pos (α := G)
      exact_mod_cast hh
    by_contra h
    have hz : N = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_mul] at haverage
    linarith
  by_cases hlog : 2 ≤ Real.log (N:ℝ)
  · have hlog1 : 1 < Real.log (N:ℝ) := by linarith
    have hcap := average_le_two_referenceCap G N d hN hvertices haverage
    have hB : d ≤ 16*(graphBase G).referenceCap := by
      have hh : (0:ℝ) ≤ (graphBase G).referenceCap := Nat.cast_nonneg _
      linarith
    obtain ⟨P⟩ := exists_preparedDecomposition G (graphBase G).referenceCap N d hd hlog1 hleft hB hD
    exact ⟨P.policy N, P.expected_cost_competitive rfl hvertices haverage⟩
  · refine ⟨fun _ _ => false, (expectedCost_le_horizon (graphBase G) N _).trans ?_⟩
    have hN8 : (N:ℝ) ≤ 8 := by exact_mod_cast small_log_vertex_bound N (lt_of_not_ge hlog)
    have hopt := expectedOpt_ge_one (graphBase G) N hN
    have hfactor := loglogFactor_ge_one N
    have hh : 1 ≤ loglogFactor N*expectedOpt (graphBase G) N := by nlinarith
    nlinarith

end GraphChoices.Peeling
