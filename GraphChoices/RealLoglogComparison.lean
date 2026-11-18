import GraphChoices.PreprocessedComparison

/-! Comparison with the bounded-at-small-n real log-log factor used by the
main target. This completes the asymptotic conversion for the preprocessed
N-arrival policy while retaining the skewness term explicitly for later benchmark comparison.
-/
namespace GraphChoices

theorem nat_log_le_twice_real_log (a : ℕ) (ha : 0 < a) :
    (Nat.log 2 a : ℝ) ≤ 2*Real.log (a:ℝ) := by
  have hp : (2:ℝ)^(Nat.log 2 a) ≤ (a:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 ha.ne'
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^(Nat.log 2 a)) hp
  rw [Real.log_pow] at hlog
  have htwo : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hn : (0:ℝ) ≤ Nat.log 2 a := Nat.cast_nonneg _
  nlinarith

theorem iteratedLog_le_real_factor (N : ℕ) (hlog : 1 < Real.log (N:ℝ)) :
    (iteratedLog N : ℝ) ≤ 3*loglogFactor N := by
  have hN : 2 ≤ N := by
    by_contra hn
    have hc : N = 0 ∨ N = 1 := by omega
    rcases hc with rfl | rfl <;> norm_num at hlog
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  let a := Nat.log 2 N+1
  have ha : 0 < a := by dsimp [a]; omega
  have hinner := nat_log_le_twice_real_log N (by omega)
  have houter := nat_log_le_twice_real_log a ha
  have hap : (0:ℝ) < a := by exact_mod_cast ha
  have haBound : (a:ℝ) ≤ 2*(1+Real.log (N:ℝ)) := by
    dsimp [a]
    push_cast
    linarith
  have hla := Real.log_le_log hap haBound
  rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith : 0 < 1+Real.log (N:ℝ)))] at hla
  have hln : 0 ≤ Real.log (1+Real.log (N:ℝ)) := Real.log_nonneg (by linarith)
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  unfold loglogFactor
  rw [max_eq_right hNr]
  have heq : (iteratedLog N : ℝ) = (Nat.log 2 a : ℝ)+1 := by
    simp only [iteratedLog, Nat.cast_add, Nat.cast_one, a]
  rw [heq]
  linarith

end GraphChoices

namespace GraphChoices.Peeling
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  {G : Graph L R} {B N : ℕ} {d : ℝ} [Nonempty G]

/-- The real log-log bound for the constructed preprocessed online policy.
The actual graph skewness remains additive; no skewness lower bound is assumed. -/
theorem PreparedDecomposition.expected_cost_real_loglog (P : PreparedDecomposition G B N d)
    (hB : B = (graphBase G).referenceCap) (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    expectedCost (graphBase G) (onlineOrientation (T := N) (P.policy N)) ≤
      4200*loglogFactor N*(expectedOpt (graphBase G) N+graphLogSkewness G d (N:ℝ)) := by
  apply (P.expected_cost_density_skew hB hvertices haverage).trans
  have hs : 0 ≤ expectedOpt (graphBase G) N+graphLogSkewness G d (N:ℝ) :=
    add_nonneg (expectedOpt_nonneg _ _) (graphLogSkewness_nonneg G d (N:ℝ))
  calc
    _ ≤ (1400*(3*loglogFactor N))*(expectedOpt (graphBase G) N+graphLogSkewness G d (N:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (iteratedLog_le_real_factor N P.large_log) (by norm_num)) hs
    _ = _ := by ring

/-- Conditional competitive guarantee: the only additional benchmark premise
is an explicitly stated parameterized log-skewness bound. The following
PreprocessedCompetitive module supplies a proved constant bound. -/
theorem PreparedDecomposition.real_competitive_of_skew_lower_bound (P : PreparedDecomposition G B N d)
    (hB : B = (graphBase G).referenceCap) (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) (K : ℝ)
    (hskew : graphLogSkewness G d (N:ℝ) ≤ K*expectedOpt (graphBase G) N) :
    expectedCost (graphBase G) (onlineOrientation (T := N) (P.policy N)) ≤
      4200*(1+K)*loglogFactor N*expectedOpt (graphBase G) N := by
  have hfactor : 0 ≤ loglogFactor N := by
    have hq : (0:ℝ) ≤ iteratedLog N := Nat.cast_nonneg _
    have hh := iteratedLog_le_real_factor N P.large_log
    linarith
  apply (P.expected_cost_real_loglog hB hvertices haverage).trans
  calc
    _ ≤ 4200*loglogFactor N*(expectedOpt (graphBase G) N+K*expectedOpt (graphBase G) N) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hskew _) (by positivity)
    _ = _ := by ring

/-- Graph-level existence theorem in the real log-log scale of the main target.
The reference capacity is the rounded maximum source density, and its
average-degree comparison is proved internally. The skewness term remains. -/
theorem exists_preprocessed_real_loglog_policy (G : Graph L R) [Nonempty G] (N : ℕ) (d : ℝ)
    (hd : 0 < d) (hlog : 1 < Real.log (N:ℝ))
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d*Real.log (N:ℝ))
    (hD : ∀ u, leftDegree G u ≤ 4*(graphBase G).referenceCap)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (haverage : 2*(G.card : ℝ) = (N:ℝ)*d) :
    ∃ p : OnlinePolicy G, expectedCost (graphBase G) (onlineOrientation (T := N) p) ≤
      4200*loglogFactor N*(expectedOpt (graphBase G) N+graphLogSkewness G d (N:ℝ)) := by
  obtain ⟨p, hp⟩ := exists_preprocessed_density_skew_policy G N d hd hlog hleft hD hvertices haverage
  refine ⟨p, hp.trans ?_⟩
  have hs : 0 ≤ expectedOpt (graphBase G) N+graphLogSkewness G d (N:ℝ) :=
    add_nonneg (expectedOpt_nonneg _ _) (graphLogSkewness_nonneg G d (N:ℝ))
  calc
    _ ≤ (1400*(3*loglogFactor N))*(expectedOpt (graphBase G) N+graphLogSkewness G d (N:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (iteratedLog_le_real_factor N hlog) (by norm_num)) hs
    _ = _ := by ring

end GraphChoices.Peeling
