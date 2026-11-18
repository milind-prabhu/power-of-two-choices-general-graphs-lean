import GraphChoices.ConcreteShattering
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The sampled-degree mean at the paper's preprocessing scale. This gives
log-squared shattering directly from M ≤ d log N and 2|E| = N d for T ≤ N.
-/
namespace GraphChoices.Patterns

theorem real_log_le_nat_log_shift (N : ℕ) (hN : 0 < N) :
    Real.log (N:ℝ) ≤ (Nat.log 2 N+1 : ℕ) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hp : (N:ℝ) ≤ (2:ℝ)^(Nat.log 2 N+1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le
  have hlog := Real.log_le_log hNr hp
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (Nat.log 2 N+1) : (0:ℝ) ≤ (Nat.log 2 N+1 : ℕ))
  exact hlog.trans (by simpa using hmul)

theorem preprocessing_mean_bound (M T N E : ℕ) (d : ℝ)
    (hE : 0 < E) (hT : T ≤ N)
    (hdegree : (M:ℝ) ≤ d*Real.log (N:ℝ))
    (haverage : 2*(E:ℝ) = (N:ℝ)*d) :
    (T:ℝ)*M/E ≤ 2*Real.log (N:ℝ) := by
  have hEr : (0:ℝ) < E := by exact_mod_cast hE
  apply (div_le_iff₀ hEr).mpr
  calc
    (T:ℝ)*M ≤ (N:ℝ)*M := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) (Nat.cast_nonneg M)
    _ ≤ (N:ℝ)*(d*Real.log (N:ℝ)) := mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg N)
    _ = (2*(E:ℝ))*Real.log (N:ℝ) := by rw [haverage]; ring
    _ = _ := by ring

theorem preprocessed_mean_below_cutoff (N c : ℕ) (μ : ℝ) (hN : 0 < N)
    (hc : 5 ≤ c) (hμ : 0 ≤ μ) (hmean : μ ≤ 2*Real.log (N:ℝ)) :
    Real.exp 1*μ ≤ (polynomialCutoff N c : ℝ) := by
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hlog := real_log_le_nat_log_shift N hN
  have hc' : (6:ℝ) ≤ (c:ℝ)+1 := by exact_mod_cast (by omega : 6 ≤ c+1)
  calc
    _ ≤ 3*μ := mul_le_mul_of_nonneg_right he hμ
    _ ≤ 3*(2*Real.log (N:ℝ)) := mul_le_mul_of_nonneg_left hmean (by norm_num)
    _ ≤ 6*(Nat.log 2 N+1 : ℕ) := by linarith
    _ ≤ ((c:ℝ)+1)*(Nat.log 2 N+1 : ℕ) :=
      mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg _)
    _ = _ := by simp only [polynomialCutoff, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

/-- Finite form of the component-shattering lemma in the preprocessed regime.
All coverage and sampling-tail premises are proved, including the source mean. -/
theorem preprocessed_log_squared_component_tail (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D M T N c : ℕ) (f : C → ℝ) (d : ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (hDL : ∀ u a, (sourceBucket encode u a).card ≤ DL a)
    (hL : ∀ a u, Peeling.leftDegree (H a) u ≤ D)
    (hR : ∀ a v, Peeling.rightDegree (H a) v ≤ DR a)
    (hM : ∀ u, (leftSourceBucket encode u).card ≤ M)
    (hT : 0 < T) (hTN : T ≤ N) (hf : ∀ a, 1 < f a)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N)
    (hc : 5 ≤ c) (hdegree : (M:ℝ) ≤ d*Real.log (N:ℝ))
    (haverage : 2*(Fintype.card E : ℝ) = (N:ℝ)*d) :
    eventProbability (largeComponentEvent encode (automaticThresholds (E := E) DL DR D T f)
      T (3*(polynomialCutoff N c+1)^2)) ≤ 3/(N:ℝ)^c := by
  apply log_squared_component_tail H encode DL DR D M T N c f hsimple hsource hDL hL hR hM hT hf hN hLN hRN
  have hmean := preprocessing_mean_bound M T N (Fintype.card E) d Fintype.card_pos hTN hdegree haverage
  have hbound := preprocessed_mean_below_cutoff N c ((T:ℝ)*M/Fintype.card E) hN hc (by positivity) hmean
  convert hbound using 1 <;> ring

end GraphChoices.Patterns
