import GraphChoices.PatternDecay
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Explicit logarithmic threshold conditions imply the local decay needed by
the fixed-pattern probability theorem. No probability conclusion is assumed. -/
namespace GraphChoices

 theorem inverse_power_le_target (f target : ℝ) (k : ℕ)
    (hf : 1 < f) (ht : 0 < target)
    (hk : Real.log (1/target) / Real.log f ≤ (k:ℝ)) :
    ((1:ℝ)/f)^k ≤ target := by
  have hfpos : 0 < f := by linarith
  apply (Real.log_le_log_iff (pow_pos (div_pos zero_lt_one hfpos) _) ht).mp
  rw [Real.log_pow, Real.log_div (by norm_num) (ne_of_gt hfpos), Real.log_one]
  have hh := (div_le_iff₀ (Real.log_pos hf)).mp hk
  rw [Real.log_div (by norm_num) (ne_of_gt ht), Real.log_one] at hh
  linarith

 theorem power_le_target_of_threshold (x f target : ℝ) (k : ℕ)
    (hx : 0 ≤ x) (hf : 1 < f) (ht : 0 < target)
    (hbase : x ≤ 1/f) (hk : Real.log (1/target) / Real.log f ≤ (k:ℝ)) :
    x^k ≤ target :=
  (pow_le_pow_left₀ hx hbase k).trans (inverse_power_le_target f target k hf ht hk)

end GraphChoices

namespace GraphChoices.Patterns
open Finset
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [DecidableEq C]
  {T m : ℕ}

 theorem bucketDecay_small_of_threshold (α DL DR : C → ℕ) (f : C → ℝ) (T : ℕ)
    (b : ℝ) (hT : 0 < T) (hb : 0 < b) (hf : ∀ c, 1 < f c)
    (hbase : ∀ c, Real.exp 1*T*(DL c : ℝ)/Fintype.card E/α c ≤ 1/f c)
    (hthreshold : ∀ c, 0 < DR c →
      Real.log (((DR c : ℝ)*((T:ℝ)/Fintype.card E))/b) / Real.log (f c) ≤ (α c : ℝ)) :
    ∀ c, (DR c : ℝ)*((T:ℝ)/Fintype.card E)*bucketDecay (E := E) α DL T c ≤ b := by
  intro c
  by_cases hDR : DR c = 0
  · simp [hDR, le_of_lt hb]
  have hp : (0:ℝ) < (DR c : ℝ)*((T:ℝ)/Fintype.card E) := by
    have hd : (0:ℝ) < DR c := by exact_mod_cast Nat.pos_of_ne_zero hDR
    have ht : (0:ℝ) < T := by exact_mod_cast hT
    exact mul_pos hd (div_pos ht (by exact_mod_cast Fintype.card_pos))
  have htarget : 0 < b / ((DR c : ℝ)*((T:ℝ)/Fintype.card E)) := div_pos hb hp
  have hlog : Real.log (1 / (b / ((DR c : ℝ)*((T:ℝ)/Fintype.card E)))) /
      Real.log (f c) ≤ (α c : ℝ) := by
    simpa [one_div_div] using hthreshold c (Nat.pos_of_ne_zero hDR)
  have hdecay : bucketDecay (E := E) α DL T c ≤ b / ((DR c : ℝ)*((T:ℝ)/Fintype.card E)) :=
    GraphChoices.power_le_target_of_threshold _ _ _ _ (by positivity) (hf c) htarget (hbase c) hlog
  calc
    _ ≤ ((DR c : ℝ)*((T:ℝ)/Fintype.card E)) * (b / ((DR c : ℝ)*((T:ℝ)/Fintype.card E))) :=
      mul_le_mul_of_nonneg_left hdecay hp.le
    _ = b := by field_simp

/-- Conditional fixed-pattern decay with explicit base and logarithmic
threshold inequalities. Instantiation by the paper's alpha_i remains separate. -/
 theorem residualPattern_decay_of_thresholds (p : ParentPattern C m) (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (DL DR : C → ℕ) (D : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (b r : ℝ) (hT : 0 < T) (hb : 0 < b) (hr : 0 ≤ r) (hbr : b ≤ r)
    (hpair : (D : ℝ)*((T:ℝ)/Fintype.card E)*b ≤ r^2)
    (hf : ∀ c, 1 < f c)
    (hbase : ∀ c, Real.exp 1*T*(DL c : ℝ)/Fintype.card E/α c ≤ 1/f c)
    (hthreshold : ∀ c, 0 < DR c →
      Real.log (((DR c : ℝ)*((T:ℝ)/Fintype.card E))/b) / Real.log (f c) ≤ (α c : ℝ))
    (hheavy : m ≤ 2*(univ.filter fun i : Fin m => p.childLeft i = true).card) :
    eventProbability (residualPatternEvent p H encode α T) ≤ (Fintype.card R : ℝ)*r^m :=
  residualPattern_probability_decay p H encode α DL DR D hsimple hDL hL hR b r hb.le hr hbr hpair
    (bucketDecay_small_of_threshold α DL DR f T b hT hb hf hbase hthreshold) hheavy

end GraphChoices.Patterns
