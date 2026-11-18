import GraphChoices.ShatteringBounds
import Mathlib.Data.Real.Archimedean

/-! An explicit rounded threshold satisfying both local numerical conditions.
This finite formula is not yet bounded by the paper's asymptotic budget. -/
namespace GraphChoices

noncomputable def sufficientThreshold (mean f logRequirement : ℝ) : ℕ :=
  ⌈max (f * mean) logRequirement⌉₊ + 1

theorem sufficientThreshold_pos (mean f z : ℝ) : 0 < sufficientThreshold mean f z := by
  unfold sufficientThreshold
  omega

theorem sufficientThreshold_dominates (mean f z : ℝ) :
    max (f*mean) z ≤ (sufficientThreshold mean f z : ℝ) := by
  have h := Nat.le_ceil (max (f*mean) z)
  simp only [sufficientThreshold, Nat.cast_add, Nat.cast_one]
  linarith

theorem sufficientThreshold_base (mean f z : ℝ) (hf : 0 < f) :
    mean / sufficientThreshold mean f z ≤ 1/f := by
  have hpos : (0:ℝ) < sufficientThreshold mean f z := by
    exact_mod_cast sufficientThreshold_pos mean f z
  apply (div_le_div_iff₀ hpos hf).mpr
  have h := (le_max_left (f*mean) z).trans (sufficientThreshold_dominates mean f z)
  nlinarith

theorem sufficientThreshold_log (mean f z : ℝ) :
    z ≤ (sufficientThreshold mean f z : ℝ) :=
  (le_max_right (f*mean) z).trans (sufficientThreshold_dominates mean f z)

end GraphChoices

namespace GraphChoices.Patterns
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

noncomputable def explicitThresholds (DL DR : C → ℕ) (T : ℕ) (f : C → ℝ) (b : ℝ) : C → ℕ :=
  fun c => sufficientThreshold (Real.exp 1*T*(DL c : ℝ)/Fintype.card E) (f c)
    (Real.log (((DR c : ℝ)*((T:ℝ)/Fintype.card E))/b) / Real.log (f c))

/-- Geometric pattern-union decay for concrete rounded integer thresholds;
no local threshold inequalities are left as premises. -/
theorem heavyShape_decay_explicit (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D T m : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (b r : ℝ) (hT : 0 < T) (hb : 0 < b) (hr : 0 ≤ r) (hbr : b ≤ r)
    (hpair : (D : ℝ)*((T:ℝ)/Fintype.card E)*b ≤ r^2)
    (hf : ∀ c, 1 < f c) :
    eventProbability (heavyShapeEvent H encode (explicitThresholds (E := E) DL DR T f b) T m) ≤
      (Fintype.card R : ℝ)*(4*(Fintype.card C : ℝ)*r)^m := by
  apply heavyShape_decay_of_thresholds H encode _ DL DR D f hsimple hDL hL hR
    b r hT hb hr hbr hpair hf
  · intro c
    exact sufficientThreshold_base _ _ _ (by linarith [hf c])
  · intro c _
    exact sufficientThreshold_log _ _ _

end GraphChoices.Patterns
