import GraphChoices.ShapePatterns
import GraphChoices.ThresholdDecay

/-! Probability tails for the canonical left-heavy tree family, derived from
explicit local threshold conditions. The deterministic coverage of arbitrary
large connected components by this family remains a separate graph theorem.
-/
namespace GraphChoices.Patterns
open Finset
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C] [DecidableEq L] [DecidableEq R] [DecidableEq C]
  {T m : ℕ}

 theorem heavyShape_decay_of_thresholds (H : C → Peeling.Graph L R)
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
      Real.log (((DR c : ℝ)*((T:ℝ)/Fintype.card E))/b) / Real.log (f c) ≤ (α c : ℝ)) :
    eventProbability (heavyShapeEvent H encode α T m) ≤
      (Fintype.card R : ℝ)*(4*(Fintype.card C : ℝ)*r)^m := by
  apply heavyShape_probability_le H encode α T m _ r (Nat.cast_nonneg _) hr
  intro s hs
  exact residualPattern_decay_of_thresholds (shapePattern s) H encode α DL DR D f
    hsimple hDL hL hR b r hT hb hr hbr hpair hf hbase hthreshold hs

 theorem heavyShape_geometric_tail (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (T m : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hdecay : eventProbability (heavyShapeEvent H encode α T m) ≤
      (Fintype.card R : ℝ)*(4*(Fintype.card C : ℝ)*r)^m)
    (hsmall : 4*(Fintype.card C : ℝ)*r ≤ 1/2) :
    eventProbability (heavyShapeEvent H encode α T m) ≤ (Fintype.card R : ℝ)/2^m := by
  calc
    _ ≤ (Fintype.card R : ℝ)*(4*(Fintype.card C : ℝ)*r)^m := hdecay
    _ ≤ (Fintype.card R : ℝ)*((1:ℝ)/2)^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsmall m) (Nat.cast_nonneg _)
    _ = _ := by rw [div_pow]; ring

/-- An explicit inverse-polynomial failure probability for the canonical
heavy-tree event. The exponent condition is exact and uses no asymptotic O. -/
 theorem heavyShape_polynomial_tail (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ) (T m N c : ℕ) (hN : 0 < N)
    (hR : Fintype.card R ≤ N)
    (hprob : eventProbability (heavyShapeEvent H encode α T m) ≤ (Fintype.card R : ℝ)/2^m)
    (hexponent : N^(c+1) ≤ 2^m) :
    eventProbability (heavyShapeEvent H encode α T m) ≤ 1/(N:ℝ)^c := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hexp : (N:ℝ)^(c+1) ≤ (2:ℝ)^m := by exact_mod_cast hexponent
  calc
    _ ≤ (Fintype.card R : ℝ)/2^m := hprob
    _ ≤ (N:ℝ)/2^m := div_le_div_of_nonneg_right (by exact_mod_cast hR) (by positivity)
    _ ≤ (N:ℝ)/(N:ℝ)^(c+1) := div_le_div_of_nonneg_left hNr.le (by positivity) hexp
    _ = _ := by rw [pow_succ]; field_simp

end GraphChoices.Patterns
