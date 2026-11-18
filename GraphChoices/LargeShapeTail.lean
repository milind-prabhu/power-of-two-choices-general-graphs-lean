import GraphChoices.ShatteringBounds
import GraphChoices.ThresholdBudget

/-! Union over tree sizes as well as shapes. This avoids assuming that a
large left-heavy tree contains a left-heavy subtree of an exact chosen size.
Coverage by the canonical encoding is still a separate deterministic step. -/
namespace GraphChoices.Patterns
open Finset
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

noncomputable def largeShapeEvent (H : C → Peeling.Graph L R)
    (encode : E → ThresholdGreedy.Arrival L R C) (α : C → ℕ) (T k B : ℕ) : Finset (Fin T → E) :=
  (range (B+1)).biUnion fun j => heavyShapeEvent H encode α T (k+j)

theorem largeShape_probability_le (H : C → Peeling.Graph L R)
    (encode : E → ThresholdGreedy.Arrival L R C) (α : C → ℕ) (T k B : ℕ)
    (htail : ∀ j ≤ B, eventProbability (heavyShapeEvent H encode α T (k+j)) ≤
      (Fintype.card R : ℝ)/2^(k+j)) :
    eventProbability (largeShapeEvent H encode α T k B) ≤ 2*(Fintype.card R : ℝ)/2^k := by
  calc
    _ ≤ ∑ j ∈ range (B+1), eventProbability (heavyShapeEvent H encode α T (k+j)) :=
      witness_union_bound _ _
    _ ≤ ∑ j ∈ range (B+1), (Fintype.card R : ℝ)/2^(k+j) := by
      apply sum_le_sum
      intro j hj
      exact htail j (by have := mem_range.mp hj; omega)
    _ = ((Fintype.card R : ℝ)/2^k) * (∑ j ∈ range (B+1), (1:ℝ)/2^j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    _ ≤ ((Fintype.card R : ℝ)/2^k) * 2 :=
      mul_le_mul_of_nonneg_left (ThresholdGreedy.inverse_powers_sum_le_two _) (by positivity)
    _ = _ := by ring

end GraphChoices.Patterns
