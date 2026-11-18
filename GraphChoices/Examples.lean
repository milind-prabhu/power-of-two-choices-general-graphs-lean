import GraphChoices.Density
import GraphChoices.ThresholdGreedy

/-! Small exact regression examples. All use kernel-reduced `decide`; no
native decider or external solver is used. -/
namespace GraphChoices.Examples

private def repeated : Instance (Fin 2) 3 where
  left _ := 0
  right _ := 1

/-- Three parallel arrivals need optimum load two, rather than density 3/2. -/
theorem repeated_opt : opt repeated = 2 := by
  let a : Orientation 3 := fun t => decide (t.val < 2)
  have hm : maxLoad repeated a = 2 := by decide
  have hu := opt_le_maxLoad repeated a
  rw [hm] at hu
  have hl := total_le_card_mul_opt repeated
  norm_num at hl
  omega

private def oneEdge : ThresholdGreedy.Arrival (Fin 1) (Fin 1) (Fin 1) := ⟨0,0,0⟩

/-- Threshold one followed by residual Greedy with ties sent right. -/
theorem threshold_execution :
    let s := ThresholdGreedy.run (fun _ : Fin 1 => 1) [oneEdge, oneEdge, oneEdge, oneEdge]
    s.threshold 0 0 = 1 ∧ s.greedyLeft 0 = 1 ∧ s.greedyRight 0 = 2 := by decide

end GraphChoices.Examples
