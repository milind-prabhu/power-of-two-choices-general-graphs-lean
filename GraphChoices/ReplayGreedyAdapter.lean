import GraphChoices.GreedyExecution
import GraphChoices.ResidualReplay
import Mathlib.Data.Fintype.Sum

/-! The ordinary residual replay is an actual indexed Greedy orientation.
Its counted loads equal the implemented state, so the checked adversarial
Greedy theorem applies directly to Threshold-Greedy's residual execution. -/
namespace GraphChoices.ThresholdGreedy
variable {L R C : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

def zeroGreedy : GreedyLoads L R := ⟨fun _ => 0,fun _ => 0⟩

def greedyVertexLoad (s : GreedyLoads L R) : L ⊕ R → ℕ := Sum.elim s.left s.right

def greedyTarget (s : GreedyLoads L R) (e : Arrival L R C) : L ⊕ R :=
  if s.left e.left < s.right e.right then Sum.inl e.left else Sum.inr e.right

 theorem greedyVertexLoad_step (s : GreedyLoads L R) (e : Arrival L R C) (v : L ⊕ R) :
    greedyVertexLoad (greedyStep s e) v = greedyVertexLoad s v + if greedyTarget s e = v then 1 else 0 := by
  by_cases hs : s.left e.left < s.right e.right <;> cases v <;>
    simp [greedyVertexLoad, greedyStep, greedyTarget, hs, eq_comm]

 theorem greedyTarget_min (s : GreedyLoads L R) (e : Arrival L R C) :
    greedyVertexLoad s (greedyTarget s e) ≤ s.left e.left ∧
    greedyVertexLoad s (greedyTarget s e) ≤ s.right e.right := by
  by_cases hs : s.left e.left < s.right e.right
  · simp [greedyVertexLoad, greedyTarget, hs, Nat.le_of_lt hs]
  · simp [greedyVertexLoad, greedyTarget, hs, Nat.le_of_not_gt hs]

 theorem greedyRun_append (s : GreedyLoads L R) (xs ys : List (Arrival L R C)) :
    greedyRun s (xs ++ ys) = greedyRun (greedyRun s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => exact ih (greedyStep s e)

 theorem greedyRun_take_succ (es : List (Arrival L R C)) (t : Fin es.length) :
    greedyRun (zeroGreedy : GreedyLoads L R) (es.take (t.val+1)) =
      greedyStep (greedyRun zeroGreedy (es.take t.val)) (es.get t) := by
  rw [List.take_succ_eq_append_getElem t.isLt, greedyRun_append]
  rfl

def replayInstance (es : List (Arrival L R C)) : Instance (L ⊕ R) es.length where
  left t := Sum.inl (es.get t).left
  right t := Sum.inr (es.get t).right

def replayOrientation (es : List (Arrival L R C)) : Orientation es.length := fun t =>
  let s := greedyRun (zeroGreedy : GreedyLoads L R) (es.take t.val)
  decide (s.left (es.get t).left < s.right (es.get t).right)

def replayState (es : List (Arrival L R C)) (k : ℕ) : L ⊕ R → ℕ :=
  greedyVertexLoad (greedyRun (zeroGreedy : GreedyLoads L R) (es.take k))

 theorem replay_destination (es : List (Arrival L R C)) (t : Fin es.length) :
    destination (replayInstance es) (replayOrientation es) t =
      greedyTarget (greedyRun zeroGreedy (es.take t.val)) (es.get t) := by
  simp [destination, replayInstance, replayOrientation, greedyTarget]

 theorem replay_zero (es : List (Arrival L R C)) (v : L ⊕ R) : replayState es 0 v = 0 := by
  cases v <;> rfl

 theorem replay_increment (es : List (Arrival L R C)) (t : Fin es.length) (v : L ⊕ R) :
    replayState es (t.val+1) v = replayState es t.val v +
      if destination (replayInstance es) (replayOrientation es) t = v then 1 else 0 := by
  unfold replayState
  rw [greedyRun_take_succ, greedyVertexLoad_step, replay_destination]

 theorem replay_isGreedy (es : List (Arrival L R C)) :
    IsGreedy (replayInstance es) (replayOrientation es) := by
  apply isGreedy_of_execution (replayInstance es) (replayOrientation es) (replayState es)
    (replay_zero es) (replay_increment es)
  intro t v hv
  have hmin := greedyTarget_min (greedyRun zeroGreedy (es.take t.val)) (es.get t)
  rw [replay_destination]
  rcases hv with rfl | rfl
  · exact hmin.1
  · exact hmin.2

 theorem replay_final_load (es : List (Arrival L R C)) (v : L ⊕ R) :
    greedyVertexLoad (greedyRun (zeroGreedy : GreedyLoads L R) es) v =
      load (replayInstance es) (replayOrientation es) v := by
  simpa [replayState] using execution_final_load (replayInstance es) (replayOrientation es)
    (replayState es) (replay_zero es) (replay_increment es) v

/-- The actual residual left load obeys the proved deterministic Greedy bound.
The optimum here is the samplewise optimum of the residual arrival instance. -/
 theorem residual_left_competitive (α : C → ℕ) (es : List (Arrival L R C))
    (u : L) (hres : 0 < (residualArrivals (trace α es)).length) :
    (run α es).greedyLeft u <
      2 * opt (replayInstance (residualArrivals (trace α es))) *
        (Nat.log 2 (Fintype.card (L ⊕ R)) + 1) := by
  let rs := residualArrivals (trace α es)
  have hr := residual_replay α es
  have hl : (run α es).greedyLeft u =
      greedyVertexLoad (greedyRun (zeroGreedy : GreedyLoads L R) rs) (Sum.inl u) := by
    exact congrArg (fun s : GreedyLoads L R => s.left u) hr
  rw [hl, replay_final_load]
  exact (load_le_maxLoad (replayInstance rs) (replayOrientation rs) (Sum.inl u)).trans_lt
    (greedy_competitive (replayInstance rs) (replayOrientation rs) (replay_isGreedy rs) hres)

 theorem residual_right_competitive (α : C → ℕ) (es : List (Arrival L R C))
    (v : R) (hres : 0 < (residualArrivals (trace α es)).length) :
    (run α es).greedyRight v <
      2 * opt (replayInstance (residualArrivals (trace α es))) *
        (Nat.log 2 (Fintype.card (L ⊕ R)) + 1) := by
  let rs := residualArrivals (trace α es)
  have hr := residual_replay α es
  have hl : (run α es).greedyRight v =
      greedyVertexLoad (greedyRun (zeroGreedy : GreedyLoads L R) rs) (Sum.inr v) := by
    exact congrArg (fun s : GreedyLoads L R => s.right v) hr
  rw [hl, replay_final_load]
  exact (load_le_maxLoad (replayInstance rs) (replayOrientation rs) (Sum.inr v)).trans_lt
    (greedy_competitive (replayInstance rs) (replayOrientation rs) (replay_isGreedy rs) hres)

end GraphChoices.ThresholdGreedy
