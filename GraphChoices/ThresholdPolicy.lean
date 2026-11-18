import GraphChoices.CanonicalCoverage
import GraphChoices.Targets

/-! The implemented full Threshold-Greedy state is an actual online policy.
Its expected load and full-sample benchmark agree with the original indexed
sample model, rather than a separate list-only performance notion. -/
namespace GraphChoices.ThresholdGreedy
open Finset
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

def encodedBaseGraph (encode : E → Arrival L R C) : BaseGraph (L ⊕ R) E where
  left e := Sum.inl (encode e).left
  right e := Sum.inr (encode e).right

theorem encoded_internalCount (encode : E → Arrival L R C) {T : ℕ} (ω : Fin T → E)
    (A : Finset (L ⊕ R)) :
    internalCount (replayInstance (sampleArrivals encode ω)) A =
      internalCount ((encodedBaseGraph encode).sample ω) A := by
  rw [replay_internalCount]
  unfold sampleArrivals
  rw [countP_ofFn_eq_sum]
  simp only [internalCount, BaseGraph.sample, encodedBaseGraph, card_eq_sum_ones, sum_filter,
    decide_eq_true_eq]

theorem encoded_opt (encode : E → Arrival L R C) {T : ℕ} (ω : Fin T → E) :
    opt (replayInstance (sampleArrivals encode ω)) = opt ((encodedBaseGraph encode).sample ω) := by
  apply Nat.le_antisymm
  · apply opt_le_of_internalCount_le
    intro A
    exact (encoded_internalCount encode ω A).le
  · apply opt_le_of_internalCount_le
    intro A
    exact (encoded_internalCount encode ω A).symm.le

theorem expectedReplayOpt_eq_expectedOpt (encode : E → Arrival L R C) (T : ℕ) :
    expectedReplayOpt encode T = expectedOpt (encodedBaseGraph encode) T := by
  unfold expectedReplayOpt expectedOpt
  congr 1
  funext ω
  rw [encoded_opt]

def stateLoad (s : State L R C) : L ⊕ R → ℕ :=
  Sum.elim (fun u => (∑ c, s.threshold u c) + s.greedyLeft u) s.greedyRight

def stepChoice (α : C → ℕ) (s : State L R C) (e : Arrival L R C) : Bool :=
  if s.threshold e.left e.cls < α e.cls then true
  else decide (s.greedyLeft e.left < s.greedyRight e.right)

theorem step_stateLoad (α : C → ℕ) (s : State L R C) (e : Arrival L R C) (v : L ⊕ R) :
    stateLoad (step α s e) v = stateLoad s v +
      if (if stepChoice α s e then Sum.inl e.left else Sum.inr e.right) = v then 1 else 0 := by
  by_cases ht : s.threshold e.left e.cls < α e.cls
  · cases v with
    | inl u =>
      by_cases hu : u = e.left <;>
        simp [stateLoad, step, stepChoice, ht, hu, sum_add_distrib, eq_comm, Nat.add_assoc,
          Nat.add_comm, Finset.filter_eq']
    | inr w => simp [stateLoad, step, stepChoice, ht]
  · by_cases hg : s.greedyLeft e.left < s.greedyRight e.right <;> cases v <;>
      simp [stateLoad, step, stepChoice, ht, hg, eq_comm, Nat.add_assoc]

/-- Only the preceding source labels and current label are inputs. -/
def thresholdPolicy (encode : E → Arrival L R C) (α : C → ℕ) : OnlinePolicy E :=
  fun history e => stepChoice α (run α (history.map encode)) (encode e)

def policyPrefixLoad (encode : E → Arrival L R C) (α : C → ℕ) {T : ℕ}
    (ω : Fin T → E) (k : ℕ) : L ⊕ R → ℕ :=
  stateLoad (run α (((List.ofFn ω).take k).map encode))

theorem policyPrefixLoad_zero (encode : E → Arrival L R C) (α : C → ℕ) {T : ℕ}
    (ω : Fin T → E) (v : L ⊕ R) : policyPrefixLoad encode α ω 0 v = 0 := by
  cases v <;> simp [policyPrefixLoad, run, runFrom, initial, stateLoad]

theorem policyPrefixLoad_step (encode : E → Arrival L R C) (α : C → ℕ) {T : ℕ}
    (ω : Fin T → E) (t : Fin T) (v : L ⊕ R) :
    policyPrefixLoad encode α ω (t.val+1) v = policyPrefixLoad encode α ω t.val v +
      if destination ((encodedBaseGraph encode).sample ω) (onlineOrientation (thresholdPolicy encode α) ω) t = v
      then 1 else 0 := by
  have hi : t.val < (List.ofFn ω).length := by simpa using t.isLt
  unfold policyPrefixLoad
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.map_singleton, run_append_singleton]
  rw [step_stateLoad]
  simp [List.getElem_ofFn, destination, encodedBaseGraph, BaseGraph.sample,
    onlineOrientation, thresholdPolicy]

theorem policy_final_load (encode : E → Arrival L R C) (α : C → ℕ) {T : ℕ}
    (ω : Fin T → E) (v : L ⊕ R) :
    totalVertexLoad α (sampleArrivals encode ω) v =
      load ((encodedBaseGraph encode).sample ω) (onlineOrientation (thresholdPolicy encode α) ω) v := by
  have h := execution_final_load ((encodedBaseGraph encode).sample ω)
    (onlineOrientation (thresholdPolicy encode α) ω) (policyPrefixLoad encode α ω)
    (policyPrefixLoad_zero encode α ω) (policyPrefixLoad_step encode α ω) v
  have htake : (List.ofFn ω).take T = List.ofFn ω := List.take_of_length_le (by simp)
  simpa only [policyPrefixLoad, htake, sampleArrivals, List.map_ofFn, stateLoad, totalVertexLoad] using h

theorem policy_maxLoad (encode : E → Arrival L R C) (α : C → ℕ) {T : ℕ} (ω : Fin T → E) :
    totalMaxLoad α (sampleArrivals encode ω) =
      maxLoad ((encodedBaseGraph encode).sample ω) (onlineOrientation (thresholdPolicy encode α) ω) := by
  unfold totalMaxLoad maxLoad
  apply Finset.sup_congr rfl
  intro v _
  exact policy_final_load encode α ω v

theorem expectedTotalMaxLoad_eq_expectedCost (encode : E → Arrival L R C) (α : C → ℕ) (T : ℕ) :
    expectedTotalMaxLoad encode α T =
      expectedCost (encodedBaseGraph encode) (onlineOrientation (T := T) (thresholdPolicy encode α)) := by
  unfold expectedTotalMaxLoad expectedCost
  congr 1
  funext ω
  rw [policy_maxLoad]

end GraphChoices.ThresholdGreedy
