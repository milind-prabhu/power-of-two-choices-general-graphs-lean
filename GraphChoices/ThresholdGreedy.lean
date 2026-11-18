import GraphChoices.Model

/-! Executable Threshold-Greedy, with class counters for threshold edges and
separate loads for the single residual Greedy process (Algorithm 1).
Counters start at zero. A counter that reaches its threshold never changes,
so using threshold counters implements the threshold phase in the paper. -/
namespace GraphChoices.ThresholdGreedy
open Finset
variable {L R C : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq C]

structure Arrival (L R C : Type*) where
  left : L
  right : R
  cls : C

structure State (L R C : Type*) where
  threshold : L → C → ℕ
  greedyLeft : L → ℕ
  greedyRight : R → ℕ

def initial : State L R C := ⟨fun _ _ => 0, fun _ => 0, fun _ => 0⟩

def isThreshold (α : C → ℕ) (s : State L R C) (e : Arrival L R C) : Bool :=
  decide (s.threshold e.left e.cls < α e.cls)

def step (α : C → ℕ) (s : State L R C) (e : Arrival L R C) : State L R C :=
  if s.threshold e.left e.cls < α e.cls then
    { s with threshold := fun u i => s.threshold u i + if u = e.left ∧ i = e.cls then 1 else 0 }
  else if s.greedyLeft e.left < s.greedyRight e.right then
    { s with greedyLeft := fun u => s.greedyLeft u + if u = e.left then 1 else 0 }
  else
    { s with greedyRight := fun v => s.greedyRight v + if v = e.right then 1 else 0 }

def runFrom (α : C → ℕ) : State L R C → List (Arrival L R C) → State L R C
  | s, [] => s
  | s, e :: es => runFrom α (step α s e) es

def run (α : C → ℕ) (es : List (Arrival L R C)) : State L R C :=
  runFrom α initial es

 theorem runFrom_append (α : C → ℕ) (s : State L R C) (xs ys : List (Arrival L R C)) :
    runFrom α s (xs ++ ys) = runFrom α (runFrom α s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons e es ih => exact ih (step α s e)

 theorem run_append_singleton (α : C → ℕ) (xs : List (Arrival L R C)) (e : Arrival L R C) :
    run α (xs ++ [e]) = step α (run α xs) e := by
  exact runFrom_append α initial xs [e]

 theorem step_preserves_caps (α : C → ℕ) (s : State L R C) (e : Arrival L R C)
    (hs : ∀ u i, s.threshold u i ≤ α i) :
    ∀ u i, (step α s e).threshold u i ≤ α i := by
  intro u i
  unfold step
  split_ifs with ht hg
  · dsimp
    by_cases h : u = e.left ∧ i = e.cls
    · rcases h with ⟨rfl, rfl⟩
      simp
      omega
    · simpa [h] using hs u i
  · exact hs u i
  · exact hs u i

 theorem runFrom_preserves_caps (α : C → ℕ) (s : State L R C)
    (es : List (Arrival L R C)) (hs : ∀ u i, s.threshold u i ≤ α i) :
    ∀ u i, (runFrom α s es).threshold u i ≤ α i := by
  induction es generalizing s with
  | nil => exact hs
  | cons e es ih => exact ih _ (step_preserves_caps α s e hs)

 theorem threshold_cap (α : C → ℕ) (es : List (Arrival L R C)) (u : L) (i : C) :
    (run α es).threshold u i ≤ α i :=
  runFrom_preserves_caps α initial es (fun _ _ => Nat.zero_le _) u i

 theorem threshold_budget [Fintype C] (α : C → ℕ) (es : List (Arrival L R C)) (u : L) :
    ∑ i, (run α es).threshold u i ≤ ∑ i, α i :=
  sum_le_sum fun i _ => threshold_cap α es u i

/-- A residual edge can occur only once its class counter is saturated. -/
 theorem residual_counter_saturated (α : C → ℕ) (es : List (Arrival L R C))
    (e : Arrival L R C) (he : isThreshold α (run α es) e = false) :
    (run α es).threshold e.left e.cls = α e.cls := by
  have hlo : α e.cls ≤ (run α es).threshold e.left e.cls := by
    simpa [isThreshold] using he
  exact Nat.le_antisymm (threshold_cap α es _ _) hlo

/-- The number of previous arrivals in a left-vertex/class bucket. -/
def incidentCount (es : List (Arrival L R C)) (u : L) (i : C) : ℕ :=
  (es.filter fun e => decide (e.left = u ∧ e.cls = i)).length

 theorem step_counter_le (α : C → ℕ) (s : State L R C) (e : Arrival L R C) (u : L) (i : C) :
    (step α s e).threshold u i ≤ s.threshold u i + if e.left = u ∧ e.cls = i then 1 else 0 := by
  unfold step
  split_ifs <;> simp_all [eq_comm]

 theorem counter_le_incident (α : C → ℕ) (es : List (Arrival L R C)) (u : L) (i : C) :
    (run α es).threshold u i ≤ incidentCount es u i := by
  induction es using List.reverseRecOn with
  | nil => simp [run, runFrom, initial, incidentCount]
  | append_singleton es e ih =>
    rw [run_append_singleton]
    have hstep := step_counter_le α (run α es) e u i
    have hc : incidentCount (es ++ [e]) u i =
        incidentCount es u i + if e.left = u ∧ e.cls = i then 1 else 0 := by
      by_cases he : e.left = u ∧ e.cls = i <;> simp [incidentCount, List.filter_append, he]
    rw [hc]
    omega

/-- The necessary incidence condition behind the pattern probability bound. -/
 theorem residual_requires_previous_arrivals (α : C → ℕ) (es : List (Arrival L R C))
    (e : Arrival L R C) (he : isThreshold α (run α es) e = false) :
    α e.cls ≤ incidentCount es e.left e.cls := by
  rw [← residual_counter_saturated α es e he]
  exact counter_le_incident α es _ _

/-- On a residual arrival the counter is unchanged and the selected endpoint
has minimum residual load. Ties go right, as in Algorithm 1. -/
 theorem residual_step (α : C → ℕ) (s : State L R C) (e : Arrival L R C)
    (he : isThreshold α s e = false) :
    (step α s e).threshold = s.threshold ∧
    ((s.greedyLeft e.left < s.greedyRight e.right ∧
        (step α s e).greedyLeft e.left = s.greedyLeft e.left + 1 ∧
        (step α s e).greedyRight = s.greedyRight) ∨
      (s.greedyRight e.right ≤ s.greedyLeft e.left ∧
        (step α s e).greedyRight e.right = s.greedyRight e.right + 1 ∧
        (step α s e).greedyLeft = s.greedyLeft)) := by
  have ht : ¬s.threshold e.left e.cls < α e.cls := by simpa [isThreshold] using he
  unfold step
  rw [if_neg ht]
  split_ifs with hg
  · simp [hg]
  · simp [hg, Nat.le_of_not_gt hg]

end GraphChoices.ThresholdGreedy
