import GraphChoices.ThresholdGreedy
import Mathlib.Data.List.Range
import Mathlib.Data.List.Nodup
import Aesop

/-! Occurrence-preserving execution logs and exact replay of residual arrivals
by a single ordinary Greedy process. Repeated edges carry distinct time labels.
-/
namespace GraphChoices.ThresholdGreedy
variable {L R C : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq C]

structure Event (L R C : Type*) where
  time : ℕ
  arrival : Arrival L R C
  threshold : Bool

def traceFrom (α : C → ℕ) : State L R C → ℕ → List (Arrival L R C) → List (Event L R C)
  | _, _, [] => []
  | s, k, e :: es =>
    ⟨k,e,isThreshold α s e⟩ :: traceFrom α (step α s e) (k+1) es

def trace (α : C → ℕ) (es : List (Arrival L R C)) : List (Event L R C) :=
  traceFrom α initial 0 es

def thresholdArrivals (log : List (Event L R C)) : List (Arrival L R C) :=
  (log.filter fun e => e.threshold).map Event.arrival

def residualArrivals (log : List (Event L R C)) : List (Arrival L R C) :=
  (log.filter fun e => !e.threshold).map Event.arrival

structure GreedyLoads (L R : Type*) where
  left : L → ℕ
  right : R → ℕ

def project (s : State L R C) : GreedyLoads L R := ⟨s.greedyLeft, s.greedyRight⟩

def greedyStep (s : GreedyLoads L R) (e : Arrival L R C) : GreedyLoads L R :=
  if s.left e.left < s.right e.right then
    {s with left := fun u => s.left u + if u = e.left then 1 else 0}
  else
    {s with right := fun v => s.right v + if v = e.right then 1 else 0}

def greedyRun : GreedyLoads L R → List (Arrival L R C) → GreedyLoads L R
  | s, [] => s
  | s, e::es => greedyRun (greedyStep s e) es

 theorem project_threshold_step (α : C → ℕ) (s : State L R C) (e : Arrival L R C)
    (h : isThreshold α s e = true) : project (step α s e) = project s := by
  have ht : s.threshold e.left e.cls < α e.cls := by simpa [isThreshold] using h
  simp [step, ht, project]

 theorem project_residual_step (α : C → ℕ) (s : State L R C) (e : Arrival L R C)
    (h : isThreshold α s e = false) : project (step α s e) = greedyStep (project s) e := by
  have ht : ¬ s.threshold e.left e.cls < α e.cls := by simpa [isThreshold] using h
  simp only [step, if_neg ht, greedyStep, project]
  split_ifs <;> rfl

/-- The implemented residual process is exactly ordinary Greedy replay on the
extracted residual list, with all classes combined. -/
 theorem residual_replay_from (α : C → ℕ) (s : State L R C) (k : ℕ)
    (es : List (Arrival L R C)) :
    project (runFrom α s es) = greedyRun (project s)
      (residualArrivals (traceFrom α s k es)) := by
  induction es generalizing s k with
  | nil => rfl
  | cons e es ih =>
    cases h : isThreshold α s e with
    | false =>
      simp only [traceFrom, residualArrivals, h, Bool.not_false, List.filter_cons_of_pos,
        List.map_cons, greedyRun]
      rw [← project_residual_step α s e h]
      exact ih _ _
    | true =>
      simp only [traceFrom, residualArrivals, h, Bool.not_true, List.filter_cons_of_neg]
      rw [← project_threshold_step α s e h]
      exact ih _ _

 theorem residual_replay (α : C → ℕ) (es : List (Arrival L R C)) :
    project (run α es) = greedyRun (project (initial : State L R C))
      (residualArrivals (trace α es)) := residual_replay_from α initial 0 es

/-- Counters count actual threshold occurrences, rather than all arrivals in
the corresponding bucket. -/
 theorem threshold_counter_exact_from (α : C → ℕ) (s : State L R C) (k : ℕ)
    (es : List (Arrival L R C)) (u : L) (i : C) :
    (runFrom α s es).threshold u i = s.threshold u i +
      incidentCount (thresholdArrivals (traceFrom α s k es)) u i := by
  induction es generalizing s k with
  | nil => simp [runFrom, traceFrom, thresholdArrivals, incidentCount]
  | cons e es ih =>
    cases h : isThreshold α s e with
    | false =>
      have ht : ¬s.threshold e.left e.cls < α e.cls := by simpa [isThreshold] using h
      simp only [runFrom, traceFrom, thresholdArrivals, h, List.filter_cons_of_neg]
      rw [ih (step α s e) (k+1)]
      simp only [step, if_neg ht]
      split_ifs <;> rfl
    | true =>
      have ht : s.threshold e.left e.cls < α e.cls := by simpa [isThreshold] using h
      simp only [runFrom, traceFrom, thresholdArrivals, h, List.filter_cons_of_pos, List.map_cons]
      rw [ih (step α s e) (k+1)]
      simp only [thresholdArrivals, step, if_pos ht, incidentCount, List.filter_cons]
      by_cases he : e.left = u ∧ e.cls = i
      · obtain ⟨rfl,rfl⟩ := he
        simp
        omega
      · have he' : ¬(u = e.left ∧ i = e.cls) := by aesop
        simp [he, he']

 theorem threshold_counter_exact (α : C → ℕ) (es : List (Arrival L R C)) (u : L) (i : C) :
    (run α es).threshold u i = incidentCount (thresholdArrivals (trace α es)) u i := by
  simpa [run, trace, initial] using threshold_counter_exact_from α initial 0 es u i

 theorem residual_has_threshold_witnesses (α : C → ℕ) (es : List (Arrival L R C))
    (e : Arrival L R C) (he : isThreshold α (run α es) e = false) :
    incidentCount (thresholdArrivals (trace α es)) e.left e.cls = α e.cls := by
  rw [← threshold_counter_exact]
  exact residual_counter_saturated α es e he

/-- The log records every occurrence in its original position. -/
 theorem traceFrom_arrivals (α : C → ℕ) (s : State L R C) (k : ℕ)
    (es : List (Arrival L R C)) : (traceFrom α s k es).map Event.arrival = es := by
  induction es generalizing s k with
  | nil => rfl
  | cons e es ih => simp [traceFrom, ih]

 theorem traceFrom_times (α : C → ℕ) (s : State L R C) (k : ℕ)
    (es : List (Arrival L R C)) :
    (traceFrom α s k es).map Event.time = List.range' k es.length := by
  induction es generalizing s k with
  | nil => simp [traceFrom]
  | cons e es ih => simp [traceFrom, ih, List.range'_succ]

 theorem traceFrom_unique_times (α : C → ℕ) (s : State L R C) (k : ℕ)
    (es : List (Arrival L R C)) : ((traceFrom α s k es).map Event.time).Nodup := by
  rw [traceFrom_times]
  exact List.nodup_range'

/-- Threshold and residual logs partition the occurrence log up to permutation.
Their internal order is retained by the filter operations. -/
 theorem trace_partition (α : C → ℕ) (es : List (Arrival L R C)) :
    (thresholdArrivals (trace α es) ++ residualArrivals (trace α es)).Perm es := by
  have h := List.filter_append_perm (fun e : Event L R C => e.threshold) (trace α es)
  have hh := h.map Event.arrival
  simpa [thresholdArrivals, residualArrivals, List.map_append, trace, traceFrom_arrivals] using hh

theorem traceFrom_append (α : C → ℕ) (s : State L R C) (k : ℕ)
    (xs ys : List (Arrival L R C)) :
    traceFrom α s k (xs ++ ys) = traceFrom α s k xs ++
      traceFrom α (runFrom α s xs) (k + xs.length) ys := by
  induction xs generalizing s k with
  | nil => simp [traceFrom, runFrom]
  | cons e es ih =>
    simp [traceFrom, runFrom, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Distinct time labels make threshold witnesses disjoint from all residual
occurrences, even when their base-edge labels are identical. -/
theorem threshold_residual_times_disjoint (log : List (Event L R C))
    (hunique : (log.map Event.time).Nodup) :
    List.Disjoint ((log.filter fun e => e.threshold).map Event.time)
      ((log.filter fun e => !e.threshold).map Event.time) := by
  apply List.disjoint_left.mpr
  intro t ht hr
  obtain ⟨e,he,het⟩ := List.mem_map.mp ht
  obtain ⟨f,hf,hft⟩ := List.mem_map.mp hr
  have hmemE := (List.mem_filter.mp he).1
  have hmemF := (List.mem_filter.mp hf).1
  have hef : e = f := List.inj_on_of_nodup_map hunique hmemE hmemF (het.trans hft.symm)
  have hetrue := (List.mem_filter.mp he).2
  have hffalse := (List.mem_filter.mp hf).2
  simp_all

theorem trace_threshold_residual_disjoint (α : C → ℕ) (es : List (Arrival L R C)) :
    List.Disjoint (((trace α es).filter fun e => e.threshold).map Event.time)
      (((trace α es).filter fun e => !e.threshold).map Event.time) :=
  threshold_residual_times_disjoint _ (traceFrom_unique_times α initial 0 es)

end GraphChoices.ThresholdGreedy
