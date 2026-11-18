import GraphChoices.ThresholdWitnesses
import Mathlib.Data.List.OfFn

/-! Links time-labelled execution events to their original input occurrences,
and represents actual threshold witness times as finite subsets of Fin T. -/
namespace GraphChoices.ThresholdGreedy
open Finset
variable {L R C : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq C]

 theorem traceFrom_mem_spec (α : C → ℕ) (s : State L R C) (k : ℕ)
    (es : List (Arrival L R C)) (ev : Event L R C) (hev : ev ∈ traceFrom α s k es) :
    ∃ i : Fin es.length, ev.time = k+i.val ∧ ev.arrival = es.get i ∧
      ev.threshold = isThreshold α (runFrom α s (es.take i.val)) (es.get i) := by
  induction es generalizing s k with
  | nil => simp [traceFrom] at hev
  | cons e es ih =>
    rcases List.mem_cons.mp hev with rfl | hev
    · exact ⟨⟨0,by simp⟩,by simp, rfl, rfl⟩
    · obtain ⟨i,hti,hai,hthi⟩ := ih (step α s e) (k+1) hev
      refine ⟨i.succ,?_,?_,?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hti
      · simpa using hai
      · simpa [List.take_succ_cons, runFrom] using hthi

 theorem trace_mem_arrival (α : C → ℕ) (es : List (Arrival L R C))
    (ev : Event L R C) (hev : ev ∈ trace α es) :
    ∃ i : Fin es.length, ev.time = i.val ∧ ev.arrival = es.get i := by
  obtain ⟨i,ht,ha,_⟩ := traceFrom_mem_spec α initial 0 es ev hev
  exact ⟨i,by simpa using ht,ha⟩

 theorem step_counter_mono (α : C → ℕ) (s : State L R C) (e : Arrival L R C) (u : L) (i : C) :
    s.threshold u i ≤ (step α s e).threshold u i := by
  unfold step
  split_ifs <;> simp

 theorem runFrom_counter_mono (α : C → ℕ) (s : State L R C)
    (es : List (Arrival L R C)) (u : L) (i : C) :
    s.threshold u i ≤ (runFrom α s es).threshold u i := by
  induction es generalizing s with
  | nil => exact le_rfl
  | cons e es ih => exact (step_counter_mono α s e u i).trans (ih (step α s e))

 theorem run_counter_mono_append (α : C → ℕ) (xs ys : List (Arrival L R C)) (u : L) (i : C) :
    (run α xs).threshold u i ≤ (run α (xs ++ ys)).threshold u i := by
  unfold run
  rw [runFrom_append]
  exact runFrom_counter_mono α _ ys u i

/-- A residual occurrence saturates its bucket in the complete execution. -/
 theorem residual_event_final_saturated (α : C → ℕ) (es : List (Arrival L R C))
    (ev : Event L R C) (hev : ev ∈ trace α es) (hr : ev.threshold = false) :
    (run α es).threshold ev.arrival.left ev.arrival.cls = α ev.arrival.cls := by
  obtain ⟨i,ht,ha,hth⟩ := traceFrom_mem_spec α initial 0 es ev hev
  have hres : isThreshold α (run α (es.take i.val)) (es.get i) = false := by
    simpa only [run] using hth.symm.trans hr
  have hsat := residual_counter_saturated α (es.take i.val) (es.get i) hres
  have hmono := run_counter_mono_append α (es.take i.val) (es.drop i.val) (es.get i).left (es.get i).cls
  rw [List.take_append_drop, hsat] at hmono
  have hcap := threshold_cap α es (es.get i).left (es.get i).cls
  simpa [ha] using Nat.le_antisymm hcap hmono

noncomputable def finiteThresholdTimes (α : C → ℕ) (es : List (Arrival L R C))
    (T : ℕ) (hlen : es.length = T) (u : L) (i : C) : Finset (Fin T) := by
  classical
  let K := (thresholdWitnessTimes α es u i).toFinset
  exact K.attach.image fun t => ⟨t.val, by
    have ht := thresholdWitnessTimes_earlier α es u i t.val (List.mem_toFinset.mp t.property)
    omega⟩

 theorem mem_finiteThresholdTimes (α : C → ℕ) (es : List (Arrival L R C))
    (T : ℕ) (hlen : es.length = T) (u : L) (i : C) (t : Fin T) :
    t ∈ finiteThresholdTimes α es T hlen u i ↔ t.val ∈ thresholdWitnessTimes α es u i := by
  classical
  unfold finiteThresholdTimes
  simp only [mem_image, mem_attach, true_and]
  constructor
  · rintro ⟨s,hs⟩
    have hv := congrArg Fin.val hs
    change s.val = t.val at hv
    rw [← hv]
    exact List.mem_toFinset.mp s.property
  · intro ht
    exact ⟨⟨t.val,List.mem_toFinset.mpr ht⟩,Fin.ext rfl⟩

 theorem finiteThresholdTimes_card (α : C → ℕ) (es : List (Arrival L R C))
    (T : ℕ) (hlen : es.length = T) (u : L) (i : C) :
    (finiteThresholdTimes α es T hlen u i).card = (run α es).threshold u i := by
  classical
  unfold finiteThresholdTimes
  rw [card_image_of_injective _ (by
    intro a b hab
    apply Subtype.ext
    exact congrArg Fin.val hab)]
  rw [card_attach, List.toFinset_card_of_nodup (thresholdWitnessTimes_nodup α es u i)]
  exact thresholdWitnessTimes_length α es u i

/-- Time labels identify a unique event, even across buckets. -/
 theorem trace_event_eq_of_time (α : C → ℕ) (es : List (Arrival L R C))
    (ev ev' : Event L R C) (h : ev ∈ trace α es) (h' : ev' ∈ trace α es)
    (ht : ev.time = ev'.time) : ev = ev' :=
  List.inj_on_of_nodup_map (traceFrom_unique_times α initial 0 es) h h' ht

 theorem finiteThresholdTimes_buckets_disjoint (α : C → ℕ) (es : List (Arrival L R C))
    (T : ℕ) (hlen : es.length = T) (u u' : L) (i i' : C) (hne : (u,i) ≠ (u',i')) :
    Disjoint (finiteThresholdTimes α es T hlen u i) (finiteThresholdTimes α es T hlen u' i') := by
  apply Finset.disjoint_left.mpr
  intro t ht ht'
  obtain ⟨ev,hev,hetime,_,hu,hi⟩ := thresholdWitnessTimes_spec α es u i t.val
    ((mem_finiteThresholdTimes α es T hlen u i t).mp ht)
  obtain ⟨ev',hev',hetime',_,hu',hi'⟩ := thresholdWitnessTimes_spec α es u' i' t.val
    ((mem_finiteThresholdTimes α es T hlen u' i' t).mp ht')
  have heq := trace_event_eq_of_time α es ev ev' hev hev' (hetime.trans hetime'.symm)
  apply hne
  exact Prod.ext (hu.symm.trans ((congrArg (fun e : Event L R C => e.arrival.left) heq).trans hu'))
    (hi.symm.trans ((congrArg (fun e : Event L R C => e.arrival.cls) heq).trans hi'))

end GraphChoices.ThresholdGreedy
