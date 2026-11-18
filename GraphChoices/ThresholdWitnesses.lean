import GraphChoices.ResidualReplay

/-! Distinct, earlier threshold occurrences are necessary witnesses for every
residual arrival. Their time labels are disjoint from the entire residual log,
so they cannot be reused as selected residual-tree occurrences. -/
namespace GraphChoices.ThresholdGreedy
variable {L R C : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq C]

def thresholdBucket (log : List (Event L R C)) (u : L) (i : C) : List (Event L R C) :=
  log.filter fun ev => ev.threshold && decide (ev.arrival.left = u ∧ ev.arrival.cls = i)

def thresholdWitnessTimes (α : C → ℕ) (es : List (Arrival L R C)) (u : L) (i : C) : List ℕ :=
  (thresholdBucket (trace α es) u i).map Event.time

 theorem thresholdBucket_length (log : List (Event L R C)) (u : L) (i : C) :
    (thresholdBucket log u i).length = incidentCount (thresholdArrivals log) u i := by
  simp [thresholdBucket, incidentCount, thresholdArrivals, List.filter_map, List.filter_filter, Bool.and_comm]

 theorem thresholdWitnessTimes_length (α : C → ℕ) (es : List (Arrival L R C)) (u : L) (i : C) :
    (thresholdWitnessTimes α es u i).length = (run α es).threshold u i := by
  simp only [thresholdWitnessTimes, List.length_map, thresholdBucket_length, threshold_counter_exact]

 theorem thresholdWitnessTimes_nodup (α : C → ℕ) (es : List (Arrival L R C)) (u : L) (i : C) :
    (thresholdWitnessTimes α es u i).Nodup := by
  apply List.Nodup.sublist (List.Sublist.map Event.time (List.filter_sublist))
  exact traceFrom_unique_times α initial 0 es

 theorem trace_prefix_mem (α : C → ℕ) (xs ys : List (Arrival L R C))
    (ev : Event L R C) (hev : ev ∈ trace α xs) : ev ∈ trace α (xs ++ ys) := by
  unfold trace
  rw [traceFrom_append]
  exact List.mem_append_left _ hev

 theorem thresholdWitnessTimes_spec (α : C → ℕ) (es : List (Arrival L R C)) (u : L) (i : C)
    (t : ℕ) (ht : t ∈ thresholdWitnessTimes α es u i) :
    ∃ ev ∈ trace α es, ev.time = t ∧ ev.threshold = true ∧ ev.arrival.left = u ∧ ev.arrival.cls = i := by
  obtain ⟨ev,hev,hetime⟩ := List.mem_map.mp ht
  have h := List.mem_filter.mp hev
  have hh : ev.threshold = true ∧ (ev.arrival.left = u ∧ ev.arrival.cls = i) := by
    simpa using h.2
  exact ⟨ev,h.1,hetime,hh.1,hh.2⟩

 theorem traceFrom_time_lt (α : C → ℕ) (s : State L R C) (k : ℕ)
    (es : List (Arrival L R C)) (ev : Event L R C) (hev : ev ∈ traceFrom α s k es) :
    ev.time < k + es.length := by
  induction es generalizing s k with
  | nil => simp [traceFrom] at hev
  | cons e es ih =>
    rcases List.mem_cons.mp hev with rfl | hev
    · simp
    · have ht := ih (step α s e) (k+1) hev
      simp only [List.length_cons]
      omega

 theorem thresholdWitnessTimes_earlier (α : C → ℕ) (es : List (Arrival L R C)) (u : L) (i : C)
    (t : ℕ) (ht : t ∈ thresholdWitnessTimes α es u i) : t < es.length := by
  obtain ⟨ev,hev,hetime,_⟩ := thresholdWitnessTimes_spec α es u i t ht
  have h := traceFrom_time_lt α initial 0 es ev hev
  simpa [hetime] using h

 theorem thresholdWitnessTimes_disjoint_residual (α : C → ℕ) (xs ys : List (Arrival L R C))
    (u : L) (i : C) :
    List.Disjoint (thresholdWitnessTimes α xs u i)
      (((trace α (xs ++ ys)).filter fun ev => !ev.threshold).map Event.time) := by
  apply List.disjoint_left.mpr
  intro t ht hr
  obtain ⟨ev,hev,hetime,heth,_,_⟩ := thresholdWitnessTimes_spec α xs u i t ht
  have hfull := trace_prefix_mem α xs ys ev hev
  have htfull : t ∈ (((trace α (xs ++ ys)).filter fun ev => ev.threshold).map Event.time) :=
    List.mem_map.mpr ⟨ev,List.mem_filter.mpr ⟨hfull,heth⟩,hetime⟩
  exact List.disjoint_left.mp (trace_threshold_residual_disjoint α (xs ++ ys)) htfull hr

/-- A residual class-i arrival forces alpha_i distinct earlier threshold
occurrences in its bucket, disjoint from every residual occurrence in the full
execution. The suffix is arbitrary and can include the current arrival. -/
 theorem residual_distinct_threshold_witnesses (α : C → ℕ) (xs ys : List (Arrival L R C))
    (e : Arrival L R C) (he : isThreshold α (run α xs) e = false) :
    ∃ W : List ℕ, W.Nodup ∧ W.length = α e.cls ∧
      (∀ t ∈ W, t < xs.length) ∧
      List.Disjoint W (((trace α (xs ++ ys)).filter fun ev => !ev.threshold).map Event.time) ∧
      ∀ t ∈ W, ∃ ev ∈ trace α xs,
        ev.time = t ∧ ev.threshold = true ∧ ev.arrival.left = e.left ∧ ev.arrival.cls = e.cls := by
  refine ⟨thresholdWitnessTimes α xs e.left e.cls,
    thresholdWitnessTimes_nodup α xs _ _, ?_, ?_, ?_, ?_⟩
  · rw [thresholdWitnessTimes_length]
    exact residual_counter_saturated α xs e he
  · exact thresholdWitnessTimes_earlier α xs _ _
  · exact thresholdWitnessTimes_disjoint_residual α xs ys _ _
  · exact thresholdWitnessTimes_spec α xs _ _

end GraphChoices.ThresholdGreedy
