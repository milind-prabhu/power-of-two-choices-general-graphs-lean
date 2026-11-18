import GraphChoices.ListArrivalGraph
import GraphChoices.ResidualTreeBound

/-! Every edge of the actual residual graph has an original sampled time and
base-edge label. This connects graph witnesses to the occurrence-based events
used in the checked probability estimates. -/
namespace GraphChoices.ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [DecidableEq C]
  {T : ℕ}

theorem mem_residual_sample_iff (encode : E → Arrival L R C) (α : C → ℕ)
    (ω : Fin T → E) (e : Arrival L R C) :
    e ∈ residualArrivals (trace α (sampleArrivals encode ω)) ↔
      ∃ t : Fin T, encode (ω t) = e ∧ residualTime α encode ω t := by
  constructor
  · intro he
    obtain ⟨ev, hev, ha⟩ := List.mem_map.mp he
    obtain ⟨htrace, hres⟩ := List.mem_filter.mp hev
    have hfalse : ev.threshold = false := by simpa using hres
    obtain ⟨i, htime, _⟩ := trace_mem_arrival α (sampleArrivals encode ω) ev htrace
    let t : Fin T := ⟨ev.time, by
      have hi := i.isLt
      have hlen := sampleArrivals_length encode ω
      omega⟩
    have hs := sample_event_arrival α encode ω ev htrace t rfl
    exact ⟨t, hs.symm.trans ha, ev, htrace, rfl, hfalse⟩
  · rintro ⟨t, he, ev, hev, ht, hres⟩
    apply List.mem_map.mpr
    refine ⟨ev, List.mem_filter.mpr ⟨hev, by simpa [hres]⟩, ?_⟩
    exact (sample_event_arrival α encode ω ev hev t ht).trans he

theorem residual_adj_iff_time (encode : E → Arrival L R C) (α : C → ℕ)
    (ω : Fin T → E) (x y : L ⊕ R) :
    (arrivalGraph (residualInstance α (sampleArrivals encode ω))).Adj x y ↔
      x ≠ y ∧ ∃ t : Fin T, residualTime α encode ω t ∧
        ((Sum.inl (encode (ω t)).left = x ∧ Sum.inr (encode (ω t)).right = y) ∨
         (Sum.inl (encode (ω t)).left = y ∧ Sum.inr (encode (ω t)).right = x)) := by
  rw [residualInstance, replay_adj_iff]
  constructor
  · rintro ⟨hne, e, he, hxy⟩
    obtain ⟨t, ht, hres⟩ := (mem_residual_sample_iff encode α ω e).mp he
    exact ⟨hne, t, hres, by simpa only [ht] using hxy⟩
  · rintro ⟨hne, t, hres, hxy⟩
    exact ⟨hne, encode (ω t), (mem_residual_sample_iff encode α ω _).mpr ⟨t, rfl, hres⟩, hxy⟩

theorem residual_adj_inl_inr_iff_time (encode : E → Arrival L R C) (α : C → ℕ)
    (ω : Fin T → E) (u : L) (v : R) :
    (arrivalGraph (residualInstance α (sampleArrivals encode ω))).Adj (Sum.inl u) (Sum.inr v) ↔
      ∃ t : Fin T, residualTime α encode ω t ∧
        (encode (ω t)).left = u ∧ (encode (ω t)).right = v := by
  rw [residual_adj_iff_time]
  simp

end GraphChoices.ThresholdGreedy
