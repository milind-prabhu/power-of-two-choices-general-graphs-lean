import GraphChoices.ExecutionIndex
import GraphChoices.WitnessEncoding

/-! The fixed-residual-tree event is contained in the counted joint witness
event. The proof uses actual execution counters and time labels, not an
assumed witness-encoding hypothesis. Tree geometry is only needed later for
counting embeddings and ensuring that left-vertex buckets are distinct. -/
namespace GraphChoices.ThresholdGreedy
open Finset
variable {E L R C J : Type*}
  [Fintype E] [DecidableEq E] [Nonempty E]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]
  [Fintype J] [DecidableEq J] {T m : ℕ}

def sampleArrivals (encode : E → Arrival L R C) (ω : Fin T → E) : List (Arrival L R C) :=
  List.ofFn fun t => encode (ω t)

 theorem sampleArrivals_length (encode : E → Arrival L R C) (ω : Fin T → E) :
    (sampleArrivals encode ω).length = T := by simp [sampleArrivals]

def residualTime (α : C → ℕ) (encode : E → Arrival L R C) (ω : Fin T → E) (t : Fin T) : Prop :=
  ∃ ev ∈ trace α (sampleArrivals encode ω), ev.time = t.val ∧ ev.threshold = false

 theorem sample_event_arrival (α : C → ℕ) (encode : E → Arrival L R C) (ω : Fin T → E)
    (ev : Event L R C) (hev : ev ∈ trace α (sampleArrivals encode ω))
    (t : Fin T) (ht : ev.time = t.val) : ev.arrival = encode (ω t) := by
  obtain ⟨i,hi,ha⟩ := trace_mem_arrival α (sampleArrivals encode ω) ev hev
  have hval : i.val = t.val := hi.symm.trans ht
  simpa only [sampleArrivals, List.get_eq_getElem, List.getElem_ofFn, hval] using ha

noncomputable def fixedResidualEvent (α : C → ℕ) (encode : E → Arrival L R C)
    (T m : ℕ) (tree : Fin m → E) : Finset (Fin T → E) := by
  classical
  exact univ.filter fun ω => ∃ τ : Fin m → Fin T, Function.Injective τ ∧
    ∀ i, ω (τ i) = tree i ∧ residualTime α encode ω (τ i)

def sourceBucket (encode : E → Arrival L R C) (u : L) (c : C) : Finset E :=
  univ.filter fun e => (encode e).left = u ∧ (encode e).cls = c

/-- For distinct fixed edge labels, occurrence of every label in the residual
process is equivalent to the injectively time-labelled event definition. -/
 theorem mem_fixedResidualEvent_iff (α : C → ℕ) (encode : E → Arrival L R C)
    (tree : Fin m → E) (htree : Function.Injective tree) (ω : Fin T → E) :
    ω ∈ fixedResidualEvent α encode T m tree ↔
      ∀ i, ∃ t : Fin T, ω t = tree i ∧ residualTime α encode ω t := by
  classical
  simp only [fixedResidualEvent, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨τ,hτ,hh⟩ i
    exact ⟨τ i,hh i⟩
  · intro hh
    choose τ hτ using hh
    refine ⟨τ,?_,hτ⟩
    intro i j hij
    apply htree
    exact (hτ i).1.symm.trans ((congrArg ω hij).trans (hτ j).1)

/-- Every fixed residual-edge event forces the exact witnesses counted in the
joint probability bound. There is one representative residual edge per bucket. -/
 theorem fixedResidualEvent_subset_witness (α : C → ℕ) (encode : E → Arrival L R C)
    (tree : Fin m → E) (vertex : J → L) (cls : J → C) (representative : J → Fin m)
    (hrepresentative : ∀ j, (encode (tree (representative j))).left = vertex j ∧
      (encode (tree (representative j))).cls = cls j)
    (hdistinct : Function.Injective (fun j => (vertex j,cls j))) :
    fixedResidualEvent α encode T m tree ⊆
      GraphChoices.patternWitnessEvent T m (fun j => α (cls j)) tree
        (fun j => sourceBucket encode (vertex j) (cls j)) := by
  classical
  intro ω hω
  obtain ⟨τ,hτ,hocc⟩ := (mem_filter.mp hω).2
  let es := sampleArrivals encode ω
  have hlen : es.length = T := sampleArrivals_length encode ω
  let K (j : J) := finiteThresholdTimes α es T hlen (vertex j) (cls j)
  apply GraphChoices.mem_patternWitnessEvent_of_times ω tree
    (fun j => sourceBucket encode (vertex j) (cls j)) τ K
  · intro j
    rw [finiteThresholdTimes_card]
    obtain ⟨ev,hev,htime,hr⟩ := (hocc (representative j)).2
    have ha : ev.arrival = encode (tree (representative j)) :=
      (sample_event_arrival α encode ω ev hev _ htime).trans (congrArg encode (hocc _).1)
    have hs := residual_event_final_saturated α es ev hev hr
    simpa [ha, (hrepresentative j).1, (hrepresentative j).2] using hs
  · exact hτ
  · exact fun i => (hocc i).1
  · intro i j ht
    obtain ⟨ev,hev,htime,hth,_,_⟩ := thresholdWitnessTimes_spec α es (vertex j) (cls j) (τ i).val
      ((mem_finiteThresholdTimes α es T hlen _ _ _).mp ht)
    obtain ⟨ev',hev',htime',hr⟩ := (hocc i).2
    have heq := trace_event_eq_of_time α es ev ev' hev hev' (htime.trans htime'.symm)
    have : true = false := hth.symm.trans ((congrArg Event.threshold heq).trans hr)
    cases this
  · intro j j' hj
    exact finiteThresholdTimes_buckets_disjoint α es T hlen _ _ _ _ (fun h => hj (hdistinct h))
  · intro j t ht
    obtain ⟨ev,hev,htime,_,hu,hc⟩ := thresholdWitnessTimes_spec α es (vertex j) (cls j) t.val
      ((mem_finiteThresholdTimes α es T hlen _ _ _).mp ht)
    have ha := sample_event_arrival α encode ω ev hev t htime
    simp only [sourceBucket, mem_filter, mem_univ, true_and]
    exact ⟨(congrArg Arrival.left ha).symm.trans hu,(congrArg Arrival.cls ha).symm.trans hc⟩

/-- The raw exponential fixed-tree probability bound (Equation (12)), now
proved for the actual residual execution. -/
 theorem fixedResidual_probability_le (α : C → ℕ) (encode : E → Arrival L R C)
    (tree : Fin m → E) (vertex : J → L) (cls : J → C) (representative : J → Fin m)
    (hrepresentative : ∀ j, (encode (tree (representative j))).left = vertex j ∧
      (encode (tree (representative j))).cls = cls j)
    (hdistinct : Function.Injective (fun j => (vertex j,cls j))) :
    GraphChoices.eventProbability (fixedResidualEvent α encode T m tree) ≤
      ((T:ℝ) / Fintype.card E)^m *
        ∏ j, (Real.exp 1 * T * ((sourceBucket encode (vertex j) (cls j)).card : ℝ) /
          Fintype.card E / α (cls j))^(α (cls j)) := by
  have hs := GraphChoices.eventProbability_mono
    (fixedResidualEvent_subset_witness (T := T) α encode tree vertex cls representative hrepresentative hdistinct)
  have hp := GraphChoices.patternWitness_probability_le_exp T m (fun j => α (cls j)) tree
    (fun j => sourceBucket encode (vertex j) (cls j))
  apply hs.trans
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hp

end GraphChoices.ThresholdGreedy
