import GraphChoices.GreedyBatchPropagation

namespace GraphChoices.LowerBound
open Finset

noncomputable def badBatches (b t m s : ℕ) : Finset (Fin b → Fin s → Edges b t m × Bool) := by
  classical
  exact univ.filter fun ω => ¬ allBatchesGood b t m s ω

theorem badBatches_probability (b t m s : ℕ) [Nonempty (Edges b t m)] :
    eventProbability (badBatches b t m s) ≤
      (b:ℝ)*(Fintype.card (Blocks b t):ℝ)*m*
        Real.exp ((b:ℝ)*Real.log 2-(s:ℝ)*(t*m)/(4*(Fintype.card (Edges b t m):ℝ))) := by
  classical
  let events := fun p : Fin b × (Blocks b t × Fin m) =>
    univ.filter fun ω : Fin b → Fin s → Edges b t m × Bool =>
      hitCount (markedBucket p.2.1 p.2.2) (ω p.1) < b
  have hsub : badBatches b t m s ⊆ univ.biUnion events := by
    intro ω hω
    have hh := (mem_filter.mp hω).2
    simp only [allBatchesGood, not_forall, not_le] at hh
    obtain ⟨i,c,a,h⟩ := hh
    exact mem_biUnion.mpr ⟨(i,c,a),mem_univ _,mem_filter.mpr ⟨mem_univ _,h⟩⟩
  have heach (p : Fin b × (Blocks b t × Fin m)) : eventProbability (events p) ≤
      Real.exp ((b:ℝ)*Real.log 2-(s:ℝ)*(t*m)/(4*(Fintype.card (Edges b t m):ℝ))) := by
    have hc := coordinate_event_probability
      (univ.filter fun η : Fin s → Edges b t m × Bool => hitCount (markedBucket p.2.1 p.2.2) η < b) p.1
    have heq : events p = univ.filter (fun ω : Fin b → Fin s → Edges b t m × Bool =>
      ω p.1 ∈ univ.filter fun η : Fin s → Edges b t m × Bool => hitCount (markedBucket p.2.1 p.2.2) η < b) := by
      ext ω
      simp [events]
    have hceq : eventProbability (events p) = eventProbability
        (univ.filter fun η : Fin s → Edges b t m × Bool => hitCount (markedBucket p.2.1 p.2.2) η < b) := by
      convert hc using 1
      congr 1
      ext ω
      simp [events]
    rw [hceq]
    apply (hitLowerTail_probability (markedBucket p.2.1 p.2.2) s b).trans_eq
    congr 1
    rw [markedBucket_card, Fintype.card_prod, Fintype.card_bool]
    push_cast
    ring
  apply (eventProbability_mono hsub).trans
  apply (witness_union_bound univ events).trans
  have hh := sum_le_sum (fun p (_ : p ∈ (univ : Finset (Fin b × (Blocks b t × Fin m)))) => heach p)
  simpa only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_assoc] using hh

theorem goodBatches_maxLoad (b t m s : ℕ) (hm : 0 < m)
    (ω : Fin b → Fin s → Edges b t m × Bool) (hgood : allBatchesGood b t m s ω) :
    b ≤ maxLoad ((RandomGreedy.coinGraph (graph b t m)).sample (blockFlatten b s ω))
      (onlineOrientation (RandomGreedy.policy (graph b t m)) (blockFlatten b s ω)) := by
  let v : Vertices b t m := ⟨0,(⟨0,by simp⟩,⟨0,hm⟩)⟩
  have hh := propagation b t m s ω hgood b le_rfl v (by simp [v])
  have heq := execution_final_load _ _ _
    (RandomGreedy.state_zero (graph b t m) (blockFlatten b s ω))
    (RandomGreedy.state_step (graph b t m) (blockFlatten b s ω)) v
  rw [heq] at hh
  exact hh.trans (load_le_maxLoad _ _ _)

theorem expectedGreedy_lower (b t m s : ℕ) [Nonempty (Edges b t m)] (hm : 0 < m) :
    (b:ℝ)*(1-(b:ℝ)*(Fintype.card (Blocks b t):ℝ)*m*
      Real.exp ((b:ℝ)*Real.log 2-(s:ℝ)*(t*m)/(4*(Fintype.card (Edges b t m):ℝ)))) ≤
      RandomGreedy.expectedLoad (graph b t m) (b*s) := by
  classical
  let good := univ \ badBatches b t m s
  have hpoint (ω : Fin b → Fin s → Edges b t m × Bool) :
      (b:ℝ)*(if ω ∈ good then (1:ℝ) else 0) ≤
        (maxLoad ((RandomGreedy.coinGraph (graph b t m)).sample (blockFlatten b s ω))
          (onlineOrientation (RandomGreedy.policy (graph b t m)) (blockFlatten b s ω)):ℝ) := by
    split_ifs with hω
    · rw [mul_one]
      have hh : allBatchesGood b t m s ω := by
        have h := (mem_sdiff.mp hω).2
        simpa only [badBatches, mem_filter, mem_univ, true_and, not_not] using h
      exact_mod_cast goodBatches_maxLoad b t m s hm ω hh
    · rw [mul_zero]
      positivity
  have hh := average_mono hpoint
  rw [average_mul, average_unit_indicator, eventProbability_compl,
    average_equiv (blockFlatten b s) (fun ω => (maxLoad ((RandomGreedy.coinGraph (graph b t m)).sample ω)
      (onlineOrientation (RandomGreedy.policy (graph b t m)) ω):ℝ))] at hh
  apply le_trans _ hh
  have hb := badBatches_probability b t m s
  have hbr : (0:ℝ) ≤ b := Nat.cast_nonneg _
  nlinarith

end GraphChoices.LowerBound
