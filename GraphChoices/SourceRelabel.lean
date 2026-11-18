import GraphChoices.ShortHorizonGreedy

/-! Changing edge-label names preserves both sampling and nonanticipating
policies. A once-per-base-edge instance identifies the rounded density cap. -/
namespace GraphChoices
open Finset
variable {V E F : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F] [Nonempty E] [Nonempty F]

theorem relabel_sample (G : BaseGraph V E) (H : BaseGraph V F) (e : E ≃ F)
    (hl : ∀ x, H.left (e x) = G.left x) (hr : ∀ x, H.right (e x) = G.right x)
    {T : ℕ} (ω : Fin T → E) : H.sample (fun t => e (ω t)) = G.sample ω := by
  apply Instance.ext <;> funext t
  · exact hl (ω t)
  · exact hr (ω t)

theorem relabel_expectedOpt (G : BaseGraph V E) (H : BaseGraph V F) (e : E ≃ F)
    (hl : ∀ x, H.left (e x) = G.left x) (hr : ∀ x, H.right (e x) = G.right x) (T : ℕ) :
    expectedOpt G T = expectedOpt H T := by
  unfold expectedOpt
  rw [← average_equiv (Equiv.arrowCongr (Equiv.refl (Fin T)) e)]
  congr 1
  funext ω
  congr 1
  change opt (G.sample ω) = opt (H.sample (fun t => e (ω t)))
  rw [relabel_sample G H e hl hr ω]

def pullbackPolicy (e : E ≃ F) (p : OnlinePolicy F) : OnlinePolicy E :=
  fun history x => p (history.map e) (e x)

theorem pullback_orientation (e : E ≃ F) (p : OnlinePolicy F) {T : ℕ} (ω : Fin T → E) :
    onlineOrientation (pullbackPolicy e p) ω = onlineOrientation p (fun t => e (ω t)) := by
  funext t
  simp only [onlineOrientation, pullbackPolicy, List.map_take, List.map_ofFn, Function.comp_def]

theorem relabel_expectedCost (G : BaseGraph V E) (H : BaseGraph V F) (e : E ≃ F)
    (hl : ∀ x, H.left (e x) = G.left x) (hr : ∀ x, H.right (e x) = G.right x)
    (T : ℕ) (p : OnlinePolicy F) :
    expectedCost G (onlineOrientation (T := T) (pullbackPolicy e p)) =
      expectedCost H (onlineOrientation (T := T) p) := by
  unfold expectedCost
  rw [← average_equiv (Equiv.arrowCongr (Equiv.refl (Fin T)) e)]
  congr 1
  funext ω
  rw [pullback_orientation]
  congr 1
  change maxLoad (G.sample ω) (onlineOrientation p (fun t => e (ω t))) =
    maxLoad (H.sample (fun t => e (ω t))) (onlineOrientation p (fun t => e (ω t)))
  rw [relabel_sample G H e hl hr ω]

theorem relabel_referenceCap (G : BaseGraph V E) (H : BaseGraph V F) (e : E ≃ F)
    (hl : ∀ x, H.left (e x) = G.left x) (hr : ∀ x, H.right (e x) = G.right x) :
    G.referenceCap = H.referenceCap := by
  have hcount (S : Finset V) : (G.internalEdges S).card = (H.internalEdges S).card := by
    apply card_equiv e
    intro x
    simp only [BaseGraph.internalEdges, mem_filter, mem_univ, true_and, hl, hr]
  have hd : G.maxBaseDensity = H.maxBaseDensity := by
    unfold BaseGraph.maxBaseDensity
    apply sup'_congr _ rfl
    intro S _
    simp only [BaseGraph.baseDensity, hcount]
  simp only [BaseGraph.referenceCap, hd]

noncomputable def sourceInstance (G : BaseGraph V E) : Instance V (Fintype.card E) :=
  G.sample (Fintype.equivFin E).symm

theorem sourceInstance_internalCount (G : BaseGraph V E) (S : Finset V) :
    internalCount (sourceInstance G) S = (G.internalEdges S).card := by
  apply card_equiv (Fintype.equivFin E).symm
  intro t
  simp only [mem_filter, mem_univ, true_and, sourceInstance, BaseGraph.sample, BaseGraph.internalEdges]

theorem sourceInstance_opt (G : BaseGraph V E) : opt (sourceInstance G) = G.referenceCap := by
  rw [opt_eq_ceil_maxDensity]
  have hd : maxDensity (sourceInstance G) = G.maxBaseDensity := by
    unfold maxDensity BaseGraph.maxBaseDensity
    apply sup'_congr _ rfl
    intro S _
    simp only [density, BaseGraph.baseDensity, sourceInstance_internalCount]
  rw [hd]
  rfl

theorem sourceInstance_split (G : BaseGraph V E) (b : E → Bool) :
    sourceInstance (G.split b) = splitInstance (sourceInstance G)
      (fun t => b ((Fintype.equivFin E).symm t)) := split_sample G b _

theorem source_split_reference (G : BaseGraph V E) (b : E → Bool) :
    G.referenceCap ≤ 2*(G.split b).referenceCap := by
  rw [← sourceInstance_opt G, ← sourceInstance_opt (G.split b), sourceInstance_split]
  exact opt_le_two_split_opt _ _

theorem exists_reference_source_orientation (G : BaseGraph V E) :
    ∃ b : E → Bool, ∀ v,
      (univ.filter fun x => (if b x then G.left x else G.right x) = v).card ≤ G.referenceCap := by
  obtain ⟨a,ha⟩ := exists_exact_opt (sourceInstance G)
  let b := fun x : E => a (Fintype.equivFin E x)
  refine ⟨b, fun v => ?_⟩
  have hc : (univ.filter fun x : E => (if b x then G.left x else G.right x) = v).card =
      load (sourceInstance G) a v := by
    apply card_equiv (Fintype.equivFin E)
    intro x
    simp only [mem_filter, mem_univ, true_and, destination, load, sourceInstance,
      BaseGraph.sample, b, Equiv.symm_apply_apply]
  rw [hc]
  have hh := load_le_maxLoad (sourceInstance G) a v
  rw [ha, sourceInstance_opt] at hh
  exact hh

end GraphChoices
