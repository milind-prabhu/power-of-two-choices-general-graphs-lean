import GraphChoices.OriginalGraphPreprocessing
import GraphChoices.BipartiteAllHorizons

/-! Theorem 1.1: a deterministic nonanticipating O(log log n)-competitive
policy for every nonempty simple base graph and every arrival horizon. -/
namespace GraphChoices
open Finset
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Nonempty E]

theorem exists_competitive_policy (G : BaseGraph V E) (hsimple : G.IsSimple) (T : ℕ) :
    ∃ p : OnlinePolicy E, expectedCost G (onlineOrientation (T := T) p) ≤
      120000*loglogFactor (Fintype.card V)*expectedOpt G T := by
  classical
  let x : E := Classical.choice (inferInstance : Nonempty E)
  have hV : 2 ≤ Fintype.card V := by
    have hh := card_le_univ ({G.left x, G.right x}:Finset V)
    simpa [hsimple.1 x] using hh
  obtain ⟨b,hD⟩ := exists_preprocessed_split G hsimple
  let H := splitGraph G b
  let e := splitEdgeEquiv G hsimple b
  letI : Nonempty H := ⟨e x⟩
  have hvertices : Fintype.card (V ⊕ V) ≤ 2*Fintype.card V := by simp only [Fintype.card_sum]; omega
  obtain ⟨p,hp⟩ := Peeling.exists_bipartite_policy_all_horizons H (2*Fintype.card V) T hvertices hD
  let q := pullbackPolicy e p
  have hq : expectedCost (G.split b) (onlineOrientation (T := T) q) ≤
      (30000*loglogFactor (2*Fintype.card V))*expectedOpt (G.split b) T := by
    rw [relabel_expectedCost (G.split b) (Peeling.graphBase H) e
      (splitEdgeEquiv_left G hsimple b) (splitEdgeEquiv_right G hsimple b) T p,
      relabel_expectedOpt (G.split b) (Peeling.graphBase H) e
        (splitEdgeEquiv_left G hsimple b) (splitEdgeEquiv_right G hsimple b) T]
    exact hp
  have hfactor := loglogFactor_ge_one (2*Fintype.card V)
  have hc : 0 ≤ 30000*loglogFactor (2*Fintype.card V) := by positivity
  refine ⟨collapsePolicy b q, (online_expected_transfer G b q _ hc hq).trans ?_⟩
  have hlog := loglogFactor_square_bound (Fintype.card V) (2*Fintype.card V) hV (by nlinarith)
  have ho := expectedOpt_nonneg G T
  have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ 60000*expectedOpt G T by positivity)
  nlinarith

/-- The exact proposition stated in Targets.lean, now proved. -/
theorem mainTheorem : MainTheorem := by
  refine ⟨120000, by norm_num, ?_⟩
  intro n m G hsimple T
  simpa only [Fintype.card_fin] using exists_competitive_policy G hsimple T

end GraphChoices
