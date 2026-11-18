import GraphChoices.DecomposedAlgorithm

/-! Expected density lower bounds, maximized over all concrete vertex sets,
including the rounding cost of an integer reference capacity. These are
statements about the full source sampling model, not a presumed benchmark.
-/
namespace GraphChoices
open Finset
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def BaseGraph.baseDensity (G : BaseGraph V E) (S : Finset V) : ℝ :=
  (G.internalEdges S).card/(S.card : ℝ)

noncomputable def BaseGraph.maxBaseDensity (G : BaseGraph V E) : ℝ :=
  (univ.powerset).sup' (by simp) (G.baseDensity)

noncomputable def BaseGraph.referenceCap (G : BaseGraph V E) : ℕ := ⌈G.maxBaseDensity⌉₊

theorem expectedOpt_nonneg (G : BaseGraph V E) (T : ℕ) : 0 ≤ expectedOpt G T := by
  unfold expectedOpt average
  positivity

theorem BaseGraph.baseDensity_nonneg (G : BaseGraph V E) (S : Finset V) : 0 ≤ G.baseDensity S := by
  unfold BaseGraph.baseDensity
  positivity

theorem BaseGraph.maxBaseDensity_nonneg (G : BaseGraph V E) : 0 ≤ G.maxBaseDensity :=
  (G.baseDensity_nonneg ∅).trans (le_sup' G.baseDensity (by simp))

theorem expected_density_ratio (G : BaseGraph V E) (S : Finset V) (T : ℕ) :
    G.baseDensity S*((T:ℝ)/Fintype.card E) ≤ expectedOpt G T := by
  by_cases hz : S.card = 0
  · simp only [BaseGraph.baseDensity, hz, Nat.cast_zero, div_zero, zero_mul]
    exact expectedOpt_nonneg G T
  have hS : (0:ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hz
  calc
    _ = ((T:ℝ)*(G.internalEdges S).card/Fintype.card E)/(S.card : ℝ) := by
      unfold BaseGraph.baseDensity
      ring
    _ ≤ ((S.card : ℝ)*expectedOpt G T)/(S.card : ℝ) :=
      div_le_div_of_nonneg_right (expected_density_lower_bound G S T) hS.le
    _ = _ := by field_simp

theorem expected_max_density_lower_bound (G : BaseGraph V E) (T : ℕ) :
    G.maxBaseDensity*((T:ℝ)/Fintype.card E) ≤ expectedOpt G T := by
  by_cases hT : T = 0
  · simpa only [hT, Nat.cast_zero, zero_div, mul_zero] using expectedOpt_nonneg G 0
  have hz : (0:ℝ) < (T:ℝ)/Fintype.card E := by
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hT) (by exact_mod_cast Fintype.card_pos)
  apply (le_div_iff₀ hz).mp
  apply (Finset.sup'_le_iff _ _).mpr
  intro S _
  exact (le_div_iff₀ hz).mpr (expected_density_ratio G S T)

/-- The expected count of a fixed source-edge label is at most twice the
expected optimum. Its endpoint pair has at most two vertices, including loops. -/
theorem expected_edge_rate_le_two_opt (G : BaseGraph V E) (T : ℕ) :
    (T:ℝ)/Fintype.card E ≤ 2*expectedOpt G T := by
  classical
  let e : E := Classical.choice (inferInstance : Nonempty E)
  let S : Finset V := {G.left e, G.right e}
  have he : e ∈ G.internalEdges S := by simp [BaseGraph.internalEdges, S]
  have hcount : 1 ≤ (G.internalEdges S).card := card_pos.mpr ⟨e,he⟩
  have hcount' : (1:ℝ) ≤ (G.internalEdges S).card := by exact_mod_cast hcount
  have hs : S.card ≤ 2 := (card_insert_le _ _).trans (by simp)
  calc
    _ ≤ (T:ℝ)*(G.internalEdges S).card/Fintype.card E := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hcount' (Nat.cast_nonneg T)
    _ ≤ (S.card : ℝ)*expectedOpt G T := expected_density_lower_bound G S T
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (expectedOpt_nonneg G T)

/-- The integer ceiling in the reference capacity costs at most another two
expected optimum units; it is not silently dropped from the density identity. -/
theorem expected_reference_cap_bound (G : BaseGraph V E) (T : ℕ) :
    (G.referenceCap : ℝ)*((T:ℝ)/Fintype.card E) ≤ 3*expectedOpt G T := by
  have hc : (G.referenceCap : ℝ) ≤ G.maxBaseDensity+1 := (Nat.ceil_lt_add_one G.maxBaseDensity_nonneg).le
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ (T:ℝ)/Fintype.card E by positivity)
  have hd := expected_max_density_lower_bound G T
  have he := expected_edge_rate_le_two_opt G T
  nlinarith

theorem BaseGraph.referenceCap_le_edges (G : BaseGraph V E) : G.referenceCap ≤ Fintype.card E := by
  apply Nat.ceil_le.mpr
  apply (Finset.sup'_le_iff _ _).mpr
  intro S _
  by_cases hS : S.card = 0
  · simp [BaseGraph.baseDensity, hS]
  have hp : (0:ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hone : (1:ℝ) ≤ S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
  have he : ((G.internalEdges S).card : ℝ) ≤ Fintype.card E := by exact_mod_cast card_le_card (subset_univ _)
  change ((G.internalEdges S).card : ℝ)/(S.card : ℝ) ≤ Fintype.card E
  apply (div_le_iff₀ hp).mpr
  have hE0 : (0:ℝ) ≤ Fintype.card E := Nat.cast_nonneg _
  nlinarith

theorem BaseGraph.total_edges_le_card_mul_referenceCap (G : BaseGraph V E) :
    (Fintype.card E : ℝ) ≤ (Fintype.card V : ℝ)*G.referenceCap := by
  classical
  have hV : Nonempty V := ⟨G.left (Classical.choice (inferInstance : Nonempty E))⟩
  have hp : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.mpr hV
  have hd : G.baseDensity univ ≤ G.maxBaseDensity := le_sup' G.baseDensity (by simp)
  have hc : G.maxBaseDensity ≤ (G.referenceCap : ℝ) := Nat.le_ceil _
  have heq : G.baseDensity univ = (Fintype.card E : ℝ)/Fintype.card V := by
    simp [BaseGraph.baseDensity, BaseGraph.internalEdges]
  rw [heq] at hd
  have hh := (div_le_iff₀ hp).mp (hd.trans hc)
  simpa only [mul_comm] using hh

end GraphChoices
