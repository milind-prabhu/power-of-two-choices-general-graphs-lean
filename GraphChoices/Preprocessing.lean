import GraphChoices.Bipartite
import GraphChoices.Uniform
import GraphChoices.Density

/-! The expected-competitive part of Lemma 2.4 and the bounded-left-degree
orientation used by the preprocessing. Edge labels are preserved by the split,
so the two product sampling spaces are literally the same. -/
namespace GraphChoices
open Finset
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Nonempty E] {T : ℕ}

def BaseGraph.split (G : BaseGraph V E) (b : E → Bool) : BaseGraph (V ⊕ V) E where
  left e := Sum.inl (if b e then G.left e else G.right e)
  right e := Sum.inr (if b e then G.right e else G.left e)

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Nonempty E] in
 theorem split_sample (G : BaseGraph V E) (b : E → Bool) (ω : Fin T → E) :
    (G.split b).sample ω = splitInstance (G.sample ω) (fun t => b (ω t)) := by
  apply Instance.ext <;> funext t
  · rfl
  · cases h : b (ω t) <;>
      simp [BaseGraph.split, BaseGraph.sample, splitInstance, destination, flip, h]

omit [DecidableEq E] [Nonempty E] in
 theorem split_expectedOpt_le (G : BaseGraph V E) (b : E → Bool) (T : ℕ) :
    expectedOpt (G.split b) T ≤ expectedOpt G T := by
  apply average_mono
  intro ω
  rw [split_sample]
  exact_mod_cast split_opt_le (G.sample ω) (fun t => b (ω t))

omit [DecidableEq E] [Nonempty E] in
 theorem expectedOpt_le_two_split (G : BaseGraph V E) (b : E → Bool) (T : ℕ) :
    expectedOpt G T ≤ 2 * expectedOpt (G.split b) T := by
  unfold expectedOpt
  rw [← average_mul]
  apply average_mono
  intro ω
  rw [split_sample]
  exact_mod_cast opt_le_two_split_opt (G.sample ω) (fun t => b (ω t))

/-- Expected maximum load of a policy. This definition also permits policies
that see the future; applications must separately establish nonanticipation. -/
noncomputable def expectedCost (G : BaseGraph V E) (a : (Fin T → E) → Orientation T) : ℝ :=
  average (fun ω => (maxLoad (G.sample ω) (a ω) : ℝ))

 theorem expected_competitive_transfer (G : BaseGraph V E) (b : E → Bool)
    (a : (Fin T → E) → Orientation T) (c : ℝ) (hc : 0 ≤ c)
    (hcost : expectedCost (G.split b) a ≤ c * expectedOpt (G.split b) T) :
    expectedCost G (fun ω => transport (fun t => b (ω t)) (a ω)) ≤
      (2*c) * expectedOpt G T := by
  have hcollapse : expectedCost G (fun ω => transport (fun t => b (ω t)) (a ω)) ≤
      2 * expectedCost (G.split b) a := by
    unfold expectedCost
    rw [← average_mul]
    apply average_mono
    intro ω
    rw [split_sample]
    exact_mod_cast collapse_maxLoad_le (G.sample ω) (fun t => b (ω t)) (a ω)
  calc
    _ ≤ 2 * expectedCost (G.split b) a := hcollapse
    _ ≤ 2 * (c * expectedOpt (G.split b) T) := mul_le_mul_of_nonneg_left hcost (by norm_num)
    _ ≤ 2 * (c * expectedOpt G T) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (split_expectedOpt_le G b T) hc) (by norm_num)
    _ = _ := by ring

/-- An actual reference orientation with maximum left degree ceil(rho*).
The index set here is an arbitrary finite sequence of base-edge occurrences. -/
 theorem exists_left_degree_bounded_split (I : Instance V T) :
    ∃ b : Orientation T, ∀ u : V,
      (univ.filter fun t => (splitInstance I b).left t = Sum.inl u).card ≤ ⌈maxDensity I⌉₊ := by
  obtain ⟨b, hb⟩ := exists_exact_opt I
  refine ⟨b, ?_⟩
  intro u
  have h := load_le_maxLoad I b u
  rw [hb, opt_eq_ceil_maxDensity] at h
  simpa [splitInstance, load] using h

end GraphChoices
