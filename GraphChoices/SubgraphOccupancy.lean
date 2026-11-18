import GraphChoices.SampleRestriction

/-! A fully probabilistic lower bound for every concrete skewness witness.
Its hypotheses concern only the base subgraph's degrees and cardinalities. -/
namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def subgraphBucket (G F : Graph L R) (u : L) : Finset G :=
  univ.filter fun e => e.val ∈ F ∧ e.val.1 = u

theorem subgraphBucket_degree_lower {G F : Graph L R} (hF : F ⊆ G) (u : L) :
    leftDegree F u ≤ (subgraphBucket G F u).card := by
  classical
  have hedge (v : leftNeighbors F u) : (u,v.val) ∈ F := by
    simpa only [leftNeighbors, mem_filter, mem_univ, true_and] using v.property
  let f : leftNeighbors F u → subgraphBucket G F u := fun v =>
    ⟨⟨(u,v.val), hF (hedge v)⟩, mem_filter.mpr ⟨mem_univ _, hedge v, rfl⟩⟩
  have hf : Function.Injective f := by
    intro v w h
    exact Subtype.ext (congrArg (fun x => x.val.val.2) h)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, leftDegree] using hh

theorem subgraphBucket_source (G F : Graph L R) (A : Finset L) :
    ∀ u ∈ A, ∀ e ∈ subgraphBucket G F u,
      e.val.1 = u ∧ e.val.2 ∈ neighborSet F A := by
  intro u hu e he
  have hs := (mem_filter.mp he).2
  refine ⟨hs.2, ?_⟩
  simp only [neighborSet, GraphChoices.neighbors, mem_filter, mem_univ, true_and]
  exact ⟨u, hu, by simpa only [← hs.2] using hs.1⟩

/-- If the block-hit lower bound predicts at least |B| successful left
vertices, the actual sampled optimum is at least k/3 in expectation. -/
theorem expectedOpt_subgraph_blocks (G F : Graph L R) [Nonempty G]
    (hF : F ⊆ G) (A : Finset L) (hB : (neighborSet F A).Nonempty)
    (k s : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hmean : x ≤ (s:ℝ)*((minLeftDegree F A : ℝ)/G.card))
    (hpop : ((neighborSet F A).card : ℝ) ≤ (A.card:ℝ)*(x/2)^k) :
    (k:ℝ)/3 ≤ expectedOpt (graphBase G) (k*s) := by
  have hprob (u : A) : (x/2)^k ≤ eventProbability (allBlocksEvent (subgraphBucket G F u.val) k s) := by
    rw [allBlocks_probability]
    apply pow_le_pow_left₀ (by positivity)
    apply blockHit_probability_lower_of_mean _ _ x hx hx1
    apply hmean.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s)
    rw [Fintype.card_coe]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg G.card)
    exact_mod_cast (minLeftDegree_le F u.property).trans (subgraphBucket_degree_lower hF u.val)
  have hh := expectedOpt_block_lower (fun e : G => e.val.1) (fun e : G => e.val.2)
    A (neighborSet F A) (subgraphBucket G F) (subgraphBucket_source G F A) k s hB
    (hpop.trans (by simpa only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] using
      (sum_le_sum fun u (_ : u ∈ (univ : Finset A)) => hprob u)))
  exact hh

end GraphChoices.Peeling
