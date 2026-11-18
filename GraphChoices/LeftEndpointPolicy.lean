import GraphChoices.ExpectedMaxHits

namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def leftBucket (G : Graph L R) (u : L) : Finset G := univ.filter fun e => e.val.1 = u

theorem leftBucket_card (G : Graph L R) (u : L) : (leftBucket G u).card = leftDegree G u := by
  classical
  apply card_bij (fun e _ => e.val.2)
  · intro e he
    have hh := (mem_filter.mp he).2
    simp only [leftNeighbors, mem_filter, mem_univ, true_and]
    simpa only [← hh] using e.property
  · intro e he f hf h
    apply Subtype.ext
    exact Prod.ext (((mem_filter.mp he).2).trans ((mem_filter.mp hf).2).symm) h
  · intro v hv
    have hh : (u,v) ∈ G := (mem_filter.mp hv).2
    exact ⟨⟨(u,v),hh⟩, mem_filter.mpr ⟨mem_univ _,rfl⟩, rfl⟩

theorem allLeft_maxLoad (G : Graph L R) {T : ℕ} (ω : Fin T → G) :
    maxLoad ((graphBase G).sample ω) (fun _ => true) =
      univ.sup (fun u : L => hitCount (leftBucket G u) ω) := by
  have hl (u : L) : load ((graphBase G).sample ω) (fun _ => true) (Sum.inl u) =
      hitCount (leftBucket G u) ω := by simp [load, destination, graphBase, BaseGraph.sample, hitCount, leftBucket]
  have hr (v : R) : load ((graphBase G).sample ω) (fun _ => true) (Sum.inr v) = 0 := by
    simp [load, destination, graphBase, BaseGraph.sample]
  apply Nat.le_antisymm
  · apply (maxLoad_le_iff _ _ _).mpr
    intro v
    cases v with
    | inl u => rw [hl]; exact Finset.le_sup (f := fun u : L => hitCount (leftBucket G u) ω) (mem_univ u)
    | inr v => rw [hr]; omega
  · apply Finset.sup_le
    intro u _
    rw [← hl]
    exact load_le_maxLoad _ _ _

theorem allLeft_expectedCost (G : Graph L R) [Nonempty G] (T N : ℕ)
    (hvertices : Fintype.card (L ⊕ R) ≤ N) :
    expectedCost (graphBase G) (onlineOrientation (T := T) (fun _ _ => true)) ≤
      2*Real.log (N:ℝ)+2*(maxLeftDegree G:ℝ)*((T:ℝ)/G.card) := by
  classical
  let e : G := Classical.choice (inferInstance : Nonempty G)
  letI : Nonempty L := ⟨e.val.1⟩
  have hc : (0:ℝ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hLN : Fintype.card L ≤ N := by simp only [Fintype.card_sum] at hvertices; omega
  have hh := expected_max_hits (leftBucket G) T ((maxLeftDegree G:ℝ)*((T:ℝ)/G.card)) (fun u => by
    rw [leftBucket_card, Fintype.card_coe]
    have hd : (leftDegree G u:ℝ) ≤ maxLeftDegree G := by exact_mod_cast leftDegree_le_max G u
    have he := mul_le_mul_of_nonneg_right hd (show 0 ≤ (T:ℝ)/G.card by positivity)
    convert he using 1 <;> ring)
  have heq : expectedCost (graphBase G) (onlineOrientation (T := T) (fun _ _ => true)) =
      average (fun ω : Fin T → G => ((univ.sup fun u => hitCount (leftBucket G u) ω:ℕ):ℝ)) := by
    unfold expectedCost
    congr 1
    funext ω
    exact_mod_cast allLeft_maxLoad G ω
  rw [heq]
  have hlog := Real.log_le_log hc (show (Fintype.card L:ℝ) ≤ N by exact_mod_cast hLN)
  linarith

theorem allLeft_reference_bound (G : Graph L R) [Nonempty G] (T N : ℕ)
    (hvertices : Fintype.card (L ⊕ R) ≤ N)
    (hD : ∀ u, leftDegree G u ≤ 4*(graphBase G).referenceCap) :
    expectedCost (graphBase G) (onlineOrientation (T := T) (fun _ _ => true)) ≤
      24*expectedOpt (graphBase G) T+2*Real.log (N:ℝ) := by
  have hd : (maxLeftDegree G:ℝ) ≤ 4*(graphBase G).referenceCap := by
    exact_mod_cast maxLeftDegree_le G _ hD
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ (T:ℝ)/G.card by positivity)
  have hc := expected_reference_cap_bound (graphBase G) T
  rw [Fintype.card_coe] at hc
  apply (allLeft_expectedCost G T N hvertices).trans
  nlinarith

end GraphChoices.Peeling
