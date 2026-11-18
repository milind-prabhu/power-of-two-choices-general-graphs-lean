import GraphChoices.OccupancySecondMoment
import GraphChoices.PreparedDecomposition

/-! The block occupancy argument applied to actual sampled bipartite graphs.
Every successful left vertex supplies one distinct arrival per block, giving
a concrete dense vertex set. -/
namespace GraphChoices
open Finset

theorem average_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℝ) : average (fun ω => f (e ω)) = average f := by
  simp only [average, e.sum_comp, Fintype.card_congr e]

def blockFlatten {E : Type*} (k s : ℕ) : (Fin k → Fin s → E) ≃ (Fin (k*s) → E) :=
  (Equiv.curry (Fin k) (Fin s) E).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl E))

theorem blockFlatten_apply {E : Type*} (k s : ℕ) (ω : Fin k → Fin s → E)
    (i : Fin k) (j : Fin s) : blockFlatten k s ω (finProdFinEquiv (i,j)) = ω i j := by
  simp [blockFlatten, Equiv.arrowCongr]

variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
  [DecidableEq L] [DecidableEq R] [DecidableEq E] [Nonempty E]

def bipartiteBase (left : E → L) (right : E → R) : BaseGraph (L ⊕ R) E where
  left e := Sum.inl (left e)
  right e := Sum.inr (right e)

/-- No independence is used here: selected left vertices hit in every block
force at least k edges per selected vertex in the same sampled induced set. -/
theorem block_success_density (left : E → L) (right : E → R)
    (A : Finset L) (B : Finset R) (bucket : L → Finset E)
    (hsource : ∀ u ∈ A, ∀ e ∈ bucket u, left e = u ∧ right e ∈ B)
    (k s : ℕ) (ω : Fin k → Fin s → E) :
    let Z := successNumber (fun u : A => allBlocksEvent (bucket u.val) k s) ω
    (k:ℝ)*Z ≤ (Z+B.card)*(opt ((bipartiteBase left right).sample (blockFlatten k s ω)) : ℝ) := by
  classical
  let H : Finset L := A.filter fun u => ω ∈ allBlocksEvent (bucket u) k s
  let S : Finset (L ⊕ R) := H.map Function.Embedding.inl ∪ B.map Function.Embedding.inr
  let I := (bipartiteBase left right).sample (blockFlatten k s ω)
  have hsuccess (u : H) (i : Fin k) : ∃ j : Fin s, ω i j ∈ bucket u.val := by
    have hu := (mem_filter.mp u.property).2
    have hh := (Fintype.mem_piFinset.mp hu) i
    exact (mem_filter.mp hh).2
  let time (u : H) (i : Fin k) : Fin (k*s) :=
    finProdFinEquiv (i, Classical.choose (hsuccess u i))
  have htime (u : H) (i : Fin k) :
      I.left (time u i) ∈ S ∧ I.right (time u i) ∈ S := by
    have hb := Classical.choose_spec (hsuccess u i)
    have hs := hsource u.val (mem_filter.mp u.property).1 _ hb
    dsimp only [I, BaseGraph.sample, bipartiteBase, time]
    rw [blockFlatten_apply]
    constructor
    · apply mem_union_left
      exact mem_map.mpr ⟨u.val, u.property, by simp [hs.1]⟩
    · apply mem_union_right
      exact mem_map.mpr ⟨right (ω i (Classical.choose (hsuccess u i))), hs.2, rfl⟩
  let f : H × Fin k → {t : Fin (k*s) // I.left t ∈ S ∧ I.right t ∈ S} :=
    fun p => ⟨time p.1 p.2, htime p.1 p.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨u,i⟩ ⟨v,j⟩ h
    have he : time u i = time v j := congrArg Subtype.val h
    have hij := congrArg Prod.fst (finProdFinEquiv.injective he)
    have hs1 := hsource u.val (mem_filter.mp u.property).1 _ (Classical.choose_spec (hsuccess u i))
    have hs2 := hsource v.val (mem_filter.mp v.property).1 _ (Classical.choose_spec (hsuccess v j))
    have ht : ω i (Classical.choose (hsuccess u i)) = ω j (Classical.choose (hsuccess v j)) :=
      by simpa only [time, blockFlatten_apply] using congrArg (fun t => blockFlatten k s ω t) he
    have huv : u = v := Subtype.ext (by rw [← hs1.1, ht, hs2.1])
    exact Prod.ext huv hij
  have hedge : H.card*k ≤ internalCount I S := by
    have hh := Fintype.card_le_of_injective f hinj
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hh
    simpa only [Fintype.card_subtype, internalCount] using hh
  have hdisj : Disjoint (H.map Function.Embedding.inl) (B.map Function.Embedding.inr) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,_,hu⟩ := mem_map.mp hx
    obtain ⟨v,_,hv⟩ := mem_map.mp hy
    exact Sum.noConfusion (hu.trans hv.symm)
  have hScard : S.card = H.card+B.card := by simp [S, card_union_of_disjoint hdisj]
  have hZ : successNumber (fun u : A => allBlocksEvent (bucket u.val) k s) ω = H.card := by
    simp only [successNumber, H, card_filter]
    push_cast
    exact Finset.sum_coe_sort A (fun u => if ω ∈ allBlocksEvent (bucket u) k s then (1:ℝ) else 0)
  dsimp only
  rw [hZ]
  have hd := hedge.trans (density_le_opt I S)
  rw [hScard] at hd
  exact_mod_cast (by simpa only [Nat.mul_comm] using hd)

theorem expectedOpt_block_lower (left : E → L) (right : E → R)
    (A : Finset L) (B : Finset R) (bucket : L → Finset E)
    (hsource : ∀ u ∈ A, ∀ e ∈ bucket u, left e = u ∧ right e ∈ B)
    (k s : ℕ) (hB : B.Nonempty)
    (hmean : (B.card:ℝ) ≤ ∑ u : A, eventProbability (allBlocksEvent (bucket u.val) k s)) :
    (k:ℝ)/3 ≤ expectedOpt (bipartiteBase left right) (k*s) := by
  let events := fun u : A => allBlocksEvent (bucket u.val) k s
  have hcov : ∀ u v : A, u ≠ v → eventProbability (events u ∩ events v) ≤
      eventProbability (events u)*eventProbability (events v) := by
    intro u v huv
    apply allBlocks_disjoint_covariance
    apply disjoint_left.mpr
    intro e he hf
    apply huv
    exact Subtype.ext (((hsource u.val u.property e he).1).symm.trans (hsource v.val v.property e hf).1)
  have hh := expected_density_of_second_moment (successNumber events)
    (fun ω => (opt ((bipartiteBase left right).sample (blockFlatten k s ω)):ℝ))
    k B.card (successNumber_nonneg events) (Nat.cast_nonneg k)
    (by exact_mod_cast hB.card_pos) (by rwa [average_successNumber])
    (by rw [average_successNumber]; exact successNumber_second_moment events hcov)
    (block_success_density left right A B bucket hsource k s)
  rw [average_equiv (blockFlatten k s) (fun ω => (opt ((bipartiteBase left right).sample ω):ℝ))] at hh
  exact hh

end GraphChoices
