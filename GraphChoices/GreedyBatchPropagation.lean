import GraphChoices.LayeredLowerGraph

namespace GraphChoices.RandomGreedy
open Finset
variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- A deterministic forcing lemma. Every marked arrival favors u when its
neighbor already has the preceding load level; unrelated arrivals help. -/
theorem batch_forces_load (G : BaseGraph V E) (k s : ℕ)
    (ω : Fin k → Fin s → E × Bool) (i : Fin k) (h : ℕ) (u : V)
    (A : Finset (Fin s)) (hcount : h+1 ≤ A.card)
    (hsource : ∀ j ∈ A, G.left (ω i j).1 = u ∧ (ω i j).2 = true ∧
      h ≤ state G (blockFlatten k s ω) (i.val*s) (G.right (ω i j).1)) :
    h+1 ≤ state G (blockFlatten k s ω) ((i.val+1)*s) u := by
  let τ := blockFlatten k s ω
  have hend : (i.val+1)*s ≤ k*s := Nat.mul_le_mul_right s (by omega)
  by_contra hbad
  have hu : state G τ ((i.val+1)*s) u ≤ h := by
    change ¬ h+1 ≤ state G τ ((i.val+1)*s) u at hbad
    omega
  have htime (j : Fin s) : (finProdFinEquiv (i,j)).val = i.val*s+j.val := by
    change j.val+s*i.val = i.val*s+j.val
    ring
  have hdest (j : Fin s) (hj : j ∈ A) :
      destination ((coinGraph G).sample τ) (onlineOrientation (policy G) τ) (finProdFinEquiv (i,j)) = u := by
    obtain ⟨hl,hcoin,hr⟩ := hsource j hj
    let t : Fin (k*s) := finProdFinEquiv (i,j)
    have ht : t.val < (i.val+1)*s := by dsimp only [t]; rw [htime]; nlinarith [j.isLt]
    have hstart : i.val*s ≤ t.val := by dsimp only [t]; rw [htime]; omega
    have hlcur : state G τ t.val u ≤ h :=
      (state_mono G τ ht.le hend u).trans hu
    have hrcur : h ≤ state G τ t.val (G.right (ω i j).1) :=
      hr.trans (state_mono G τ hstart (Nat.le_of_lt t.isLt) _)
    have hmark : τ t = ω i j := blockFlatten_apply k s ω i j
    change (if choice G (state G τ t.val) (τ t) then G.left (τ t).1 else G.right (τ t).1) = u
    rw [hmark]
    rw [choice_favours_left G _ _ hcoin (by rw [hl]; omega), if_pos rfl, hl]
  have hc : A.card ≤ prefixLoad ((coinGraph G).sample τ) (onlineOrientation (policy G) τ)
      ((i.val+1)*s) u := by
    apply card_le_card_of_injOn (fun j => finProdFinEquiv (i,j))
    · intro j hj
      change finProdFinEquiv (i,j) ∈ univ.filter (fun t => t.val < (i.val+1)*s ∧
        destination ((coinGraph G).sample τ) (onlineOrientation (policy G) τ) t = u)
      exact mem_filter.mpr ⟨mem_univ _,by rw [htime]; nlinarith [j.isLt],hdest j hj⟩
    · intro j _ j' _ he
      exact congrArg Prod.snd (finProdFinEquiv.injective he)
  rw [← state_eq_prefixLoad G τ _ hend] at hc
  omega

end GraphChoices.RandomGreedy

namespace GraphChoices.LowerBound
open Finset

def markedBucket {b t m : ℕ} (c : Blocks b t) (a : Fin m) : Finset (Edges b t m × Bool) :=
  (({c} : Finset (Blocks b t)) ×ˢ (({a} : Finset (Fin m)) ×ˢ univ)) ×ˢ {true}

theorem markedBucket_card {b t m : ℕ} (c : Blocks b t) (a : Fin m) :
    (markedBucket c a).card = t*m := by simp [markedBucket]

theorem markedBucket_source {b t m : ℕ} (c : Blocks b t) (a : Fin m)
    (x : Edges b t m × Bool) (hx : x ∈ markedBucket c a) :
    (graph b t m).left x.1 = leftVertex (c,a) ∧ x.2 = true ∧
      ((graph b t m).right x.1).1.val = c.1.val+1 := by
  simp only [markedBucket, mem_product, mem_singleton, mem_univ, and_true] at hx
  rcases x with ⟨⟨c',a',r⟩,coin⟩
  rcases hx with ⟨⟨rfl,rfl⟩,rfl⟩
  exact ⟨rfl,rfl,rfl⟩

def allBatchesGood (b t m s : ℕ) (ω : Fin b → Fin s → Edges b t m × Bool) : Prop :=
  ∀ i c a, b ≤ hitCount (markedBucket c a) (ω i)

theorem propagation (b t m s : ℕ) (ω : Fin b → Fin s → Edges b t m × Bool)
    (hgood : allBatchesGood b t m s ω) :
    ∀ i, i ≤ b → ∀ v : Vertices b t m, v.1.val = b-i →
      i ≤ RandomGreedy.state (graph b t m) (blockFlatten b s ω) (i*s) v := by
  intro i
  induction i with
  | zero => intro _ _ _; omega
  | succ i ih =>
    intro hib v hv
    have hib' : i < b := by omega
    let ci : Fin b := ⟨v.1.val,by omega⟩
    let c : Blocks b t := ⟨ci,v.2.1⟩
    have hleft : leftVertex (c,v.2.2) = v := by
      rcases v with ⟨j,g,a⟩
      rfl
    let A := univ.filter fun j : Fin s => ω ⟨i,hib'⟩ j ∈ markedBucket c v.2.2
    have hcount : i+1 ≤ A.card := (by omega : i+1 ≤ b).trans (hgood ⟨i,hib'⟩ c v.2.2)
    have hh := RandomGreedy.batch_forces_load (graph b t m) b s ω ⟨i,hib'⟩ i v A hcount
      (fun j hj => by
        have hs := markedBucket_source c v.2.2 _ ((mem_filter.mp hj).2)
        refine ⟨hs.1.trans hleft,hs.2.1,?_⟩
        exact ih (by omega) _ (by rw [hs.2.2]; dsimp only [c,ci]; omega))
    exact hh

end GraphChoices.LowerBound
