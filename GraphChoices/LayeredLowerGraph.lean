import GraphChoices.BinomialLowerTail

namespace GraphChoices.LowerBound
open Finset

abbrev Vertices (b t m : ℕ) := (i : Fin (b+1)) × (Fin (t^i.val) × Fin m)
abbrev Blocks (b t : ℕ) := (i : Fin b) × Fin (t^i.val)
abbrev Edges (b t m : ℕ) := Blocks b t × (Fin m × Fin (t*m))

def leftVertex {b t m : ℕ} (p : Blocks b t × Fin m) : Vertices b t m :=
  ⟨p.1.1.castSucc,(p.1.2,p.2)⟩

def childGroup {t m i : ℕ} (g : Fin (t^i)) (r : Fin (t*m)) : Fin (t^(i+1)) :=
  Fin.cast (pow_succ t i).symm (finProdFinEquiv (g,(finProdFinEquiv.symm r).1))

def rightVertex {b t m : ℕ} (p : Blocks b t × Fin (t*m)) : Vertices b t m :=
  ⟨p.1.1.succ,(childGroup p.1.2 p.2,(finProdFinEquiv.symm p.2).2)⟩

def graph (b t m : ℕ) : BaseGraph (Vertices b t m) (Edges b t m) where
  left e := leftVertex (e.1,e.2.1)
  right e := rightVertex (e.1,e.2.2)

theorem leftVertex_injective (b t m : ℕ) : Function.Injective (@leftVertex b t m) := by
  rintro ⟨⟨i,g⟩,a⟩ ⟨⟨j,h⟩,a'⟩ he
  have hij : i = j := Fin.ext (congrArg (fun v => v.1.val) he)
  subst j
  have hp : (g,a) = (h,a') := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
  rfl

theorem rightVertex_injective (b t m : ℕ) : Function.Injective (@rightVertex b t m) := by
  rintro ⟨⟨i,g⟩,r⟩ ⟨⟨j,h⟩,s⟩ he
  have hij : i = j := by
    have hh := congrArg (fun v => v.1.val) he
    exact Fin.ext (by simpa only [rightVertex, Fin.val_succ] using Nat.succ.inj hh)
  subst j
  have hp : (childGroup g r,(finProdFinEquiv.symm r).2) =
      (childGroup h s,(finProdFinEquiv.symm s).2) := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have hc := Fin.cast_injective (pow_succ t i.val).symm (congrArg Prod.fst hp)
  have hpair := finProdFinEquiv.injective hc
  have hg : g = h := congrArg Prod.fst hpair
  have hr1 : (finProdFinEquiv.symm r).1 = (finProdFinEquiv.symm s).1 := congrArg (fun p : Fin (t^i.val) × Fin t => p.2) hpair
  have hr2 : (finProdFinEquiv.symm r).2 = (finProdFinEquiv.symm s).2 := congrArg (fun p : Fin (t^(i.val+1)) × Fin m => p.2) hp
  have hr : r = s := finProdFinEquiv.symm.injective (Prod.ext hr1 hr2)
  subst h
  subst s
  rfl

theorem graph_isSimple (b t m : ℕ) : (graph b t m).IsSimple := by
  constructor
  · intro e he
    have hh := congrArg (fun v => v.1.val) he
    change e.1.1.val = e.1.1.val+1 at hh
    omega
  · intro e f hef
    rcases hef with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · have hleft := leftVertex_injective b t m hl
      have hright := rightVertex_injective b t m hr
      have hc : e.1 = f.1 := congrArg (fun p : Blocks b t × Fin m => p.1) hleft
      have ha : e.2.1 = f.2.1 := congrArg (fun p : Blocks b t × Fin m => p.2) hleft
      have hr : e.2.2 = f.2.2 := congrArg (fun p : Blocks b t × Fin (t*m) => p.2) hright
      exact Prod.ext hc (Prod.ext ha hr)
    · have h1 := congrArg (fun v => v.1.val) hl
      have h2 := congrArg (fun v => v.1.val) hr
      change e.1.1.val = f.1.1.val+1 at h1
      change e.1.1.val+1 = f.1.1.val at h2
      omega

def layerSum (t b : ℕ) : ℕ := ∑ i ∈ range b, t^i

theorem card_blocks (b t : ℕ) : Fintype.card (Blocks b t) = layerSum t b := by
  simp only [Blocks, Fintype.card_sigma, Fintype.card_fin, layerSum, Fin.sum_univ_eq_sum_range]

theorem card_vertices (b t m : ℕ) : Fintype.card (Vertices b t m) = m*layerSum t (b+1) := by
  simp only [Vertices, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    ← sum_mul, Fin.sum_univ_eq_sum_range, layerSum]
  ring

theorem card_edges (b t m : ℕ) : Fintype.card (Edges b t m) = m^2*t*layerSum t b := by
  simp only [Edges, Fintype.card_prod, Fintype.card_fin, card_blocks]
  ring

theorem layerSum_succ (t b : ℕ) : layerSum t (b+1) = layerSum t b+t^b := sum_range_succ _ _

theorem layerSum_shift (t b : ℕ) : layerSum t (b+1) = 1+t*layerSum t b := by
  simp only [layerSum, sum_range_succ', pow_succ, ← sum_mul, pow_zero]
  ring

theorem layerSum_pos (t b : ℕ) (hb : 0 < b) : 0 < layerSum t b := by
  have hh : (1:ℕ) ≤ layerSum t b := by
    simpa only [pow_zero] using (single_le_sum (f := fun i => t^i) (fun _ _ => Nat.zero_le _) (mem_range.mpr hb))
  omega

theorem layerSum_upper (t b : ℕ) (ht : 1 ≤ t) : layerSum t (b+1) ≤ (b+1)*t^b := by
  apply le_trans (sum_le_card_nsmul _ _ (t^b) ?_) (by simp)
  intro i hi
  exact Nat.pow_le_pow_right (by omega) (by have := mem_range.mp hi; omega)

end GraphChoices.LowerBound
