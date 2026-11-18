import GraphChoices.LayeredLowerGraph
import GraphChoices.LowerFamilyLogBounds

namespace GraphChoices.LowerBound
open Finset

def baseDegree {V E : Type*} [Fintype E] [DecidableEq V] (G : BaseGraph V E) (v : V) : ℕ :=
  (univ.filter fun e => G.left e = v ∨ G.right e = v).card

theorem block_degree_upper {V C : Type*} [Fintype C] [DecidableEq C] [DecidableEq V] {m r : ℕ}
    (left : C × Fin m → V) (right : C × Fin r → V)
    (hl : Function.Injective left) (hr : Function.Injective right) (v : V) :
    baseDegree (blockBase left right) v ≤ m+r := by
  have hL : (univ.filter fun e : C × (Fin m × Fin r) => left (e.1,e.2.1) = v).card ≤ r := by
    let A := univ.filter fun e : C × (Fin m × Fin r) => left (e.1,e.2.1) = v
    let f : A → Fin r := fun e => e.val.2.2
    have hf : Function.Injective f := by
      intro e f h
      have hh := hl (((mem_filter.mp e.property).2).trans ((mem_filter.mp f.property).2).symm)
      apply Subtype.ext
      exact Prod.ext (congrArg (fun p : C × Fin m => p.1) hh)
        (Prod.ext (congrArg (fun p : C × Fin m => p.2) hh) h)
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hR : (univ.filter fun e : C × (Fin m × Fin r) => right (e.1,e.2.2) = v).card ≤ m := by
    let A := univ.filter fun e : C × (Fin m × Fin r) => right (e.1,e.2.2) = v
    let f : A → Fin m := fun e => e.val.2.1
    have hf : Function.Injective f := by
      intro e f h
      have hh := hr (((mem_filter.mp e.property).2).trans ((mem_filter.mp f.property).2).symm)
      apply Subtype.ext
      exact Prod.ext (congrArg (fun p : C × Fin r => p.1) hh)
        (Prod.ext h (congrArg (fun p : C × Fin r => p.2) hh))
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have heq : (univ.filter fun e : C × (Fin m × Fin r) => left (e.1,e.2.1) = v ∨ right (e.1,e.2.2) = v) =
      (univ.filter fun e => left (e.1,e.2.1) = v) ∪ (univ.filter fun e => right (e.1,e.2.2) = v) := by ext e; simp
  unfold baseDegree
  change (univ.filter fun e : C × (Fin m × Fin r) => left (e.1,e.2.1) = v ∨ right (e.1,e.2.2) = v).card ≤ m+r
  rw [heq]
  exact (card_union_le _ _).trans (by omega)

theorem rightVertex_covers_positive (b t m : ℕ) (v : Vertices b t m) (hv : v.1 ≠ 0) :
    ∃ p : Blocks b t × Fin (t*m), rightVertex p = v := by
  rcases v with ⟨i,g,a⟩
  obtain ⟨j,rfl⟩ := Fin.eq_succ_of_ne_zero hv
  let p := finProdFinEquiv.symm (Fin.cast (pow_succ t j.val) g)
  refine ⟨(⟨j,p.1⟩,finProdFinEquiv (p.2,a)),?_⟩
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl,heq_of_eq ?_⟩
  simp only [rightVertex,childGroup,Equiv.symm_apply_apply,Prod.fst,Prod.snd]
  apply Prod.ext
  · change Fin.cast (pow_succ t j.val).symm (finProdFinEquiv p) = g
    change Fin.cast (pow_succ t j.val).symm
      (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast (pow_succ t j.val) g))) = g
    rw [Equiv.apply_symm_apply]
    exact Fin.ext rfl
  · rfl

theorem vertex_block_cover (b t m : ℕ) (hb : 0 < b) (v : Vertices b t m) :
    (∃ p : Blocks b t × Fin m, leftVertex p = v) ∨
      ∃ p : Blocks b t × Fin (t*m), rightVertex p = v := by
  by_cases hv : v.1.val < b
  · left
    exact ⟨(⟨⟨v.1.val,hv⟩,v.2.1⟩,v.2.2),rfl⟩
  · right
    apply rightVertex_covers_positive
    intro hz
    have hval := congrArg Fin.val hz
    simp only [Fin.val_zero] at hval
    omega

theorem graph_degree_lower (b t m : ℕ) (hb : 0 < b) (ht : 1 ≤ t) (v : Vertices b t m) :
    m ≤ baseDegree (graph b t m) v := by
  rcases vertex_block_cover b t m hb v with ⟨⟨c,a⟩,hv⟩ | ⟨⟨c,r⟩,hv⟩
  · have hh : t*m ≤ baseDegree (graph b t m) v := by
      let f : Fin (t*m) → {e : Edges b t m // (graph b t m).left e = v ∨ (graph b t m).right e = v} :=
        fun r => ⟨(c,a,r),Or.inl hv⟩
      have hf : Function.Injective f := by intro r s h; exact congrArg (fun e => e.val.2.2) h
      simpa only [Fintype.card_fin,Fintype.card_subtype,baseDegree] using Fintype.card_le_of_injective f hf
    exact (by nlinarith : m ≤ t*m).trans hh
  · let f : Fin m → {e : Edges b t m // (graph b t m).left e = v ∨ (graph b t m).right e = v} :=
      fun a => ⟨(c,a,r),Or.inr hv⟩
    have hf : Function.Injective f := by intro a a' h; exact congrArg (fun e => e.val.2.1) h
    simpa only [Fintype.card_fin,Fintype.card_subtype,baseDegree] using Fintype.card_le_of_injective f hf

/-- The literal degree interval in Theorem 1.2, with the actual vertex
count N rather than an auxiliary asymptotic size parameter. -/
theorem family_degree_range (b : ℕ) (hb : 16 ≤ b) (v : Vertices b (branching b) (width b)) :
    Real.sqrt (size b:ℝ) ≤ (baseDegree (graph b (branching b) (width b)) v:ℝ) ∧
      (baseDegree (graph b (branching b) (width b)) v:ℝ) ≤
        Real.sqrt (size b:ℝ)*(Real.log (size b:ℝ))^3 := by
  have hp := family_parameter_bounds b hb
  have hm : (0:ℝ) ≤ width b := Nat.cast_nonneg _
  have hN : (0:ℝ) ≤ size b := Nat.cast_nonneg _
  have hmin := graph_degree_lower b (branching b) (width b) (by omega) (by have := hp.1; omega) v
  have hmax := block_degree_upper (@leftVertex b (branching b) (width b)) (@rightVertex b (branching b) (width b))
    (leftVertex_injective _ _ _) (rightVertex_injective _ _ _) v
  have hminr : (width b:ℝ) ≤ baseDegree (graph b (branching b) (width b)) v := by exact_mod_cast hmin
  have hmaxr : (baseDegree (graph b (branching b) (width b)) v:ℝ) ≤ (width b:ℝ)*(branching b+1) := by
    have hh : baseDegree (graph b (branching b) (width b)) v ≤ width b+branching b*width b := hmax
    exact_mod_cast (by nlinarith : baseDegree (graph b (branching b) (width b)) v ≤ width b*(branching b+1))
  have hsqrt : Real.sqrt (size b:ℝ) ≤ width b := Real.sqrt_le_iff.mpr ⟨hm,by exact_mod_cast hp.2.2.2.2.2⟩
  have hS : (branching b)^b ≤ layerSum (branching b) (b+1) := by rw [layerSum_succ]; omega
  have hm2N : (width b:ℝ)^2 ≤ 2*(size b:ℝ) := by
    have hh := Nat.mul_le_mul_left (4*(branching b)^b) hS
    unfold width size at *
    exact_mod_cast (by nlinarith : (2*(branching b)^b)^2 ≤ 2*(2*(branching b)^b*layerSum (branching b) (b+1)))
  have hs0 := Real.sqrt_nonneg (size b:ℝ)
  have hs2 := Real.sq_sqrt hN
  have hmupper : (width b:ℝ) ≤ 2*Real.sqrt (size b:ℝ) := by nlinarith
  have hlog := family_log_large b hb
  have hpow := pow_le_pow_left₀ (show (0:ℝ) ≤ 30*(b:ℝ) by positivity) hlog 3
  have htdef : (branching b:ℝ) = 4096*(b:ℝ)^3 := by unfold branching; push_cast; ring
  have hb16 : (16:ℝ) ≤ b := by exact_mod_cast hb
  have hb3 : (1:ℝ) ≤ (b:ℝ)^3 := one_le_pow₀ (by linarith : (1:ℝ) ≤ b)
  have htlog : 2*((branching b:ℝ)+1) ≤ (Real.log (size b:ℝ))^3 := by rw [htdef]; nlinarith
  refine ⟨hsqrt.trans hminr,?_⟩
  have hh := mul_le_mul_of_nonneg_right hmupper (show 0 ≤ (branching b:ℝ)+1 by positivity)
  have hh' := mul_le_mul_of_nonneg_left htlog hs0
  push_cast at hmaxr
  nlinarith

end GraphChoices.LowerBound
