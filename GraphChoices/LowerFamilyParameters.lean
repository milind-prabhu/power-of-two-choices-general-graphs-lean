import GraphChoices.BlockDensityTailArithmetic

namespace GraphChoices.LowerBound
open Finset

def branching (b : ℕ) : ℕ := (16*b)^3
def width (b : ℕ) : ℕ := 2*(branching b)^b
def batchLength (b : ℕ) : ℕ := (width b/b)*layerSum (branching b) (b+1)
def size (b : ℕ) : ℕ := width b*layerSum (branching b) (b+1)
noncomputable def densityThreshold (t : ℕ) : ℕ := ⌈16*Real.log (t:ℝ)⌉₊+16

theorem size_eq_vertices (b : ℕ) : size b = Fintype.card (Vertices b (branching b) (width b)) := by
  rw [card_vertices]
  rfl

theorem size_eq_batches (b : ℕ) (hb : 0 < b) : size b = b*batchLength b := by
  have ht : b ∣ branching b := dvd_pow (Nat.dvd_mul_left b 16) (by decide : 3 ≠ 0)
  have hm : b ∣ width b := dvd_mul_of_dvd_right (dvd_pow ht (by omega : b ≠ 0)) 2
  unfold size batchLength
  rw [← mul_assoc,Nat.mul_div_cancel' hm]

theorem layerSum_geometric_upper (t b : ℕ) (ht : 2 ≤ t) : layerSum t (b+1) ≤ 2*t^b := by
  induction b with
  | zero => simp [layerSum]
  | succ b ih =>
    rw [layerSum_succ]
    have hp : t^(b+1) = t^b*t := pow_succ _ _
    nlinarith

theorem layerSum_le_width (b t : ℕ) (ht : 1 ≤ t) : layerSum t b ≤ b*t^b := by
  apply le_trans (sum_le_card_nsmul _ _ (t^b) ?_) (by simp)
  intro i hi
  exact Nat.pow_le_pow_right (by omega) (by have := mem_range.mp hi; omega)

theorem densityThreshold_scale (t : ℕ) (ht : 4 ≤ t) :
    16 ≤ densityThreshold t ∧
      Real.exp 1*(t:ℝ)*(2*Real.exp 1/(densityThreshold t:ℝ))^(densityThreshold t) ≤ 1/256 := by
  let k := densityThreshold t
  have hk : 16 ≤ k := by dsimp [k,densityThreshold]; omega
  have hkr : (16:ℝ) ≤ k := by exact_mod_cast hk
  have htp : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hl : 2*Real.log 2 ≤ Real.log (t:ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) (show (4:ℝ) ≤ t by exact_mod_cast ht)
    have he : Real.log (4:ℝ) = 2*Real.log 2 := by convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
    rwa [he] at hh
  have hlog : 0 ≤ Real.log (t:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  have hkl : 16*Real.log (t:ℝ) ≤ (k:ℝ) := by
    have hh := Nat.le_ceil (16*Real.log (t:ℝ))
    dsimp only [k,densityThreshold]
    push_cast
    linarith
  have hbase : 2*Real.exp 1/(k:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ (by linarith : (0:ℝ)<k)).mpr
    linarith [Real.exp_one_lt_d9]
  have hpow : (2*Real.exp 1/(k:ℝ))^k ≤ (1/2:ℝ)^k := pow_le_pow_left₀ (by positivity) hbase k
  have heq : Real.exp 1*(t:ℝ)*(1/2:ℝ)^k =
      Real.exp (1+Real.log (t:ℝ)-(k:ℝ)*Real.log 2) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_log htp, Real.exp_log (by norm_num)]
    rw [div_pow]
    ring
  have hsmall : 1+Real.log (t:ℝ)-(k:ℝ)*Real.log 2 ≤ -(8*Real.log 2) := by
    have hh : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hp := mul_le_mul_of_nonneg_right hkl (by linarith : 0 ≤ Real.log 2)
    nlinarith
  refine ⟨hk,?_⟩
  calc
    _ ≤ Real.exp 1*(t:ℝ)*(1/2:ℝ)^k := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ Real.exp (-(8*Real.log 2)) := by rw [heq]; exact Real.exp_le_exp.mpr hsmall
    _ = _ := by rw [Real.exp_neg, show (8:ℝ)*Real.log 2 = (8:ℕ)*Real.log 2 by norm_num,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]; norm_num

theorem densityThreshold_upper (t : ℕ) (ht : 1 ≤ t) :
    (densityThreshold t:ℝ) ≤ 16*Real.log (t:ℝ)+17 := by
  have hh := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ) ≤ 16)
    (Real.log_nonneg (show (1:ℝ) ≤ t by exact_mod_cast ht)))
  unfold densityThreshold
  push_cast
  linarith

theorem family_parameter_bounds (b : ℕ) (hb : 16 ≤ b) :
    4 ≤ branching b ∧ 2 ≤ width b ∧ branching b ≤ width b ∧
      layerSum (branching b) b ≤ width b ∧ b ≤ size b ∧ size b ≤ (width b)^2 := by
  let t := branching b
  have ht : 4 ≤ t := by
    change 4 ≤ (16*b)^3
    exact (show 4 ≤ 16*b by omega).trans (Nat.le_pow (by decide : 0 < 3))
  have hbt : b ≤ t := by
    change b ≤ (16*b)^3
    exact (show b ≤ 16*b by omega).trans (Nat.le_pow (by decide : 0 < 3))
  have hpow : 1 ≤ t^b := Nat.one_le_pow _ _ (by omega)
  have hpowt : t ≤ t^b := Nat.le_pow (by omega)
  have hm : b ≤ width b := by change b ≤ 2*t^b; omega
  have htm : t ≤ width b := by change t ≤ 2*t^b; omega
  have hQ : layerSum t b ≤ width b := by
    have hh := layerSum_geometric_upper t b (by omega)
    have hh' : layerSum t b ≤ layerSum t (b+1) := by rw [layerSum_succ]; omega
    exact hh'.trans hh
  have hS := layerSum_geometric_upper t b (by omega)
  have hSpos : 1 ≤ layerSum t (b+1) := layerSum_pos t (b+1) (by omega)
  have hN : b ≤ size b := by unfold size; change b ≤ width b*layerSum t (b+1); nlinarith
  have hNupper : size b ≤ (width b)^2 := by
    have hmdef : width b = 2*t^b := rfl
    unfold size
    change width b*layerSum t (b+1) ≤ (width b)^2
    nlinarith
  exact ⟨ht,by change 2 ≤ 2*t^b; omega,htm,hQ,hN,hNupper⟩

theorem family_edges_nonempty (b : ℕ) (hb : 16 ≤ b) : Nonempty (Edges b (branching b) (width b)) := by
  have hp := family_parameter_bounds b hb
  apply Fintype.card_pos_iff.mp
  rw [card_edges]
  have hh := layerSum_pos (branching b) b (by omega)
  have ht := hp.1
  have hm := hp.2.1
  positivity

theorem family_rate_bounds (b : ℕ) (hb : 16 ≤ b) :
    (Fintype.card (Edges b (branching b) (width b)):ℝ) ≤ (size b:ℝ)*width b ∧
      (size b:ℝ)*width b ≤ 2*(Fintype.card (Edges b (branching b) (width b)):ℝ) := by
  have hp := family_parameter_bounds b hb
  have hQ : 0 < layerSum (branching b) b := layerSum_pos _ _ (by omega)
  rw [size_eq_vertices,card_vertices,card_edges]
  have hshift := layerSum_shift (branching b) b
  rw [hshift]
  have hprod : 1 ≤ branching b*layerSum (branching b) b := by nlinarith [hp.1]
  have hh := Nat.mul_le_mul_left ((width b)^2) hprod
  constructor
  · exact_mod_cast (by nlinarith : (width b)^2*branching b*layerSum (branching b) b ≤
      width b*(1+branching b*layerSum (branching b) b)*width b)
  · exact_mod_cast (by nlinarith : width b*(1+branching b*layerSum (branching b) b)*width b ≤
      2*((width b)^2*branching b*layerSum (branching b) b))

end GraphChoices.LowerBound
