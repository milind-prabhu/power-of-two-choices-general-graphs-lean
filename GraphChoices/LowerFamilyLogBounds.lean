import GraphChoices.LowerFamilyParameters

namespace GraphChoices.LowerBound
open Finset

theorem branching_log (b : ℕ) : Real.log (branching b:ℝ) = 3*Real.log (16*(b:ℝ)) := by
  simp only [branching, Nat.cast_pow, Nat.cast_mul, Real.log_pow, Nat.cast_ofNat]

theorem family_elementary_logs (b : ℕ) (hb : 16 ≤ b) :
    1 ≤ Real.log ((b:ℝ)+1) ∧ 15 ≤ Real.log (branching b:ℝ) ∧
      Real.log (branching b:ℝ) ≤ 12*Real.log ((b:ℝ)+1) := by
  have hbr : (16:ℝ) ≤ b := by exact_mod_cast hb
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have h16 : Real.log (16:ℝ) = 4*Real.log 2 := by convert Real.log_pow (2:ℝ) 4 using 1 <;> norm_num
  have h256 : Real.log (256:ℝ) = 8*Real.log 2 := by convert Real.log_pow (2:ℝ) 8 using 1 <;> norm_num
  have hbp := Real.log_le_log (by norm_num : (0:ℝ)<16) (show (16:ℝ) ≤ (b:ℝ)+1 by linarith)
  rw [h16] at hbp
  have h15 := Real.log_le_log (by norm_num : (0:ℝ)<256) (show (256:ℝ) ≤ 16*(b:ℝ) by linarith)
  rw [h256] at h15
  have hblog := Real.log_le_log (show (0:ℝ)<b by linarith) (show (b:ℝ) ≤ (b:ℝ)+1 by linarith)
  have ht := branching_log b
  rw [Real.log_mul (by norm_num) (by positivity),h16] at ht
  refine ⟨by linarith,?_,?_⟩
  · rw [branching_log]; linarith
  · linarith

theorem family_log_bounds (b : ℕ) (hb : 16 ≤ b) :
    (b:ℝ)+1 ≤ Real.log (size b:ℝ) ∧
      Real.log (size b:ℝ) ≤ 26*(b:ℝ)*Real.log ((b:ℝ)+1) := by
  have hp := family_parameter_bounds b hb
  obtain ⟨hlogbp,hlogt,hlogt_up⟩ := family_elementary_logs b hb
  have hbr : (16:ℝ) ≤ b := by exact_mod_cast hb
  have htp : 0 < branching b := by have := hp.1; omega
  have hN : 0 < size b := by have := hp.2.2.2.2.1; omega
  have hpowm : (branching b)^b ≤ width b := by unfold width; omega
  have hmN : width b ≤ size b := by
    unfold size
    have hs : 1 ≤ layerSum (branching b) (b+1) := layerSum_pos _ _ (by omega)
    nlinarith
  have hlogpow := Real.log_le_log (show (0:ℝ) < (branching b:ℝ)^b by positivity)
    (show (branching b:ℝ)^b ≤ size b by exact_mod_cast hpowm.trans hmN)
  rw [Real.log_pow] at hlogpow
  constructor
  · nlinarith
  · have hupper : size b ≤ 2*(b+1)*(branching b)^(2*b) := by
      unfold size
      have hs := layerSum_upper (branching b) b (by have := hp.1; omega)
      have hh := Nat.mul_le_mul_left (width b) hs
      unfold width at hh
      convert hh using 1 <;> rw [show 2*b = b+b by omega,pow_add] <;> ring
    have hu := Real.log_le_log (show (0:ℝ) < size b by exact_mod_cast hN)
      (show (size b:ℝ) ≤ 2*((b:ℝ)+1)*(branching b:ℝ)^(2*b) by exact_mod_cast hupper)
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hu
    push_cast at hu
    have hmul := mul_le_mul_of_nonneg_left hlogt_up (show 0 ≤ 2*(b:ℝ) by positivity)
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith

theorem family_log_large (b : ℕ) (hb : 16 ≤ b) : 30*(b:ℝ) ≤ Real.log (size b:ℝ) := by
  have hp := family_parameter_bounds b hb
  have htp : 0 < branching b := by have := hp.1; omega
  have hS : (branching b)^b ≤ layerSum (branching b) (b+1) := by rw [layerSum_succ]; omega
  have hN : 2*(branching b)^(2*b) ≤ size b := by
    unfold size width
    rw [show 2*b = b+b by omega,pow_add]
    have hh := Nat.mul_le_mul_left (2*(branching b)^b) hS
    nlinarith
  have hh := Real.log_le_log (show (0:ℝ) < 2*(branching b:ℝ)^(2*b) by positivity)
    (show 2*(branching b:ℝ)^(2*b) ≤ size b by exact_mod_cast hN)
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
  push_cast at hh
  have ht := (family_elementary_logs b hb).2.1
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2*(b:ℝ) by positivity)
  nlinarith

theorem branching_large (b : ℕ) (hb : 16 ≤ b) : 1024*b^3 ≤ branching b := by
  unfold branching
  rw [show (16*b)^3 = 4096*b^3 by ring]
  omega

theorem family_propagation_error (b : ℕ) (hb : 16 ≤ b) :
    (b:ℝ)*(Fintype.card (Blocks b (branching b)):ℝ)*width b*
      Real.exp ((b:ℝ)*Real.log 2-(batchLength b:ℝ)*(branching b*width b)/
        (4*(Fintype.card (Edges b (branching b) (width b)):ℝ))) ≤ 1/(size b:ℝ)^2 := by
  have hp := family_parameter_bounds b hb
  letI := family_edges_nonempty b hb
  have hbr : (16:ℝ) ≤ b := by exact_mod_cast hb
  have hm : (0:ℝ) < width b := by have hh := hp.2.1; exact_mod_cast (show 0 < width b by omega)
  have hN : (0:ℝ) < size b := by have hh := hp.2.2.2.2.1; exact_mod_cast (show 0 < size b by omega)
  have hE : (0:ℝ) < Fintype.card (Edges b (branching b) (width b)) := by exact_mod_cast Fintype.card_pos
  have hQ : (0:ℝ) < Fintype.card (Blocks b (branching b)) := by rw [card_blocks]; exact_mod_cast layerSum_pos (branching b) b (by omega)
  let M : ℝ := Fintype.card (Edges b (branching b) (width b))
  let μ : ℝ := (batchLength b:ℝ)*(branching b*width b)/(4*M)
  let C : ℝ := (b:ℝ)*(Fintype.card (Blocks b (branching b)):ℝ)*width b
  have hC : 0 < C := by dsimp [C]; positivity
  have hμ : 256*(b:ℝ)^2 ≤ μ := by
    have hr := (family_rate_bounds b hb).1
    have hmul := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (branching b): (0:ℝ) ≤ branching b)
    have hsize : (size b:ℝ) = (b:ℝ)*batchLength b := by exact_mod_cast size_eq_batches b (by omega)
    have hlow : (branching b:ℝ)/(4*(b:ℝ)) ≤ μ := by
      apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*(b:ℝ)) (by dsimp [M]; positivity : (0:ℝ)<4*M)).mpr
      dsimp [μ]
      rw [hsize] at hmul
      push_cast
      nlinarith
    have ht : 1024*(b:ℝ)^3 ≤ branching b := by exact_mod_cast branching_large b hb
    apply le_trans _ hlow
    apply (le_div_iff₀ (by positivity : (0:ℝ)<4*(b:ℝ))).mpr
    nlinarith
  have hCbound : C ≤ (b:ℝ)*size b := by
    have hQle : layerSum (branching b) b ≤ layerSum (branching b) (b+1) := by rw [layerSum_succ]; omega
    have hmul := Nat.mul_le_mul_left (b*width b) hQle
    dsimp only [C]
    rw [card_blocks,size_eq_vertices,card_vertices]
    exact_mod_cast (by nlinarith : b*layerSum (branching b) b*width b ≤ b*(width b*layerSum (branching b) (b+1)))
  have hlogC := Real.log_le_log hC hCbound
  rw [Real.log_mul (by positivity) hN.ne'] at hlogC
  have hlogN := (family_log_bounds b hb).2
  have hlogbp := Real.log_le_sub_one_of_pos (show (0:ℝ)<(b:ℝ)+1 by positivity)
  have hlogb := Real.log_le_sub_one_of_pos (show (0:ℝ)<b by positivity)
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogN' : Real.log (size b:ℝ) ≤ 26*(b:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hlogbp (show 0 ≤ 26*(b:ℝ) by positivity)
    nlinarith
  have hexp : Real.log C+((b:ℝ)*Real.log 2-μ) ≤ -(2*Real.log (size b:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg b : (0:ℝ) ≤ b)
    nlinarith
  change C*Real.exp ((b:ℝ)*Real.log 2-μ) ≤ _
  calc
    _ = Real.exp (Real.log C+((b:ℝ)*Real.log 2-μ)) := by rw [Real.exp_add,Real.exp_log hC]
    _ ≤ Real.exp (-(2*Real.log (size b:ℝ))) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_neg,show (2:ℝ)*Real.log (size b:ℝ) = (2:ℕ)*Real.log (size b:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hN]; simp

end GraphChoices.LowerBound
