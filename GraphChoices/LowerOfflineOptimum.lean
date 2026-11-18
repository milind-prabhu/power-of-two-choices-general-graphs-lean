import GraphChoices.CompleteBlockTail
import GraphChoices.LowerFamilyParameters

namespace GraphChoices.LowerBound
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C]

theorem expectedOpt_complete_blocks (m t T k : ℕ) (left : C × Fin m → V) (right : C × Fin (t*m) → V)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hm : 0 < m) (ht : 1 ≤ t) (hk : 16 ≤ k)
    (hrate : (T:ℝ)*(m:ℝ) ≤ 2*(Fintype.card (C × (Fin m × Fin (t*m))):ℝ))
    (hscale : Real.exp 1*(t:ℝ)*(2*Real.exp 1/(k:ℝ))^k ≤ 1/256) :
    letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    letI : Nonempty (Fin (t*m)) := ⟨⟨0,by positivity⟩⟩
    expectedOpt (blockBase left right) T ≤
      2*(k:ℝ)+(T:ℝ)*((Fintype.card C:ℝ)*m*(t*m)/(m:ℝ)^8) := by
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  letI : Nonempty (Fin (t*m)) := ⟨⟨0,by positivity⟩⟩
  have hh := average_le_good_add_bad
    (fun ω : Fin T → C × (Fin m × Fin (t*m)) => (opt ((blockBase left right).sample ω):ℝ))
    (fun _ => 2*(k:ℝ)) (badBlockDensity m (t*m) T k) (T:ℝ)
    (fun ω hω => by
      change (opt ((blockBase left right).sample ω):ℝ) ≤ 2*(k:ℝ)
      exact_mod_cast opt_le_of_block_density left right hl hr ω k (not_badBlockDensity _ _ _ _ ω hω))
    (fun ω _ => by
      change (opt ((blockBase left right).sample ω):ℝ) ≤ 2*(k:ℝ)+(T:ℝ)
      have hp := opt_le_length ((blockBase left right).sample ω)
      exact_mod_cast (show opt ((blockBase left right).sample ω) ≤ 2*k+T by omega))
  rw [average_const] at hh
  apply hh.trans
  have hb := badBlockDensity_probability (C := C) m t T k hm ht hk hrate hscale
  nlinarith

theorem family_offline_bound (b : ℕ) (hb : 16 ≤ b) :
    letI := family_edges_nonempty b hb
    expectedOpt (graph b (branching b) (width b)) (size b) ≤
      2*(densityThreshold (branching b):ℝ)+1 := by
  letI := family_edges_nonempty b hb
  have hp := family_parameter_bounds b hb
  letI : Nonempty (Blocks b (branching b)) := ⟨⟨⟨0,by omega⟩,⟨0,by simp⟩⟩⟩
  obtain ⟨hk,hscale⟩ := densityThreshold_scale (branching b) hp.1
  have hh := expectedOpt_complete_blocks (width b) (branching b) (size b) (densityThreshold (branching b))
    (@leftVertex b (branching b) (width b)) (@rightVertex b (branching b) (width b))
    (leftVertex_injective _ _ _) (rightVertex_injective _ _ _) (by omega) (by omega)
    hk (family_rate_bounds b hb).2 hscale
  change expectedOpt (graph b (branching b) (width b)) (size b) ≤ _ at hh
  have hmr : (2:ℝ) ≤ width b := by exact_mod_cast hp.2.1
  have hQ : (Fintype.card (Blocks b (branching b)):ℝ) ≤ width b := by
    rw [card_blocks]
    exact_mod_cast hp.2.2.2.1
  have ht : (branching b:ℝ) ≤ width b := by exact_mod_cast hp.2.2.1
  have hN : (size b:ℝ) ≤ 2*(width b:ℝ)^2 := by
    have hh : (size b:ℝ) ≤ (width b:ℝ)^2 := by exact_mod_cast hp.2.2.2.2.2
    nlinarith
  have hnum : (Fintype.card (Blocks b (branching b)):ℝ)*width b*(branching b*width b) ≤ (width b:ℝ)^4 := by
    push_cast
    have h1 := mul_le_mul_of_nonneg_right hQ (show 0 ≤ (width b:ℝ)*(branching b:ℝ)*width b by positivity)
    have h2 := mul_le_mul_of_nonneg_right ht (show 0 ≤ (width b:ℝ)^3 by positivity)
    nlinarith
  have herr : (size b:ℝ)*((Fintype.card (Blocks b (branching b)):ℝ)*width b*(branching b*width b)/(width b:ℝ)^8) ≤ 1 := by
    calc
      _ ≤ (size b:ℝ)*((width b:ℝ)^4/(width b:ℝ)^8) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) (Nat.cast_nonneg _)
      _ ≤ (2*(width b:ℝ)^2)*((width b:ℝ)^4/(width b:ℝ)^8) := mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 2/(width b:ℝ)^2 := by field_simp
      _ ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  exact hh.trans (by linarith)

end GraphChoices.LowerBound
