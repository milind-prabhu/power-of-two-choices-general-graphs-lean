import GraphChoices.RateCompetitive

namespace GraphChoices
open Finset

theorem greedy_bound_by_arrivals {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}
    (I : Instance V T) (a : Orientation T) (hg : IsGreedy I a) (hT : 0 < T) :
    maxLoad I a ≤ 2*opt I*(Nat.log 2 (2*T)+1) := by
  let S := univ.image I.left ∪ univ.image I.right
  have hl (t : Fin T) : I.left t ∈ S := mem_union_left _ (mem_image.mpr ⟨t,mem_univ _,rfl⟩)
  have hr (t : Fin T) : I.right t ∈ S := mem_union_right _ (mem_image.mpr ⟨t,mem_univ _,rfl⟩)
  have hc : S.card ≤ 2*T := by
    have h1 := card_image_le (f := I.left) (s := univ)
    have h2 := card_image_le (f := I.right) (s := univ)
    have h3 := card_union_le (univ.image I.left) (univ.image I.right)
    simp only [card_univ, Fintype.card_fin] at h1 h2
    dsimp only [S]
    omega
  apply (maxLoad_le_iff _ _ _).mpr
  intro v
  by_cases hv : v ∈ S
  · exact (greedy_load_lt_of_closed I a hg S (fun t => ⟨fun _ => hr t,fun _ => hl t⟩)
      hT (Nat.log 2 (2*T)+1) (hc.trans_lt (Nat.lt_pow_succ_log_self (by decide) _)) v hv).le
  · have hz : load I a v = 0 := by
      apply card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro t ht
      have hd := (mem_filter.mp ht).2
      have hm : destination I a t ∈ S := by
        rcases destination_endpoint I a t with he | he
        · rw [he]; exact hl t
        · rw [he]; exact hr t
      exact hv (hd ▸ hm)
    rw [hz]
    omega

end GraphChoices

namespace GraphChoices.Peeling
open Finset ThresholdGreedy
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def simpleEncode (G : Graph L R) (e : G) : Arrival L R Unit := ⟨e.val.1,e.val.2,()⟩
def simpleGreedyPolicy (G : Graph L R) : OnlinePolicy G := thresholdPolicy (simpleEncode G) (fun _ => 0)

theorem simpleGreedyPolicy_isGreedy (G : Graph L R) [Nonempty G] {T : ℕ} (ω : Fin T → G) :
    IsGreedy ((graphBase G).sample ω) (onlineOrientation (simpleGreedyPolicy G) ω) := by
  apply isGreedy_of_execution _ _ (policyPrefixLoad (simpleEncode G) (fun _ => 0) ω)
    (policyPrefixLoad_zero _ _ ω) (policyPrefixLoad_step _ _ ω)
  intro t v hv
  let es := (((List.ofFn ω).take t.val).map (simpleEncode G))
  let s := run (fun _ : Unit => 0) es
  have hzero (u : L) : ∑ i : Unit, s.threshold u i = 0 := by
    have hh := threshold_budget (fun _ : Unit => 0) es u
    simpa only [sum_const_zero, Nat.le_zero] using hh
  have hload (u : L) : stateLoad s (Sum.inl u) = s.greedyLeft u := by simp only [stateLoad, Sum.elim_inl, hzero, zero_add]
  change stateLoad s (if stepChoice (fun _ : Unit => 0) s (simpleEncode G (ω t)) then
    Sum.inl (ω t).val.1 else Sum.inr (ω t).val.2) ≤ stateLoad s v
  change v = Sum.inl (ω t).val.1 ∨ v = Sum.inr (ω t).val.2 at hv
  simp only [stepChoice, Nat.not_lt_zero, ↓reduceIte, simpleEncode, decide_eq_true_eq]
  by_cases hh : s.greedyLeft (ω t).val.1 < s.greedyRight (ω t).val.2
  · rw [if_pos hh, hload]
    rcases hv with rfl | rfl
    · rw [hload]
    · exact hh.le
  · rw [if_neg hh]
    rcases hv with rfl | rfl
    · rw [hload]
      exact le_of_not_gt hh
    · exact le_rfl

theorem short_horizon_policy (G : Graph L R) [Nonempty G] (N T : ℕ)
    (hT : 0 < T) (hlog : 2 ≤ Real.log (N:ℝ)) (hshort : (T:ℝ) ≤ Real.log (N:ℝ)) :
    expectedCost (graphBase G) (onlineOrientation (T := T) (simpleGreedyPolicy G)) ≤
      12*loglogFactor N*expectedOpt (graphBase G) T := by
  have hgreedy : expectedCost (graphBase G) (onlineOrientation (T := T) (simpleGreedyPolicy G)) ≤
      (2*(Nat.log 2 (2*T)+1):ℕ)*expectedOpt (graphBase G) T := by
    unfold expectedCost expectedOpt
    rw [← average_mul]
    apply average_mono
    intro ω
    have hh := greedy_bound_by_arrivals ((graphBase G).sample ω) _ (simpleGreedyPolicy_isGreedy G ω) hT
    exact_mod_cast (by nlinarith : maxLoad ((graphBase G).sample ω) (onlineOrientation (simpleGreedyPolicy G) ω) ≤
      (2*(Nat.log 2 (2*T)+1))*opt ((graphBase G).sample ω))
  have hln := nat_log_le_twice_real_log (2*T) (by omega)
  have hTp : (0:ℝ) < T := by exact_mod_cast hT
  have hlogT := Real.log_le_log hTp hshort
  have hloglog := Real.log_le_log (by linarith : 0 < Real.log (N:ℝ)) (by linarith : Real.log (N:ℝ) ≤ 1+Real.log (N:ℝ))
  have hN2 : (2:ℝ) ≤ N := by
    by_contra hn
    have hnat : N < 2 := by exact_mod_cast lt_of_not_ge hn
    have hz : N = 0 ∨ N = 1 := by omega
    rcases hz with rfl | rfl <;> norm_num at hlog
  have hfactor : loglogFactor N = 1+Real.log (1+Real.log (N:ℝ)) := by unfold loglogFactor; rw [max_eq_right hN2]
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  rw [Nat.cast_mul, Real.log_mul (by norm_num) hTp.ne'] at hln
  norm_num only [Nat.cast_ofNat] at hln
  have hcoeff : (((2*(Nat.log 2 (2*T)+1):ℕ):ℝ)) ≤ 12*loglogFactor N := by
    push_cast
    rw [hfactor]
    have hh := Real.log_nonneg (show 1 ≤ 1+Real.log (N:ℝ) by linarith)
    linarith
  exact hgreedy.trans (mul_le_mul_of_nonneg_right hcoeff (expectedOpt_nonneg _ _))

end GraphChoices.Peeling
