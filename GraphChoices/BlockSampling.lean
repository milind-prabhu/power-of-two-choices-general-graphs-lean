import GraphChoices.SamplingTail

/-! A lower-tail substitute for Lemma 3.3: a bucket hit in every independent
block has at least as many occurrences as there are blocks. Disjoint buckets'
block-success indicators have nonpositive pairwise covariance. -/
namespace GraphChoices
open Finset

theorem average_unit_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (A : Finset Ω) :
    average (fun ω => if ω ∈ A then (1 : ℝ) else 0) = eventProbability A := by
  simp [average, eventProbability]

theorem eventProbability_le_one {Ω : Type*} [Fintype Ω] (A : Finset Ω) :
    eventProbability A ≤ 1 := by
  unfold eventProbability
  by_cases h : Fintype.card Ω = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    exact_mod_cast card_le_univ A

theorem eventProbability_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (A : Finset Ω) :
    eventProbability (univ \ A) = 1 - eventProbability A := by
  simp only [eventProbability, card_sdiff, inter_univ, card_univ]
  rw [Nat.cast_sub (card_le_univ A)]
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem eventProbability_union_inter {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A B : Finset Ω) :
    eventProbability (A ∪ B) + eventProbability (A ∩ B) =
      eventProbability A + eventProbability B := by
  unfold eventProbability
  rw [← add_div, ← add_div]
  congr 1
  exact_mod_cast card_union_add_card_inter A B

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

def blockHitEvent (A : Finset E) (s : ℕ) : Finset (Fin s → E) :=
  univ.filter fun ω => ∃ t, ω t ∈ A

theorem blockHitEvent_compl (A : Finset E) (s : ℕ) :
    univ \ blockHitEvent A s = Fintype.piFinset (fun _ : Fin s => univ \ A) := by
  ext ω
  simp [blockHitEvent, Fintype.mem_piFinset]

theorem blockHit_probability (A : Finset E) (s : ℕ) :
    eventProbability (blockHitEvent A s) =
      1 - (1 - (A.card : ℝ) / Fintype.card E)^s := by
  have h := eventProbability_compl (blockHitEvent A s)
  rw [blockHitEvent_compl, probability_coordinate_constraints] at h
  have hm : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((univ \ A).card : ℝ) / Fintype.card E =
      1 - (A.card : ℝ) / Fintype.card E := by
    rw [card_sdiff, inter_univ, card_univ, Nat.cast_sub (card_le_univ A)]
    field_simp
  simp only [hc, prod_const, card_univ, Fintype.card_fin] at h
  linarith

theorem blockHit_union (A B : Finset E) (s : ℕ) :
    blockHitEvent A s ∪ blockHitEvent B s = blockHitEvent (A ∪ B) s := by
  ext ω
  simp only [mem_union, blockHitEvent, mem_filter, mem_univ, true_and, mem_union]
  exact exists_or.symm

theorem blockHit_disjoint_covariance (A B : Finset E) (s : ℕ) (hAB : Disjoint A B) :
    eventProbability (blockHitEvent A s ∩ blockHitEvent B s) ≤
      eventProbability (blockHitEvent A s) * eventProbability (blockHitEvent B s) := by
  have hi := eventProbability_union_inter (blockHitEvent A s) (blockHitEvent B s)
  rw [blockHit_union] at hi
  simp only [blockHit_probability] at hi ⊢
  have ha : (0 : ℝ) ≤ 1 - (A.card : ℝ) / Fintype.card E := by
    have h := eventProbability_le_one A
    unfold eventProbability at h
    linarith
  have hb : (0 : ℝ) ≤ 1 - (B.card : ℝ) / Fintype.card E := by
    have h := eventProbability_le_one B
    unfold eventProbability at h
    linarith
  have hab : (0 : ℝ) ≤ 1 - ((A.card : ℝ) + B.card) / Fintype.card E := by
    have h := eventProbability_le_one (A ∪ B)
    simp only [eventProbability, card_union_of_disjoint hAB, Nat.cast_add] at h
    linarith
  have hh : 1 - ((A.card : ℝ) + B.card) / Fintype.card E ≤
      (1 - (A.card : ℝ) / Fintype.card E) * (1 - (B.card : ℝ) / Fintype.card E) := by
    have hprod : (0 : ℝ) ≤ ((A.card : ℝ) / Fintype.card E) *
        ((B.card : ℝ) / Fintype.card E) := by positivity
    rw [add_div]
    nlinarith
  have hp := pow_le_pow_left₀ hab hh s
  rw [mul_pow] at hp
  simp only [card_union_of_disjoint hAB, Nat.cast_add] at hi
  nlinarith

noncomputable def allBlocksEvent (A : Finset E) (k s : ℕ) :
    Finset (Fin k → Fin s → E) := Fintype.piFinset fun _ => blockHitEvent A s

theorem allBlocks_probability (A : Finset E) (k s : ℕ) :
    eventProbability (allBlocksEvent A k s) = (eventProbability (blockHitEvent A s))^k := by
  rw [allBlocksEvent, probability_coordinate_constraints]
  simp [eventProbability, div_pow]

theorem allBlocks_inter (A B : Finset E) (k s : ℕ) :
    allBlocksEvent A k s ∩ allBlocksEvent B k s =
      Fintype.piFinset (fun _ : Fin k => blockHitEvent A s ∩ blockHitEvent B s) := by
  ext ω
  simp only [allBlocksEvent, mem_inter, Fintype.mem_piFinset]
  exact forall_and.symm

theorem allBlocks_disjoint_covariance (A B : Finset E) (k s : ℕ) (hAB : Disjoint A B) :
    eventProbability (allBlocksEvent A k s ∩ allBlocksEvent B k s) ≤
      eventProbability (allBlocksEvent A k s) * eventProbability (allBlocksEvent B k s) := by
  rw [allBlocks_inter, probability_coordinate_constraints]
  simp only [prod_const, card_univ, Fintype.card_fin]
  change (eventProbability (blockHitEvent A s ∩ blockHitEvent B s))^k ≤ _
  rw [allBlocks_probability, allBlocks_probability, ← mul_pow]
  exact pow_le_pow_left₀ (eventProbability_nonneg _) (blockHit_disjoint_covariance A B s hAB) k

theorem bernoulli_miss_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : ℕ) :
    (1-p)^s * (1+s*p) ≤ 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hh : (1-p)*(1+((s+1 : ℕ) : ℝ)*p) ≤ 1+s*p := by
      push_cast
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (s:ℝ)+1) (sq_nonneg p)]
    calc
      _ = (1-p)^s * ((1-p)*(1+((s+1 : ℕ) : ℝ)*p)) := by rw [pow_succ]; ring
      _ ≤ (1-p)^s * (1+s*p) := mul_le_mul_of_nonneg_left hh (pow_nonneg (by linarith) _)
      _ ≤ 1 := ih

/-- A direct binomial lower bound, valid without an asymptotic quantile lemma. -/
theorem blockHit_probability_lower (A : Finset E) (s : ℕ) :
    ((s:ℝ)*((A.card : ℝ)/Fintype.card E)) /
      (1+(s:ℝ)*((A.card : ℝ)/Fintype.card E)) ≤ eventProbability (blockHitEvent A s) := by
  have hp : (0 : ℝ) ≤ (A.card : ℝ)/Fintype.card E := by positivity
  have hp1 : (A.card : ℝ)/Fintype.card E ≤ 1 := eventProbability_le_one A
  rw [blockHit_probability]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1+(s:ℝ)*((A.card : ℝ)/Fintype.card E))).mpr
  have h := bernoulli_miss_bound _ hp hp1 s
  nlinarith

theorem blockHit_probability_lower_of_mean (A : Finset E) (s : ℕ) (x : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hmean : x ≤ (s:ℝ)*((A.card : ℝ)/Fintype.card E)) :
    x/2 ≤ eventProbability (blockHitEvent A s) := by
  have hm : (0 : ℝ) ≤ (s:ℝ)*((A.card : ℝ)/Fintype.card E) := by positivity
  apply le_trans _ (blockHit_probability_lower A s)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1+(s:ℝ)*((A.card : ℝ)/Fintype.card E))).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hmean) (sub_nonneg.mpr hx1)]

end GraphChoices
