import GraphChoices.WitnessProbability
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.Exponential

/-! An explicit binomial upper tail proved directly in the finite i.i.d.
sampling model, by selecting distinct witness time steps and union-bounding.
-/
namespace GraphChoices
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] {T : ℕ}

def hitCount (A : Finset E) (ω : Fin T → E) : ℕ :=
  (univ.filter fun t => ω t ∈ A).card

def hitTailEvent (A : Finset E) (T k : ℕ) : Finset (Fin T → E) :=
  univ.filter fun ω => k ≤ hitCount A ω

noncomputable def requiredHitsEvent (A : Finset E) (K : Finset (Fin T)) : Finset (Fin T → E) :=
  Fintype.piFinset fun t => if t ∈ K then A else univ

 theorem requiredHits_probability (A : Finset E) (K : Finset (Fin T)) :
    eventProbability (requiredHitsEvent A K) = ((A.card : ℝ) / Fintype.card E)^K.card := by
  classical
  rw [requiredHitsEvent, probability_coordinate_constraints]
  have hm : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfactor (t : Fin T) :
      (((if t ∈ K then A else univ : Finset E).card : ℝ) / Fintype.card E) =
      if t ∈ K then (A.card : ℝ) / Fintype.card E else 1 := by
    by_cases ht : t ∈ K <;> simp [ht,hm]
  simp_rw [hfactor]
  simp [div_pow]

 theorem hitTail_subset_witness_union (A : Finset E) (T k : ℕ) :
    hitTailEvent A T k ⊆
      (univ.powersetCard k).biUnion (fun K : Finset (Fin T) => requiredHitsEvent A K) := by
  classical
  intro ω hω
  have hk := (mem_filter.mp hω).2
  obtain ⟨K,hK,hcard⟩ := exists_subset_card_eq hk
  apply mem_biUnion.mpr
  refine ⟨K, mem_powersetCard.mpr ⟨subset_univ _,hcard⟩, ?_⟩
  simp only [requiredHitsEvent, Fintype.mem_piFinset]
  intro t
  by_cases ht : t ∈ K
  · simp only [if_pos ht]
    exact (mem_filter.mp (hK ht)).2
  · simp [ht]

/-- P[Bin(T,p) >= k] <= choose(T,k) p^k, with p = |A|/|E|.
This is an upper bound for every k, including k=0 and k>T. -/
 theorem hitTail_probability_le (A : Finset E) (T k : ℕ) :
    eventProbability (hitTailEvent A T k) ≤
      (T.choose k : ℝ) * ((A.card : ℝ) / Fintype.card E)^k := by
  calc
    _ ≤ eventProbability ((univ.powersetCard k).biUnion
        (fun K : Finset (Fin T) => requiredHitsEvent A K)) :=
      eventProbability_mono (hitTail_subset_witness_union A T k)
    _ ≤ ∑ K ∈ univ.powersetCard k, eventProbability (requiredHitsEvent A K) :=
      witness_union_bound _ _
    _ = ∑ _K ∈ (univ : Finset (Fin T)).powersetCard k,
        ((A.card : ℝ) / Fintype.card E)^k := by
      apply sum_congr rfl
      intro K hK
      rw [requiredHits_probability, (mem_powersetCard.mp hK).2]
    _ = _ := by simp [card_powersetCard]

/-- The standard exponential estimate for binomial coefficients, including
k=0. It is derived from the exponential series and the factorial bound. -/
theorem choose_le_exp_div_pow (T k : ℕ) :
    (T.choose k : ℝ) ≤ (Real.exp 1 * T / k)^k := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
  have he : Real.exp (k : ℝ) = (Real.exp 1)^k := by simpa using Real.exp_nat_mul 1 k
  have hp := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k : (0:ℝ) ≤ k) k
  rw [he] at hp
  have hscale := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ ((T:ℝ)/k)^k)
  calc
    (T.choose k : ℝ) ≤ (T:ℝ)^k / k.factorial := Nat.choose_le_pow_div k T
    _ = ((T:ℝ)/k)^k * ((k:ℝ)^k / k.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((T:ℝ)/k)^k * (Real.exp 1)^k := hscale
    _ = _ := by rw [← mul_pow]; congr 1; ring

/-- A Chernoff-style upper tail in the paper's exact sampling space. -/
theorem hitTail_probability_le_exp (A : Finset E) (T k : ℕ) :
    eventProbability (hitTailEvent A T k) ≤
      (Real.exp 1 * T * ((A.card : ℝ) / Fintype.card E) / k)^k := by
  calc
    _ ≤ (T.choose k : ℝ) * ((A.card : ℝ) / Fintype.card E)^k := hitTail_probability_le A T k
    _ ≤ (Real.exp 1 * T / k)^k * ((A.card : ℝ) / Fintype.card E)^k :=
      mul_le_mul_of_nonneg_right (choose_le_exp_div_pow T k) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

/-- A useful geometric form once the threshold dominates the bucket's mean. -/
theorem hitTail_probability_le_geometric (A : Finset E) (T k : ℕ) (r : ℝ)
    (h : Real.exp 1 * T * ((A.card : ℝ) / Fintype.card E) / k ≤ r) :
    eventProbability (hitTailEvent A T k) ≤ r^k := by
  apply (hitTail_probability_le_exp A T k).trans
  exact pow_le_pow_left₀ (by positivity) h k

/-- Union bound for large sampled degrees across any finite family of buckets. -/
theorem some_bucket_tail_bound {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Finset E) (T k : ℕ) (r : ℝ)
    (h : ∀ v, Real.exp 1 * T * (((A v).card : ℝ) / Fintype.card E) / k ≤ r) :
    eventProbability (univ.filter fun ω : Fin T → E => ∃ v, k ≤ hitCount (A v) ω) ≤
      Fintype.card V * r^k := by
  have hsub : (univ.filter fun ω : Fin T → E => ∃ v, k ≤ hitCount (A v) ω) ⊆
      univ.biUnion (fun v : V => hitTailEvent (A v) T k) := by
    intro ω hω
    obtain ⟨v,hv⟩ := (mem_filter.mp hω).2
    exact mem_biUnion.mpr ⟨v,mem_univ _,mem_filter.mpr ⟨mem_univ _,hv⟩⟩
  calc
    _ ≤ eventProbability (univ.biUnion fun v : V => hitTailEvent (A v) T k) := eventProbability_mono hsub
    _ ≤ ∑ v, eventProbability (hitTailEvent (A v) T k) := witness_union_bound _ _
    _ ≤ ∑ _v : V, r^k := sum_le_sum fun v _ => hitTail_probability_le_geometric (A v) T k r (h v)
    _ = _ := by simp

end GraphChoices
