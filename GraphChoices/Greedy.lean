import GraphChoices.Model
import Mathlib.Data.Nat.Log

/-! A quantitative version of Fact 3.6, for every arrival sequence and either
legal tie choice. The proof uses a doubling inequality for high-load layers. -/
namespace GraphChoices
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}

def prefixLoad (I : Instance V T) (a : Orientation T) (k : ℕ) (v : V) : ℕ :=
  (univ.filter fun t => t.val < k ∧ destination I a t = v).card

/-- A relational specification: both ways of breaking ties are included. -/
def IsGreedy (I : Instance V T) (a : Orientation T) : Prop :=
  ∀ t, ∀ v, (v = I.left t ∨ v = I.right t) →
    prefixLoad I a t.val (destination I a t) ≤ prefixLoad I a t.val v

omit [Fintype V] in
 theorem prefixLoad_le_load (I : Instance V T) (a : Orientation T) (k : ℕ) (v : V) :
    prefixLoad I a k v ≤ load I a v := by
  apply card_le_card
  intro t ht
  simp only [mem_filter, mem_univ, true_and] at ht ⊢
  exact ht.2

omit [Fintype V] in
 theorem prefixLoad_strict (I : Instance V T) (a : Orientation T) (v : V)
    (t u : Fin T) (htu : t < u) (ht : destination I a t = v) :
    prefixLoad I a t.val v < prefixLoad I a u.val v := by
  have hnot : t ∉ univ.filter (fun s : Fin T => s.val < t.val ∧ destination I a s = v) := by simp
  have hsub : insert t (univ.filter fun s : Fin T => s.val < t.val ∧ destination I a s = v) ⊆
      univ.filter (fun s : Fin T => s.val < u.val ∧ destination I a s = v) := by
    intro s hs
    rcases mem_insert.mp hs with rfl | hs
    · simp [htu, ht]
    · simp only [mem_filter, mem_univ, true_and] at hs ⊢
      exact ⟨lt_trans hs.1 htu, hs.2⟩
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hnot] at hc
  exact hc

omit [Fintype V] in
/-- A vertex has at most k arrivals assigned before its load reaches k. -/
 theorem low_arrivals_le (I : Instance V T) (a : Orientation T) (v : V) (k : ℕ) :
    (univ.filter fun t => destination I a t = v ∧ prefixLoad I a t.val v < k).card ≤ k := by
  have h := card_le_card_of_injOn (fun t : Fin T => prefixLoad I a t.val v)
    (s := univ.filter fun t => destination I a t = v ∧ prefixLoad I a t.val v < k)
    (t := range k)
    (by intro t ht; simpa using (mem_filter.mp ht).2.2)
    (by
      intro t ht u hu heq
      dsimp at heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := prefixLoad_strict I a v t u h (mem_filter.mp ht).2.1
        omega
      · have := prefixLoad_strict I a v u t h (mem_filter.mp hu).2.1
        omega)
  simpa using h

def highVertices (I : Instance V T) (a : Orientation T) (k : ℕ) : Finset V :=
  univ.filter fun v => k ≤ load I a v

def highArrivals (I : Instance V T) (a : Orientation T) (k : ℕ) : Finset (Fin T) :=
  univ.filter fun t => k ≤ prefixLoad I a t.val (destination I a t)

 theorem highArrivals_internal (I : Instance V T) (a : Orientation T) (hg : IsGreedy I a)
    (k : ℕ) :
    highArrivals I a k ⊆ univ.filter
      (fun t => I.left t ∈ highVertices I a k ∧ I.right t ∈ highVertices I a k) := by
  intro t ht
  have hk := (mem_filter.mp ht).2
  simp only [mem_filter, mem_univ, true_and, highVertices]
  exact ⟨le_trans hk ((hg t _ (Or.inl rfl)).trans (prefixLoad_le_load I a _ _)),
    le_trans hk ((hg t _ (Or.inr rfl)).trans (prefixLoad_le_load I a _ _))⟩

omit [Fintype V] in
 theorem load_le_low_add_high (I : Instance V T) (a : Orientation T) (v : V) (k : ℕ) :
    load I a v ≤ k + ((highArrivals I a k).filter fun t => destination I a t = v).card := by
  have heq : load I a v =
      (univ.filter fun t => destination I a t = v ∧ prefixLoad I a t.val v < k).card +
      ((highArrivals I a k).filter fun t => destination I a t = v).card := by
    rw [load, ← filter_card_add_filter_neg_card_eq_card (s := univ.filter fun t => destination I a t = v)
      (p := fun t => prefixLoad I a t.val v < k)]
    congr 1
    · congr 1
      ext t
      simp
    · congr 1
      ext t
      simp only [highArrivals, mem_filter, mem_univ, true_and, not_lt]
      constructor
      · rintro ⟨hd, hk⟩; exact ⟨by simpa [hd] using hk, hd⟩
      · rintro ⟨hk, hd⟩; exact ⟨hd, by simpa [hd] using hk⟩
  rw [heq]
  exact Nat.add_le_add_right (low_arrivals_le I a v k) _

/-- The key deterministic layer inequality, with the true offline optimum. -/
 theorem greedy_layer_bound (I : Instance V T) (a : Orientation T) (hg : IsGreedy I a)
    (k d : ℕ) :
    d * (highVertices I a (k + d)).card ≤ opt I * (highVertices I a k).card := by
  calc
    d * (highVertices I a (k + d)).card = ∑ v ∈ highVertices I a (k+d), d := by simp [mul_comm]
    _ ≤ ∑ v ∈ highVertices I a (k+d),
        ((highArrivals I a k).filter fun t => destination I a t = v).card := by
      apply sum_le_sum
      intro v hv
      have hl := (mem_filter.mp hv).2
      have hb := load_le_low_add_high I a v k
      omega
    _ ≤ ∑ v, ((highArrivals I a k).filter fun t => destination I a t = v).card :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = (highArrivals I a k).card := by
      symm
      exact card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ internalCount I (highVertices I a k) := card_le_card (highArrivals_internal I a hg k)
    _ ≤ opt I * (highVertices I a k).card := by
      simpa [mul_comm] using density_le_opt I (highVertices I a k)

 theorem greedy_layers_decay (I : Instance V T) (a : Orientation T) (hg : IsGreedy I a)
    (hc : 0 < opt I) (j : ℕ) :
    2^j * (highVertices I a (2 * opt I * j)).card ≤ Fintype.card V := by
  induction j with
  | zero => simp [highVertices]
  | succ j ih =>
    have h := greedy_layer_bound I a hg (2 * opt I * j) (2 * opt I)
    have hstep : 2 * (highVertices I a (2 * opt I * (j+1))).card ≤
        (highVertices I a (2 * opt I * j)).card := by
      have heq : 2 * opt I * j + 2 * opt I = 2 * opt I * (j+1) := by ring
      rw [heq] at h
      nlinarith
    calc
      _ = 2^j * (2 * (highVertices I a (2 * opt I * (j+1))).card) := by rw [pow_succ]; ring
      _ ≤ 2^j * (highVertices I a (2 * opt I * j)).card := Nat.mul_le_mul_left _ hstep
      _ ≤ _ := ih

/-- Explicit adversarial bound. Any j with 2^j > |V| is sufficient. -/
 theorem greedy_maxLoad_lt (I : Instance V T) (a : Orientation T) (hg : IsGreedy I a)
    (hT : 0 < T) (j : ℕ) (hj : Fintype.card V < 2^j) :
    maxLoad I a < 2 * opt I * j := by
  have hd := greedy_layers_decay I a hg (opt_pos I hT) j
  have hz : (highVertices I a (2 * opt I * j)).card = 0 := by
    by_contra hn
    have : 1 ≤ (highVertices I a (2 * opt I * j)).card := by omega
    have := Nat.mul_le_mul_left (2^j) this
    omega
  have hn : Nonempty V := ⟨I.left ⟨0,hT⟩⟩
  have hp : 0 < 2 * opt I * j := by
    have : 0 < j := by
      by_contra h
      have hj0 : j = 0 := by omega
      have := Fintype.card_pos_iff.mpr hn
      simp [hj0] at hj
    exact Nat.mul_pos (Nat.mul_pos (by omega) (opt_pos I hT)) this
  have hbound : maxLoad I a ≤ 2 * opt I * j - 1 := by
    apply (maxLoad_le_iff I a _).2
    intro v
    have hnot : v ∉ highVertices I a (2 * opt I * j) := by
      rw [card_eq_zero.mp hz]; simp
    simp only [highVertices, mem_filter, mem_univ, true_and, not_le] at hnot
    omega
  omega

/-- Fact 3.6, with an explicit constant and base-two logarithm. -/
 theorem greedy_competitive (I : Instance V T) (a : Orientation T) (hg : IsGreedy I a)
    (hT : 0 < T) :
    maxLoad I a < 2 * opt I * (Nat.log 2 (Fintype.card V) + 1) := by
  exact greedy_maxLoad_lt I a hg hT _ (Nat.lt_pow_succ_log_self (by decide) _)

end GraphChoices
