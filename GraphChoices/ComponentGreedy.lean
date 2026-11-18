import GraphChoices.Greedy
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Greedy restricted to an edge-closed set. The logarithm depends on the
number of vertices in that set; the benchmark remains the full optimum.
No arrival occurrence is discarded or identified in the counting argument. -/
namespace GraphChoices
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}

/-- A union of components: no arrival crosses the boundary. -/
def EdgeClosed (I : Instance V T) (S : Finset V) : Prop :=
  ∀ t, I.left t ∈ S ↔ I.right t ∈ S

omit [Fintype V] [DecidableEq V] in
theorem endpoints_mem_of_destination_mem (I : Instance V T) (a : Orientation T)
    (S : Finset V) (hS : EdgeClosed I S) (t : Fin T)
    (ht : destination I a t ∈ S) : I.left t ∈ S ∧ I.right t ∈ S := by
  rcases destination_endpoint I a t with h | h
  · rw [h] at ht
    exact ⟨ht, (hS t).mp ht⟩
  · rw [h] at ht
    exact ⟨(hS t).mpr ht, ht⟩

def localHighVertices (I : Instance V T) (a : Orientation T) (S : Finset V) (k : ℕ) :=
  S.filter fun v => k ≤ load I a v

def localHighArrivals (I : Instance V T) (a : Orientation T) (S : Finset V) (k : ℕ) :=
  (highArrivals I a k).filter fun t => destination I a t ∈ S

theorem localHighArrivals_internal (I : Instance V T) (a : Orientation T)
    (hg : IsGreedy I a) (S : Finset V) (hS : EdgeClosed I S) (k : ℕ) :
    localHighArrivals I a S k ⊆ univ.filter (fun t =>
      I.left t ∈ localHighVertices I a S k ∧ I.right t ∈ localHighVertices I a S k) := by
  intro t ht
  obtain ⟨hhigh, hmem⟩ := mem_filter.mp ht
  have he := endpoints_mem_of_destination_mem I a S hS t hmem
  have hh := (mem_filter.mp (highArrivals_internal I a hg k hhigh)).2
  simp only [mem_filter, mem_univ, true_and, localHighVertices, highVertices] at hh ⊢
  exact ⟨⟨he.1, hh.1⟩, ⟨he.2, hh.2⟩⟩

theorem greedy_local_layer_bound (I : Instance V T) (a : Orientation T)
    (hg : IsGreedy I a) (S : Finset V) (hS : EdgeClosed I S) (k d : ℕ) :
    d * (localHighVertices I a S (k+d)).card ≤
      opt I * (localHighVertices I a S k).card := by
  calc
    _ = ∑ v ∈ localHighVertices I a S (k+d), d := by simp [mul_comm]
    _ ≤ ∑ v ∈ localHighVertices I a S (k+d),
        ((localHighArrivals I a S k).filter fun t => destination I a t = v).card := by
      apply sum_le_sum
      intro v hv
      obtain ⟨hvS, hvload⟩ := mem_filter.mp hv
      have heq : ((localHighArrivals I a S k).filter fun t => destination I a t = v) =
          ((highArrivals I a k).filter fun t => destination I a t = v) := by
        ext t
        simp only [localHighArrivals, mem_filter]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · exact fun h => ⟨⟨h.1, h.2 ▸ hvS⟩, h.2⟩
      rw [heq]
      have hb := load_le_low_add_high I a v k
      omega
    _ ≤ ∑ v, ((localHighArrivals I a S k).filter fun t => destination I a t = v).card :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = (localHighArrivals I a S k).card := by
      symm
      exact card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ internalCount I (localHighVertices I a S k) :=
      card_le_card (localHighArrivals_internal I a hg S hS k)
    _ ≤ opt I * (localHighVertices I a S k).card := by
      simpa [mul_comm] using density_le_opt I (localHighVertices I a S k)

theorem greedy_local_layers_decay (I : Instance V T) (a : Orientation T)
    (hg : IsGreedy I a) (S : Finset V) (hS : EdgeClosed I S)
    (hc : 0 < opt I) (j : ℕ) :
    2^j * (localHighVertices I a S (2*opt I*j)).card ≤ S.card := by
  induction j with
  | zero => simp [localHighVertices]
  | succ j ih =>
    have h := greedy_local_layer_bound I a hg S hS (2*opt I*j) (2*opt I)
    have hstep : 2 * (localHighVertices I a S (2*opt I*(j+1))).card ≤
        (localHighVertices I a S (2*opt I*j)).card := by
      have heq : 2*opt I*j + 2*opt I = 2*opt I*(j+1) := by ring
      rw [heq] at h
      nlinarith
    calc
      _ = 2^j * (2 * (localHighVertices I a S (2*opt I*(j+1))).card) := by
        rw [pow_succ]; ring
      _ ≤ 2^j * (localHighVertices I a S (2*opt I*j)).card := Nat.mul_le_mul_left _ hstep
      _ ≤ _ := ih

theorem greedy_load_lt_of_closed (I : Instance V T) (a : Orientation T)
    (hg : IsGreedy I a) (S : Finset V) (hS : EdgeClosed I S)
    (hT : 0 < T) (j : ℕ) (hj : S.card < 2^j) (v : V) (hv : v ∈ S) :
    load I a v < 2*opt I*j := by
  have hd := greedy_local_layers_decay I a hg S hS (opt_pos I hT) j
  by_contra h
  have hm : v ∈ localHighVertices I a S (2*opt I*j) := mem_filter.mpr ⟨hv, by omega⟩
  have hp := card_pos.mpr ⟨v, hm⟩
  have hh := Nat.mul_le_mul_left (2^j) (show 1 ≤ (localHighVertices I a S (2*opt I*j)).card by omega)
  omega

/-- Forget multiplicities only for connectivity. Loads still count all times. -/
def arrivalGraph (I : Instance V T) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ t, (I.left t = u ∧ I.right t = v) ∨
    (I.left t = v ∧ I.right t = u)
  symm := by
    intro u v h
    obtain ⟨hne, t, ht⟩ := h
    exact ⟨hne.symm, t, ht.symm⟩
  loopless := by intro u h; exact h.1 rfl

noncomputable def componentVertices (I : Instance V T) (v : V) : Finset V := by
  classical
  exact univ.filter fun w => (arrivalGraph I).Reachable v w

omit [DecidableEq V] in
theorem mem_componentVertices (I : Instance V T) (v w : V) :
    w ∈ componentVertices I v ↔ (arrivalGraph I).Reachable v w := by
  classical
  simp [componentVertices]

omit [DecidableEq V] in
theorem self_mem_componentVertices (I : Instance V T) (v : V) :
    v ∈ componentVertices I v :=
  (mem_componentVertices I v v).mpr (SimpleGraph.Reachable.refl v)

omit [Fintype V] in
theorem arrival_endpoints_reachable (I : Instance V T) (t : Fin T) :
    (arrivalGraph I).Reachable (I.left t) (I.right t) := by
  by_cases h : I.left t = I.right t
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h, t, Or.inl ⟨rfl, rfl⟩⟩

theorem componentVertices_closed (I : Instance V T) (v : V) :
    EdgeClosed I (componentVertices I v) := by
  intro t
  rw [mem_componentVertices, mem_componentVertices]
  have h := arrival_endpoints_reachable I t
  exact ⟨fun hv => hv.trans h, fun hv => hv.trans h.symm⟩

/-- Component-local Fact 3.6, benchmarked against the full arrival instance. -/
theorem greedy_component_competitive (I : Instance V T) (a : Orientation T)
    (hg : IsGreedy I a) (hT : 0 < T) (v : V) :
    load I a v < 2*opt I*(Nat.log 2 (componentVertices I v).card + 1) :=
  greedy_load_lt_of_closed I a hg _ (componentVertices_closed I v) hT _
    (Nat.lt_pow_succ_log_self (by decide) _) v (self_mem_componentVertices I v)

end GraphChoices
