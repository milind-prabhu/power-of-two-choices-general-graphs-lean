import GraphChoices.CanonicalForest
import GraphChoices.AutomaticThresholds

/-! Coverage of every actual geometric heavy tree by the counted canonical
family. This discharges the hcoverage premise in the earlier conditional
shattering and expectation theorems. -/
namespace GraphChoices.Patterns
open Finset
open ThresholdGreedy
variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C]

theorem largeHeavyTree_subset_largeShape (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ)
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (T k : ℕ) :
    largeHeavyTreeEvent encode α T k ⊆
      largeShapeEvent H encode α T k (Fintype.card (L ⊕ R)) := by
  classical
  intro ω hω
  obtain ⟨v, s, G, htree, hadj, hlarge, hheavy, root, hroot⟩ := (mem_filter.mp hω).2
  letI : Fintype s := Fintype.ofFinite s
  let color : s → Bool := fun x => isLeft x.val.val
  have hcolor : ∀ x y, G.Adj x y → color x ≠ color y :=
    fun x y hxy => replay_adj_sides _ _ _ (hadj x y hxy)
  obtain ⟨m, shape, e, hsize, heroot, hspec⟩ :=
    exists_canonical_embedding G htree.isConnected color hcolor root hroot
  let f : Fin (m+1) → L ⊕ R := fun i => (e i).val.val
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.injective)
  have hroot' : ∃ w, f ⟨0, by omega⟩ = Sum.inr w := by
    change ∃ w, (e ⟨0, by omega⟩).val.val = Sum.inr w
    rw [heroot]
    cases hr : root.val.val with
    | inl u => simp [hr, isLeft] at hroot
    | inr w => exact ⟨w, rfl⟩
  have hside : ∀ i, isLeft (f (childIndex i)) = (skeletonPattern shape).childLeft i :=
    fun i => (hspec i).2
  have hedge : ∀ i, (arrivalGraph (residualInstance α (sampleArrivals encode ω))).Adj
      (f (childIndex i)) (f (parentIndex (skeletonPattern shape) i)) :=
    fun i => hadj _ _ (hspec i).1
  have hsize' : m+1 = Nat.card s := by simpa only [Nat.card_eq_fintype_card] using hsize
  have hpart : Nat.card {x : s // color x = true} + Nat.card {x : s // color x = false} = Nat.card s := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using bool_partition_card color
  have hcount := left_index_card m e color (by rw [heroot]; exact hroot)
  have hleft : m ≤ 2*(univ.filter fun i : Fin m => isLeft (f (childIndex i)) = true).card := by
    change m ≤ 2*(univ.filter fun i : Fin m => color (e (childIndex i)) = true).card
    rw [hcount]
    change Nat.card {x : s // color x = false}+1 ≤ Nat.card {x : s // color x = true} at hheavy
    omega
  have hshape := mem_heavyShapeEvent_of_geometric_embedding H encode α hsource
    ω shape f hf hroot' hside hedge hleft
  have hk : k ≤ m := by omega
  have hbound : m+1 ≤ Fintype.card (L ⊕ R) := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  change ω ∈ (range (Fintype.card (L ⊕ R)+1)).biUnion (fun j => heavyShapeEvent H encode α T (k+j))
  apply mem_biUnion.mpr
  refine ⟨m-k, mem_range.mpr (by omega), ?_⟩
  have heq : k+(m-k) = m := by omega
  simpa only [heq] using hshape

/-- Actual component shattering for concrete automatic thresholds. There is
no canonical-coverage or per-shape probability premise in this theorem. -/
theorem largeComponent_polynomial_automatic (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D T d k N c : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (hT : 0 < T) (hf : ∀ c, 1 < f c)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N)
    (hd : polynomialCutoff N c ≤ d+1) (hk : polynomialCutoff N c ≤ k)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(d+1) ≤ 1/2) :
    eventProbability (largeComponentEvent encode (automaticThresholds (E := E) DL DR D T f)
      T ((d+1)*(k+1))) ≤ 3/(N:ℝ)^c := by
  apply largeComponent_polynomial_automatic_of_coverage H encode DL DR D T d k
    (Fintype.card (L ⊕ R)) N c f hsimple hDL hL hR hT hf hN hLN hRN hd hk hmean
  exact largeHeavyTree_subset_largeShape H encode _ hsource T k

theorem expected_load_polynomial_automatic (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (DL DR : C → ℕ) (D T d k N c : ℕ) (f : C → ℝ)
    (hsimple : Function.Injective fun e => ((encode e).left,(encode e).right))
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (hDL : ∀ u c, (sourceBucket encode u c).card ≤ DL c)
    (hL : ∀ c u, Peeling.leftDegree (H c) u ≤ D)
    (hR : ∀ c v, Peeling.rightDegree (H c) v ≤ DR c)
    (hT : 0 < T) (hf : ∀ c, 1 < f c)
    (hN : 0 < N) (hLN : Fintype.card L ≤ N) (hRN : Fintype.card R ≤ N)
    (hd : polynomialCutoff N c ≤ d+1) (hk : polynomialCutoff N c ≤ k)
    (hmean : ∀ u, Real.exp 1*T*(((leftSourceBucket encode u).card : ℝ)/Fintype.card E)/(d+1) ≤ 1/2) :
    expectedTotalMaxLoad encode (automaticThresholds (E := E) DL DR D T f) T ≤
      (∑ a, (automaticThresholds (E := E) DL DR D T f a : ℝ)) +
      (2*(Nat.log 2 ((d+1)*(k+1))+1) : ℕ)*expectedReplayOpt encode T + 3*T/(N:ℝ)^c := by
  apply expected_load_polynomial_automatic_of_coverage H encode DL DR D T d k
    (Fintype.card (L ⊕ R)) N c f hsimple hDL hL hR hT hf hN hLN hRN hd hk hmean
  exact largeHeavyTree_subset_largeShape H encode _ hsource T k

end GraphChoices.Patterns
