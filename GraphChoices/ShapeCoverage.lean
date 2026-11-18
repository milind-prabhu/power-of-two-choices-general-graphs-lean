import GraphChoices.PatternCoverage

/-! A geometric embedding of an unlabelled canonical shape in the actual
residual graph forces the class-labelled shape event. Edge classes and
distinct occurrence witnesses are constructed from the actual execution.
-/
namespace GraphChoices.Patterns
open Finset
open ThresholdGreedy

abbrev UnlabelledShape (m : ℕ) := {t : Tree Unit // t ∈ Tree.treesOfNumNodesEq m}

def skeletonPattern {m : ℕ} (s : UnlabelledShape m) : ParentPattern Unit m :=
  shapePattern (s, fun _ => ())

variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C]
  [DecidableEq L] [DecidableEq R] [DecidableEq C] {T m : ℕ}

/-- The only input is an unlabelled geometric embedding. Classes, edge labels
and globally distinct occurrence witnesses follow from actual adjacency. -/
theorem mem_heavyShapeEvent_of_geometric_embedding (H : C → Peeling.Graph L R)
    (encode : E → Arrival L R C) (α : C → ℕ)
    (hsource : ∀ e, ((encode e).left, (encode e).right) ∈ H (encode e).cls)
    (ω : Fin T → E) (s : UnlabelledShape m) (f : Fin (m+1) → L ⊕ R)
    (hf : Function.Injective f) (hroot : ∃ v, f ⟨0, by omega⟩ = Sum.inr v)
    (hside : ∀ i, isLeft (f (childIndex i)) = (skeletonPattern s).childLeft i)
    (hadj : ∀ i, (arrivalGraph (residualInstance α (sampleArrivals encode ω))).Adj
      (f (childIndex i)) (f (parentIndex (skeletonPattern s) i)))
    (hheavy : m ≤ 2*(univ.filter fun i : Fin m => isLeft (f (childIndex i)) = true).card) :
    ω ∈ heavyShapeEvent H encode α T m := by
  classical
  have ht : ∀ i : Fin m, ∃ t : Fin T, residualTime α encode ω t ∧
      if (skeletonPattern s).childLeft i then
        f (childIndex i) = Sum.inl (encode (ω t)).left ∧
        f (parentIndex (skeletonPattern s) i) = Sum.inr (encode (ω t)).right
      else
        f (parentIndex (skeletonPattern s) i) = Sum.inl (encode (ω t)).left ∧
        f (childIndex i) = Sum.inr (encode (ω t)).right := by
    intro i
    obtain ⟨_, t, hres, hxy⟩ := (residual_adj_iff_time encode α ω _ _).mp (hadj i)
    refine ⟨t, hres, ?_⟩
    have hsi := hside i
    cases hs : (skeletonPattern s).childLeft i <;> simp only [hs, Bool.false_eq_true, if_false, if_true]
    · rcases hxy with hxy | hxy
      · rw [← hxy.1, hs] at hsi
        simp [isLeft] at hsi
      · exact ⟨hxy.1.symm, hxy.2.symm⟩
    · rcases hxy with hxy | hxy
      · exact ⟨hxy.1.symm, hxy.2.symm⟩
      · rw [← hxy.2, hs] at hsi
        simp [isLeft] at hsi
  choose τ hτ using ht
  let g : Fin m → E := fun i => ω (τ i)
  let labelled : ShapeCode C m := (s, fun i => (encode (g i)).cls)
  have he : EdgeData (shapePattern labelled) encode f g := by
    intro i
    exact ⟨rfl, (hτ i).2⟩
  have hp := mem_residualPatternEvent_of_data (shapePattern labelled) H encode α hsource
    ω f g hf hroot he (fun i => ⟨τ i, rfl, (hτ i).1⟩)
  have hheavy' : m ≤ 2*(univ.filter fun i : Fin m => (shapePattern labelled).childLeft i = true).card := by
    simpa only [hside] using hheavy
  apply mem_biUnion.mpr
  refine ⟨labelled, mem_univ _, ?_⟩
  simpa only [if_pos hheavy'] using hp

end GraphChoices.Patterns
