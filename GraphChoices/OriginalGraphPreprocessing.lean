import GraphChoices.SourceRelabel

/-! The oriented vertex-copy construction as a concrete simple bipartite
edge set, together with its proved degree certificate and label bijection. -/
namespace GraphChoices
open Finset
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Nonempty E]

def orientedPair (G : BaseGraph V E) (b : E → Bool) (x : E) : V × V :=
  (if b x then G.left x else G.right x, if b x then G.right x else G.left x)

def splitGraph (G : BaseGraph V E) (b : E → Bool) : Peeling.Graph V V :=
  univ.image (orientedPair G b)

theorem orientedPair_injective (G : BaseGraph V E) (hsimple : G.IsSimple) (b : E → Bool) :
    Function.Injective (orientedPair G b) := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  cases hx : b x <;> cases hy : b y <;>
    simp only [orientedPair, hx, hy, Bool.false_eq_true, ↓reduceIte] at h1 h2
  · exact hsimple.2 x y (Or.inl ⟨h2,h1⟩)
  · exact hsimple.2 x y (Or.inr ⟨h2,h1⟩)
  · exact hsimple.2 x y (Or.inr ⟨h1,h2⟩)
  · exact hsimple.2 x y (Or.inl ⟨h1,h2⟩)

noncomputable def splitEdgeEquiv (G : BaseGraph V E) (hsimple : G.IsSimple) (b : E → Bool) :
    E ≃ splitGraph G b := Equiv.ofBijective
      (fun x => ⟨orientedPair G b x, mem_image.mpr ⟨x,mem_univ _,rfl⟩⟩)
      ⟨fun _ _ h => orientedPair_injective G hsimple b (congrArg Subtype.val h), by
        intro y
        obtain ⟨x,_,hx⟩ := mem_image.mp y.property
        exact ⟨x,Subtype.ext hx⟩⟩

theorem splitEdgeEquiv_left (G : BaseGraph V E) (hsimple : G.IsSimple) (b : E → Bool) (x : E) :
    (Peeling.graphBase (splitGraph G b)).left (splitEdgeEquiv G hsimple b x) = (G.split b).left x := rfl

theorem splitEdgeEquiv_right (G : BaseGraph V E) (hsimple : G.IsSimple) (b : E → Bool) (x : E) :
    (Peeling.graphBase (splitGraph G b)).right (splitEdgeEquiv G hsimple b x) = (G.split b).right x := rfl

theorem exists_preprocessed_split (G : BaseGraph V E) (hsimple : G.IsSimple) :
    ∃ b : E → Bool, ∀ u,
      Peeling.leftDegree (splitGraph G b) u ≤
        4*(Peeling.graphBase (splitGraph G b)).referenceCap := by
  classical
  obtain ⟨b,hb⟩ := exists_reference_source_orientation G
  refine ⟨b, fun u => ?_⟩
  let H := splitGraph G b
  let e := splitEdgeEquiv G hsimple b
  letI : Nonempty H := ⟨e (Classical.choice (inferInstance : Nonempty E))⟩
  have hc : (univ.filter fun x : E => (if b x then G.left x else G.right x) = u).card =
      (Peeling.leftBucket H u).card := by
    apply card_equiv e
    intro x
    simp only [Peeling.leftBucket, mem_filter, mem_univ, true_and]
    rfl
  have hleft : Peeling.leftDegree H u ≤ G.referenceCap := by
    rw [← Peeling.leftBucket_card, ← hc]
    exact hb u
  have hcap : (G.split b).referenceCap = (Peeling.graphBase H).referenceCap :=
    relabel_referenceCap (G.split b) (Peeling.graphBase H) e
      (splitEdgeEquiv_left G hsimple b) (splitEdgeEquiv_right G hsimple b)
  have hs := source_split_reference G b
  rw [hcap] at hs
  change Peeling.leftDegree H u ≤ 4*(Peeling.graphBase H).referenceCap
  omega

end GraphChoices
