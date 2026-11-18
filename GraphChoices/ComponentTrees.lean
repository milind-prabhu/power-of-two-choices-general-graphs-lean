import GraphChoices.ComponentGreedy
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Actual arrival components have spanning trees on exactly their vertex
sets. Every selected tree edge is backed by an original arrival occurrence.
Converting those trees to the counted canonical shape codes remains separate.
-/
namespace GraphChoices
variable {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}

omit [DecidableEq V] in
theorem componentVertices_coe_eq_supp (I : Instance V T) (v : V) :
    (componentVertices I v : Set V) = ((arrivalGraph I).connectedComponentMk v).supp := by
  ext w
  simp only [Finset.mem_coe, mem_componentVertices,
    SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
  exact SimpleGraph.reachable_comm

theorem component_induce_connected (I : Instance V T) (v : V) :
    ((arrivalGraph I).induce (componentVertices I v : Set V)).Connected := by
  rw [componentVertices_coe_eq_supp]
  exact SimpleGraph.ConnectedComponent.connected_toSimpleGraph _

/-- Spanning-tree extraction from an actual component, including its exact
vertex count. Edges inherit original occurrence times, with no sampling premise. -/
theorem exists_component_spanning_tree (I : Instance V T) (v : V) :
    ∃ H : SimpleGraph {w : V // w ∈ componentVertices I v},
      H.IsTree ∧
      (∀ x y, H.Adj x y → ∃ t : Fin T,
        (I.left t = x.val ∧ I.right t = y.val) ∨
        (I.left t = y.val ∧ I.right t = x.val)) ∧
      Fintype.card {w : V // w ∈ componentVertices I v} = (componentVertices I v).card := by
  classical
  obtain ⟨H, hle, htree⟩ := (component_induce_connected I v).exists_isTree_le
  refine ⟨H, htree, ?_, Fintype.card_coe _⟩
  intro x y hxy
  exact (hle hxy).2

end GraphChoices
