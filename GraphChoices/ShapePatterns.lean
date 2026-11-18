import GraphChoices.PatternDecay
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Bounds

/-! Canonical plane rooted patterns via first-child/next-sibling binary forests.
A forest with m nodes encodes the m non-root vertices of a rooted tree. There
are at most 4^m such shapes and |C|^m ways to label their edges. -/
namespace GraphChoices.Patterns
open Finset

/-- Parent-before-child indices from a first-child/next-sibling forest. The
extra parent p is outside the forest, at or before its starting position. -/
def forestParent : (t : Tree Unit) → (p start : ℕ) → p ≤ start →
    (i : Fin t.numNodes) → Fin (start+i.val+1)
  | .nil, _, _, _, i => Fin.elim0 i
  | .node _ l r, p, start, hp, i =>
    if hz : i.val = 0 then ⟨p,by omega⟩
    else if hl : i.val ≤ l.numNodes then
      let j : Fin l.numNodes := ⟨i.val-1,by omega⟩
      let q := forestParent l (start+1) (start+1) le_rfl j
      ⟨q.val,by have := q.isLt; dsimp [j] at this; omega⟩
    else
      let j : Fin r.numNodes := ⟨i.val-1-l.numNodes,by
        have hi := i.isLt
        simp only [Tree.numNodes] at hi
        omega⟩
      let q := forestParent r p (start+1+l.numNodes) (by omega) j
      ⟨q.val,by have := q.isLt; dsimp [j] at this; omega⟩

def forestSide : (t : Tree Unit) → Bool → Fin t.numNodes → Bool
  | .nil, _, i => Fin.elim0 i
  | .node _ l r, side, i =>
    if hz : i.val = 0 then side
    else if hl : i.val ≤ l.numNodes then
      forestSide l (!side) ⟨i.val-1,by omega⟩
    else
      forestSide r side ⟨i.val-1-l.numNodes,by
        have hi := i.isLt
        simp only [Tree.numNodes] at hi
        omega⟩

abbrev ShapeCode (C : Type*) (m : ℕ) :=
  {t : Tree Unit // t ∈ Tree.treesOfNumNodesEq m} × (Fin m → C)

def shapePattern {C : Type*} {m : ℕ} (s : ShapeCode C m) : ParentPattern C m where
  parent i :=
    let j : Fin s.1.val.numNodes := Fin.cast (Tree.mem_treesOfNumNodesEq.mp s.1.property).symm i
    let q := forestParent s.1.val 0 0 le_rfl j
    ⟨q.val,by simpa [j] using q.isLt⟩
  cls := s.2
  childLeft i := forestSide s.1.val true (Fin.cast (Tree.mem_treesOfNumNodesEq.mp s.1.property).symm i)

 theorem shapes_card_le (m : ℕ) : (Tree.treesOfNumNodesEq m).card ≤ 4^m := by
  rw [Tree.treesOfNumNodesEq_card_eq_catalan, catalan_eq_centralBinom_div]
  calc
    _ ≤ Nat.centralBinom m := Nat.div_le_self _ _
    _ ≤ 2^(2*m) := Nat.choose_le_two_pow _ _
    _ = _ := by rw [pow_mul]; norm_num

 theorem shapeCode_card_le {C : Type*} [Fintype C] [DecidableEq C] (m : ℕ) :
    Fintype.card (ShapeCode C m) ≤ 4^m * (Fintype.card C)^m := by
  simp only [ShapeCode, Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin]
  exact Nat.mul_le_mul_right _ (shapes_card_le m)

variable {E L R C : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  [Fintype L] [Fintype R] [Fintype C] [DecidableEq L] [DecidableEq R] [DecidableEq C]

/-- Union-bound over canonical plane-tree shapes and class labels. Only the
left-heavy patterns are retained; the per-pattern bound is a stated premise. -/
noncomputable def heavyShapeEvent (H : C → Peeling.Graph L R) (encode : E → ThresholdGreedy.Arrival L R C)
    (α : C → ℕ) (T m : ℕ) : Finset (Fin T → E) := by
  classical
  exact univ.biUnion fun s : ShapeCode C m =>
    if m ≤ 2*(univ.filter fun i : Fin m => (shapePattern s).childLeft i = true).card
    then residualPatternEvent (shapePattern s) H encode α T else ∅

 theorem heavyShape_probability_le (H : C → Peeling.Graph L R) (encode : E → ThresholdGreedy.Arrival L R C)
    (α : C → ℕ) (T m : ℕ) (N r : ℝ) (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hpattern : ∀ s : ShapeCode C m,
      m ≤ 2*(univ.filter fun i : Fin m => (shapePattern s).childLeft i = true).card →
      eventProbability (residualPatternEvent (shapePattern s) H encode α T) ≤ N*r^m) :
    eventProbability (heavyShapeEvent H encode α T m) ≤ N*(4*(Fintype.card C : ℝ)*r)^m := by
  classical
  calc
    _ ≤ ∑ s : ShapeCode C m, eventProbability
      (if m ≤ 2*(univ.filter fun i : Fin m => (shapePattern s).childLeft i = true).card
      then residualPatternEvent (shapePattern s) H encode α T else ∅) := witness_union_bound _ _
    _ ≤ ∑ _s : ShapeCode C m, N*r^m := by
      apply sum_le_sum
      intro s _
      split_ifs with h
      · exact hpattern s h
      · simpa [eventProbability] using mul_nonneg hN (pow_nonneg hr m)
    _ = (Fintype.card (ShapeCode C m) : ℝ)*(N*r^m) := by simp
    _ ≤ (4^m*(Fintype.card C)^m : ℕ)*(N*r^m) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hN (pow_nonneg hr m))
      exact_mod_cast shapeCode_card_le (C := C) m
    _ = _ := by push_cast; rw [mul_pow, mul_pow]; ring

end GraphChoices.Patterns
