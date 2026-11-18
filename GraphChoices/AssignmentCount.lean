import GraphChoices.Model
import Mathlib.Data.Fin.Tuple.Basic

/-! Counting sequentially generated assignments by their available choices.
Menus may depend on every preceding choice. No independence is assumed. -/
namespace GraphChoices
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def appendChoice {n : ℕ} (f : Fin n → V) (v : V) : Fin (n+1) → V := Fin.snoc f v

noncomputable def menuAssignments (menu : (k : ℕ) → (Fin k → V) → Finset V) :
    (n : ℕ) → Finset (Fin n → V)
  | 0 => univ
  | n+1 => (menuAssignments menu n).biUnion fun f =>
      (menu n f).image fun v => appendChoice f v

def MenuValid (menu : (k : ℕ) → (Fin k → V) → Finset V) : (n : ℕ) → (Fin n → V) → Prop
  | 0, _ => True
  | n+1, f => MenuValid menu n (Fin.init f) ∧ f (Fin.last n) ∈ menu n (Fin.init f)

 theorem mem_menuAssignments_iff (menu : (k : ℕ) → (Fin k → V) → Finset V)
    (n : ℕ) (f : Fin n → V) : f ∈ menuAssignments menu n ↔ MenuValid menu n f := by
  classical
  induction n with
  | zero =>
    change f ∈ (univ : Finset (Fin 0 → V)) ↔ True
    simp only [mem_univ]
  | succ n ih =>
    simp only [menuAssignments, mem_biUnion, mem_image]
    constructor
    · rintro ⟨g,hg,v,hv,rfl⟩
      simp only [MenuValid, appendChoice, Fin.init_snoc, Fin.snoc_last]
      exact ⟨(ih g).mp hg,hv⟩
    · rintro ⟨hg,hv⟩
      exact ⟨Fin.init f,(ih _).mpr hg,f (Fin.last n),hv,Fin.snoc_init_self f⟩

/-- The number of complete assignments is at most the product of the menu
bounds, even though each menu can depend on the prefix. -/
 theorem menuAssignments_card_le (menu : (k : ℕ) → (Fin k → V) → Finset V)
    (d : ℕ → ℕ) (n : ℕ) (hmenu : ∀ k, k < n → ∀ f, (menu k f).card ≤ d k) :
    (menuAssignments menu n).card ≤ ∏ k ∈ range n, d k := by
  classical
  induction n with
  | zero => simp [menuAssignments]
  | succ n ih =>
    have hi := ih (fun k hk f => hmenu k (Nat.lt_succ_of_lt hk) f)
    rw [menuAssignments]
    calc
      _ ≤ ∑ f ∈ menuAssignments menu n, ((menu n f).image fun v => appendChoice f v).card := card_biUnion_le (s := menuAssignments menu n)
        (t := fun f : Fin n → V => (menu n f).image (appendChoice f))
      _ ≤ ∑ f ∈ menuAssignments menu n, d n := by
        apply sum_le_sum
        intro f _
        exact card_image_le.trans (hmenu n (by omega) f)
      _ = (menuAssignments menu n).card * d n := by simp
      _ ≤ (∏ k ∈ range n, d k) * d n := Nat.mul_le_mul_right _ hi
      _ = _ := (prod_range_succ _ _).symm

end GraphChoices
