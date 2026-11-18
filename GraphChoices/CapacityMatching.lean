import GraphChoices.Model
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Prod

/-! The capacitated Hall step in Lemma 3.7. The expansion premise is explicit;
it is not assumed to hold for every graph. The preceding analytic module
proves the numerical rearrangement that supplies this premise from skewness. -/
namespace GraphChoices
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def neighbors (r : L → R → Prop) [DecidableRel r] (A : Finset L) : Finset R :=
  univ.filter fun v => ∃ u ∈ A, r u v

omit [DecidableEq L] in
/-- A capacity-b matching covering every left vertex. Capacities are integers. -/
 theorem exists_capacity_matching (r : L → R → Prop) [DecidableRel r] (b : ℕ)
    (hexpand : ∀ A : Finset L, A.card ≤ b * (neighbors r A).card) :
    ∃ f : L → R, (∀ u, r u (f u)) ∧
      ∀ v, (univ.filter fun u => f u = v).card ≤ b := by
  classical
  have hhall : ∀ A : Finset L,
      A.card ≤ (univ.filter fun p : R × Fin b => ∃ u ∈ A, r u p.1).card := by
    intro A
    have heq : (univ.filter fun p : R × Fin b => ∃ u ∈ A, r u p.1) =
        (neighbors r A) ×ˢ (univ : Finset (Fin b)) := by
      ext p
      simp [neighbors]
    rw [heq, card_product]
    simpa [mul_comm] using hexpand A
  let family (u : L) : Finset (R × Fin b) := univ.filter fun p => r u p.1
  have hfamily (A : Finset L) : A.biUnion family =
      (univ.filter fun p : R × Fin b => ∃ u ∈ A, r u p.1) := by
    ext p
    simp [family]
  obtain ⟨g, hginj, hg⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' family).mp
      (fun A => by rw [hfamily]; exact hhall A)
  simp only [family, mem_filter, mem_univ, true_and] at hg
  refine ⟨fun u => (g u).1, hg, ?_⟩
  intro v
  have hh := card_le_card_of_injOn (fun u : L => (g u).2)
    (s := univ.filter fun u => (g u).1 = v) (t := univ)
    (fun _ _ => mem_univ _)
    (by
      intro u hu w hw hslots
      apply hginj
      apply Prod.ext
      · exact (mem_filter.mp hu).2.trans (mem_filter.mp hw).2.symm
      · exact hslots)
  simpa using hh

end GraphChoices
