import GraphChoices.Peeling
import GraphChoices.SkewExpansion
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Positivity

/-! A finite maximum log-skewness over actual bipartite subgraphs, and the
bridge from this parameter to hereditary expansion and terminating peeling.
Admissibility explicitly excludes zero degrees and nonpositive log denominators.
-/
namespace GraphChoices.Peeling
open Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

noncomputable def minLeftDegree (F : Graph L R) (A : Finset L) : ℕ :=
  if h : A.Nonempty then A.inf' h (leftDegree F) else 0

 theorem minLeftDegree_le (F : Graph L R) {A : Finset L} {u : L} (hu : u ∈ A) :
    minLeftDegree F A ≤ leftDegree F u := by
  rw [minLeftDegree, dif_pos ((show A.Nonempty from ⟨u,hu⟩))]
  exact inf'_le _ hu

 theorem le_minLeftDegree (F : Graph L R) {A : Finset L} (hA : A.Nonempty)
    (k : ℕ) (hk : ∀ u ∈ A, k ≤ leftDegree F u) : k ≤ minLeftDegree F A := by
  rw [minLeftDegree, dif_pos hA]
  exact le_inf' hA (leftDegree F) hk

def neighborSet (F : Graph L R) (A : Finset L) : Finset R :=
  GraphChoices.neighbors (fun u v => (u,v) ∈ F) A

noncomputable def skewValue (F : Graph L R) (A : Finset L) (d n : ℝ) : ℝ :=
  GraphChoices.localLogSkewness A.card (neighborSet F A).card (minLeftDegree F A) d n

noncomputable def SkewAdmissible (F : Graph L R) (A : Finset L) (d n : ℝ) : Prop :=
  A.Nonempty ∧ (neighborSet F A).Nonempty ∧ (neighborSet F A).card ≤ A.card ∧
    0 < minLeftDegree F A ∧ 1 < d * (Real.log n)^2 / minLeftDegree F A

noncomputable def skewValues (G : Graph L R) (d n : ℝ) : Finset ℝ := by
  classical
  exact insert 0 (((G.powerset ×ˢ (univ : Finset L).powerset).filter
    fun p => SkewAdmissible p.1 p.2 d n).image fun p => skewValue p.1 p.2 d n)

noncomputable def graphLogSkewness (G : Graph L R) (d n : ℝ) : ℝ :=
  (skewValues G d n).sup' (by
    classical
    simp [skewValues]) id

 theorem graphLogSkewness_nonneg (G : Graph L R) (d n : ℝ) :
    0 ≤ graphLogSkewness G d n := by
  classical
  unfold graphLogSkewness
  exact le_sup' id (by simp [skewValues])

 theorem skewValue_le_graphLogSkewness {G F : Graph L R} (hF : F ⊆ G)
    (A : Finset L) (d n : ℝ) (ha : SkewAdmissible F A d n) :
    skewValue F A d n ≤ graphLogSkewness G d n := by
  classical
  unfold graphLogSkewness
  apply le_sup' id
  apply mem_insert_of_mem
  apply mem_image.mpr
  refine ⟨(F,A), ?_, rfl⟩
  simp [hF, ha]

noncomputable def scaleCapacity (G : Graph L R) (d n f : ℝ) : ℕ :=
  ⌈(f * Real.log n)^(2 * graphLogSkewness G d n)⌉₊

 theorem scaleCapacity_pos (G : Graph L R) (d n f : ℝ)
    (hf : 1 ≤ f) (hn : 1 < Real.log n) : 1 ≤ scaleCapacity G d n f := by
  have hb : 1 ≤ f * Real.log n := by nlinarith
  have hp : (1:ℝ) ≤ (f * Real.log n)^(2 * graphLogSkewness G d n) :=
    Real.one_le_rpow hb (mul_nonneg (by norm_num) (graphLogSkewness_nonneg G d n))
  have hc := Nat.le_ceil ((f * Real.log n)^(2 * graphLogSkewness G d n))
  exact_mod_cast hp.trans hc

/-- Bounded log-skewness supplies the actual Hall expansion premise in every
residual graph. The left-degree hypothesis is the preprocessing degree bound. -/
 theorem peelingExpansion_of_graphLogSkewness (G : Graph L R) (k : ℕ) (d n f : ℝ)
    (hd : 0 < d) (hf : 1 ≤ f) (hn : 1 < Real.log n)
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d * Real.log n)
    (hcut : d / f^2 ≤ (k+1 : ℕ)) :
    PeelingExpansion G k (scaleCapacity G d n f) := by
  classical
  intro F hF A hA
  by_cases hAempty : A = ∅
  · simp [hAempty]
  have hAne : A.Nonempty := nonempty_iff_ne_empty.mpr hAempty
  have hkmin : k+1 ≤ minLeftDegree F A :=
    le_minLeftDegree F hAne (k+1) (fun u hu => hA u hu)
  have hmin : 0 < minLeftDegree F A := by omega
  obtain ⟨u, hu⟩ := hAne
  have hAne : A.Nonempty := ⟨u,hu⟩
  have hdmin : (0:ℝ) < minLeftDegree F A := by exact_mod_cast hmin
  have hminmax : (minLeftDegree F A : ℝ) ≤ d * Real.log n := by
    have hh := (minLeftDegree_le F hu).trans (leftDegree_mono hF u)
    have hreal : (minLeftDegree F A : ℝ) ≤ leftDegree G u := by exact_mod_cast hh
    exact hreal.trans (hleft u)
  have hden : 1 < d * (Real.log n)^2 / minLeftDegree F A := by
    apply (lt_div_iff₀ hdmin).mpr
    have hh : d * Real.log n < d * (Real.log n)^2 := by
      nlinarith [mul_pos hd (mul_pos (by linarith : 0 < Real.log n) (by linarith : 0 < Real.log n - 1))]
    linarith
  have hNne : (neighborSet F A).Nonempty := by
    have hdu : 0 < leftDegree F u := (Nat.zero_le k).trans_lt (hA u hu)
    obtain ⟨v,hv⟩ := card_pos.mp hdu
    refine ⟨v, ?_⟩
    simp only [leftNeighbors, mem_filter, mem_univ, true_and] at hv
    simp only [neighborSet, GraphChoices.neighbors, mem_filter, mem_univ, true_and]
    exact ⟨u,hu,hv⟩
  by_cases hbal : A.card ≤ (neighborSet F A).card
  · have hcap := scaleCapacity_pos G d n f hf hn
    change A.card ≤ scaleCapacity G d n f * (neighborSet F A).card
    exact hbal.trans (by nlinarith)
  · have hadm : SkewAdmissible F A d n :=
      ⟨hAne, hNne, by omega, hmin, hden⟩
    have hskew := skewValue_le_graphLogSkewness hF A d n hadm
    have hdeg : d / f^2 ≤ (minLeftDegree F A : ℝ) :=
      hcut.trans (by exact_mod_cast hkmin)
    have hexp := GraphChoices.expansion_at_scale
      (a := (A.card : ℝ)) (b := ((neighborSet F A).card : ℝ))
      (d := (minLeftDegree F A : ℝ)) (D := d) (n := n) (f := f)
      (by exact_mod_cast hAne.card_pos) (by exact_mod_cast hNne.card_pos) hdmin
      (by linarith) (by linarith) (graphLogSkewness_nonneg G d n) hdeg hden hskew
    have hceil := Nat.le_ceil ((f * Real.log n)^(2 * graphLogSkewness G d n))
    have hbnonneg : (0:ℝ) ≤ (neighborSet F A).card := Nat.cast_nonneg _
    have hh := hexp.trans (mul_le_mul_of_nonneg_left hceil hbnonneg)
    change A.card ≤ scaleCapacity G d n f * (neighborSet F A).card
    rw [Nat.mul_comm]
    exact_mod_cast hh

/-- One full extraction round, including finite termination, derived from the
maximum over concrete log-skewness witnesses. -/
 theorem exists_graph_skew_piece (G : Graph L R) (k D : ℕ) (d n f : ℝ)
    (hd : 0 < d) (hf : 1 ≤ f) (hn : 1 < Real.log n)
    (hleft : ∀ u, (leftDegree G u : ℝ) ≤ d * Real.log n)
    (hcut : d / f^2 ≤ (k+1 : ℕ)) (hD : ∀ u, leftDegree G u ≤ D) :
    ∃ P : Graph L R, P ⊆ G ∧
      (∀ u, leftDegree (G \ P) u ≤ k) ∧
      (∀ v, rightDegree P v ≤ D * scaleCapacity G d n f) := by
  exact exists_peeling_piece G k _ D hD
    (peelingExpansion_of_graphLogSkewness G k d n f hd hf hn hleft hcut)

end GraphChoices.Peeling
