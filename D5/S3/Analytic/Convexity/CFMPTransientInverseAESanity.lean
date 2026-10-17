import D5.S3.Analytic.Convexity.CFMPTransientInverseAE
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! Transient, uncompiled consumers. These are source probes, not test receipts. -/

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal

namespace CFMPInverseAE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Exercise the all-good branch: U = D = Ω = univ and the exceptional image is empty. -/
theorem sanity_all_good (μ : Measure E) [IsAddHaarMeasure μ] :
    ∀ᵐ y ∂μ, ∃ B : E →L[ℝ] E,
      HasFDerivAt (id : E → E) B y ∧
      ∀ u v, inner ℝ (B u) v = inner ℝ u (B v) := by
  have hMain := ae_symmetric_derivative_of_finite_exceptional_values
    (E := E) μ (D := univ) (Ω := univ) (U := univ)
    (F := fun _ => (0 : E)) (G := id) (K := 1)
    isOpen_univ LipschitzWith.id.lipschitzOnWith
    (by intro y hy; exact mem_univ _)
    (by intro y hy; simp)
    (by
      intro x hx
      refine ⟨0, hasFDerivAt_const (0 : E) x, ?_⟩
      intro u v
      simp)
    (by simp)
  simpa only [Measure.restrict_univ] using hMain

/-- With F = 0 and U empty, EVERY target is exceptional and its measure is positive.
The proof calls the original homeomorphism consumer, including its original premises. -/
theorem sanity_all_targets_exceptional {K : ℝ≥0}
    (hLip : LipschitzOnWith K (id : E → E) univ) :
    (∀ᵐ y ∂(volume : Measure E), ∃ B : E →L[ℝ] E,
      HasFDerivAt (id : E → E) B y ∧
      ∀ u v, inner ℝ (B u) v = inner ℝ u (B v)) ∧
    (univ \ ((fun x : E => x + (0 : E)) '' (∅ : Set E))) = univ ∧
    0 < (volume : Measure E) univ := by
  have hFinite : ((fun _ : E => (0 : E)) '' (univ \ (∅ : Set E))).Finite := by
    apply (Set.finite_singleton (0 : E)).subset
    rintro z ⟨x, _hx, rfl⟩
    exact mem_singleton 0
  have hMain := original_inverse_ae_symmetric_derivative
    (E := E) (D := univ) (Ω := univ) (U := ∅)
    (F := fun _ => (0 : E)) (G := id) (K := K)
    isOpen_univ isOpen_univ continuous_const.continuousOn
    (Homeomorph.refl (univ : Set E))
    (by intro x; simp)
    (by intro y; rfl)
    hLip isOpen_empty (empty_subset _)
    (by intro x hx; cases hx)
    hFinite
  refine ⟨?_, by simp, ?_⟩
  · simpa only [Measure.restrict_univ] using hMain
  · exact isOpen_univ.measure_pos (volume : Measure E) univ_nonempty

/-- Empty target, K = 0, and completely arbitrary ambient F and G. -/
theorem sanity_empty_target (μ : Measure E) [IsAddHaarMeasure μ] (F G : E → E) :
    ∀ᵐ y ∂μ.restrict (∅ : Set E), ∃ B : E →L[ℝ] E,
      HasFDerivAt G B y ∧ ∀ u v, inner ℝ (B u) v = inner ℝ u (B v) := by
  apply ae_symmetric_derivative_of_finite_exceptional_values
    μ (D := ∅) (Ω := ∅) (U := ∅) (F := F) (G := G) (K := 0)
    isOpen_empty (lipschitzOnWith_empty 0 G)
  · intro y hy
    cases hy
  · intro y hy
    cases hy
  · intro x hx
    cases hx
  · simp

/-- The zero-dimensional case admits K = 0 on a nonempty target. Its single point
has positive canonical volume; no step may discard this point as null. -/
theorem sanity_zero_dimension_K_zero [Subsingleton E] :
    LipschitzOnWith 0 (id : E → E) univ ∧
    ContinuousLinearMap.id ℝ E = 0 ∧
    (∀ᵐ y ∂(volume : Measure E), ∃ B : E →L[ℝ] E,
      HasFDerivAt (id : E → E) B y ∧
      ∀ u v, inner ℝ (B u) v = inner ℝ u (B v)) ∧
    0 < (volume : Measure E) ({0} : Set E) := by
  have hLip : LipschitzOnWith 0 (id : E → E) univ := by
    intro x hx y hy
    simp [Subsingleton.elim x y]
  have hMain := sanity_all_targets_exceptional hLip
  refine ⟨hLip, ?_, hMain.1, ?_⟩
  · ext v
    exact Subsingleton.elim _ _
  · have hUniv : (univ : Set E) = {0} := by
      ext x
      simp [Subsingleton.elim x (0 : E)]
    rw [← hUniv]
    exact hMain.2.2

end CFMPInverseAE
