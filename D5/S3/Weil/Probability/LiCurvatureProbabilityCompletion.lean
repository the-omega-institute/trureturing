/- GID: D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/LiCurvatureProbabilityCompletion
   mirror-E: none(waiver:analytic-proof-source)
   anchors: []
   utility: none
   digest: Reconstruct the entire original Li-type sequence from normalized positive curvature without assuming a Herglotz measure, and expose the remaining arithmetic input. -/

import D5.S3.Weil.Probability.CircleProbabilitySemigroup

/-!
This module consumes the pre-existing geometricPolynomial, reconstructedLi,
second-difference uniqueness and Li-curvature criterion. No alternate Li
coefficient sequence is introduced. Normalization c(0)=1 is an explicit source
condition needed for a probability measure; it was not a field of the older
conditional theorem. The canonical derivative-defined Li criterion and its RH
Fourier representation remain visible premises of the RH adapter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.LiCurvatureProbabilityCompletion

open MeasureTheory
open scoped ComplexOrder
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.Probability.CircleHerglotzCompletion
open D5.S3.Weil.Probability.CircleProbabilitySemigroup

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The same unique circle measure realizes every curvature moment and
reconstructs every term of the supplied original sequence. No representing
measure, Li positivity conclusion, or arithmetic criterion is assumed. -/
theorem normalized_curvature_reconstruction
    (c : ℤ → ℂ) (L : ℕ → ℝ)
    (normalized : c 0 = 1)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef)
    (zeroValue : L 0 = 0)
    (recurrence : ∀ n, 1 ≤ n →
      L (n + 1) - 2 * L n + L (n - 1) = 2 * L 1 * (c n).re) :
    ∃! μ : ProbabilityMeasure Circle,
      (∀ n : ℤ, circleMoment (μ : Measure Circle) n = c n) ∧
      (∀ n : ℕ, L n = reconstructedLi (μ : Measure Circle) (L 1) n) := by
  obtain ⟨μ, hμ, unique⟩ := (circle_herglotz_iff c normalized).mp positive
  have equality : reconstructedLi (μ : Measure Circle) (L 1) = L := by
    apply second_difference_recurrence_unique
      (reconstructedLi (μ : Measure Circle) (L 1)) L
      (fun n => 2 * L 1 * (c n).re)
    · rw [reconstructedLi_zero, zeroValue]
    · exact reconstructedLi_one _ _
    · intro n hn
      rw [reconstructedLi_second_difference _ _ n hn, hμ]
    · exact recurrence
  refine ⟨μ, ⟨hμ, fun n => (congrFun equality n).symm⟩, ?_⟩
  intro ν hν
  exact unique ν hν.1

/-- Positive normalized curvature and a nonnegative first coefficient imply
all original coefficients are nonnegative, through the constructed measure. -/
theorem normalized_curvature_forces_nonnegative
    (c : ℤ → ℂ) (L : ℕ → ℝ)
    (normalized : c 0 = 1)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef)
    (zeroValue : L 0 = 0) (firstNonnegative : 0 ≤ L 1)
    (recurrence : ∀ n, 1 ≤ n →
      L (n + 1) - 2 * L n + L (n - 1) = 2 * L 1 * (c n).re) :
    ∀ n : ℕ, 0 ≤ L n := by
  obtain ⟨μ, hμ, _⟩ :=
    normalized_curvature_reconstruction c L normalized positive zeroValue recurrence
  intro n
  rw [hμ.2 n]
  exact reconstructedLi_nonneg _ _ firstNonnegative n

/-- Supply the formerly external Herglotz premise of the existing Li-curvature
criterion from the new representation theorem. The arithmetic criterion,
actual recurrence and RH Fourier identification are still explicit. -/
theorem li_curvature_criterion_without_herglotz
    (c : ℤ → ℂ) (L : ℕ → ℝ) (normalized : c 0 = 1)
    (liCriterion : RiemannHypothesis ↔ ∀ n, 0 ≤ L n)
    (zeroValue : L 0 = 0) (firstNonnegative : 0 ≤ L 1)
    (recurrence : ∀ n, 1 ≤ n →
      L (n + 1) - 2 * L n + L (n - 1) = 2 * L 1 * (c n).re)
    (rhFourierRepresentation : RiemannHypothesis →
      ∃ μ : Measure Circle, IsProbabilityMeasure μ ∧ ∀ n, c n = circleMoment μ n) :
    RiemannHypothesis ↔ ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef := by
  apply li_curvature_criterion c L liCriterion zeroValue firstNonnegative
    recurrence rhFourierRepresentation
  intro positive
  obtain ⟨μ, hμ⟩ := circle_herglotz_exists c normalized positive
  exact ⟨μ, inferInstance, fun n => (hμ n).symm⟩

/-- If an actual circle probability measure represents the time-one Li
exponentials, its moment bound supplies the reverse RH implication via the
specified arithmetic criterion. Existence of that measure is not established
by this theorem, and arbitrary nonnegative sequences do not suffice. -/
theorem time_one_li_probability_implies_rh
    (L : ℕ → ℝ) (liCriterion : RiemannHypothesis ↔ ∀ n, 0 ≤ L n)
    (μ : ProbabilityMeasure Circle)
    (moments : ∀ n : ℤ,
      circleMoment (μ : Measure Circle) n = (Real.exp (-L n.natAbs) : ℂ)) :
    RiemannHypothesis := by
  apply liCriterion.mpr
  intro n
  have h := exponential_probability_forces_nonnegative
    (fun k : ℤ => L k.natAbs) μ moments (n : ℤ)
  simpa using h

#print axioms normalized_curvature_reconstruction
#print axioms normalized_curvature_forces_nonnegative
#print axioms li_curvature_criterion_without_herglotz
#print axioms time_one_li_probability_implies_rh

end D5.S3.Weil.Probability.LiCurvatureProbabilityCompletion
