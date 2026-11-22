/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSparseZeroPhaseAlignment
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSparseZeroPhaseAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse omitted positive zeta ordinates give full weighted phase alignment and the signed-window coefficient. -/

import D5.S3.Analytic.Oscillation.SparseOrdinateMass
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedPhaseLimsup
import D5.S3.Fourier.WeightedPhaseRelationLattice

/-! Application to the actual positive zeta ordinates and analytic multiplicities. -/

set_option autoImplicit false

open Filter Set ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum)
open D5.S3.Analytic.Oscillation.SparseOrdinateMass (cutoffSum harmonicMass_tendsto_zero)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

noncomputable section

/-- Omitted positive zeta zeros through the same inclusive cutoff as the full mass. -/
def omittedCutoff (hRH : RiemannHypothesis) (S : Set ℝ) (T : ℝ) :
    Finset PositiveZetaZero := by
  classical
  exact (positiveCutoff hRH T).filter (fun j => ordinate j ∉ S)

/-- The original multiplicities of omitted positive zeta zeros. -/
def omittedCount (hRH : RiemannHypothesis) (S : Set ℝ) (T : ℝ) : ℕ :=
  ∑ j ∈ omittedCutoff hRH S T, Zeta23.zeroMult j.val

/-- The original harmonic weights of omitted positive zeta zeros. -/
def omittedMass (hRH : RiemannHypothesis) (S : Set ℝ) (T : ℝ) : ℝ :=
  ∑ j ∈ omittedCutoff hRH S T, harmonicWeight j

/-- A sparse omitted multiplicity count gives vanishing harmonic mass on the squared logarithmic scale. -/
theorem omittedMass_tendsto_zero (hRH : RiemannHypothesis) (S : Set ℝ)
    (hcount : Tendsto (fun T : ℝ => (omittedCount hRH S T : ℝ) / (T * Real.log T))
      atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => omittedMass hRH S T / Real.log T ^ 2) atTop (𝓝 0) := by
  classical
  let m (j : PositiveZetaZero) := if ordinate j ∉ S then Zeta23.zeroMult j.val else 0
  let finite_le : ∀ T : ℝ, {j : PositiveZetaZero | ordinate j ≤ T}.Finite :=
    (zetaSpectrum hRH).finite_le
  have count_eq (T : ℝ) :
      (omittedCount hRH S T : ℝ) = cutoffSum ordinate finite_le (fun j => (m j : ℝ)) T := by
    rw [omittedCount, Nat.cast_sum, omittedCutoff, Finset.sum_filter]
    change (∑ j ∈ positiveCutoff hRH T,
      if ordinate j ∉ S then (Zeta23.zeroMult j.val : ℝ) else 0) =
      ∑ j ∈ positiveCutoff hRH T, (m j : ℝ)
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ordinate j ∈ S <;> simp [m, hj]
  have mass_eq (T : ℝ) :
      omittedMass hRH S T = cutoffSum ordinate finite_le
        (fun j => (m j : ℝ) * ordinate j / (1 / 4 + ordinate j ^ 2)) T := by
    rw [omittedMass, omittedCutoff, Finset.sum_filter]
    change (∑ j ∈ positiveCutoff hRH T,
      if ordinate j ∉ S then harmonicWeight j else 0) =
      ∑ j ∈ positiveCutoff hRH T, (m j : ℝ) * ordinate j / (1 / 4 + ordinate j ^ 2)
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ordinate j ∈ S <;> simp [m, hj, harmonicWeight]
  simp_rw [count_eq] at hcount
  simp_rw [mass_eq]
  exact harmonicMass_tendsto_zero ordinate m finite_le (fun j => j.property.2) hcount

