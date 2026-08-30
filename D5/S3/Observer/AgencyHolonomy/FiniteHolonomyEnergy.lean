/- GID: D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite stable swap curvature aggregates into a faithful nonnegative energy. -/

import D5.S3.Observer.AgencyHolonomy.StableResidualSwapCurvatureBound
import Mathlib.Tactic

/-!
# Finite holonomy energy

A finite observer window carries one stable swap curvature for every ordered
pair of channels. Summing the squared norms produces a nonnegative scalar
energy. Its vanishing is faithful: the total is zero exactly when every
pairwise curvature vanishes.

The residual envelope theorem from
`StableResidualSwapCurvatureBound` gives a uniform pairwise bound. This module
aggregates that bound over a finite carrier and obtains the cardinal-square
estimate

`card ι ^ 2 * (2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2) ^ 2`.

This is a finite scalar precursor of a weighted Gram or Lyapunov energy. It
does not choose an infinite-prime normalization, prove residual decay, recover
observer origins at resonance, or compare prime-side energy with zero-side
spectral energy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy

open D5.S3.Observer.AgencyHolonomy.StableResidualSwapCurvatureBound

universe u v

variable {K : Type v} [NormedField K]

/-- The unnormalized finite ordered-pair energy of a curvature field. -/
noncomputable def finiteHolonomyEnergy
    {ι : Type u} [Fintype ι] (curvature : ι → ι → K) : ℝ :=
  ∑ p, ∑ q, ‖curvature p q‖ ^ 2

/-- The finite ordered-pair energy of stable residual swap curvature. -/
noncomputable def stableResidualHolonomyEnergy
    {ι : Type u} [Fintype ι]
    (stable : K) (residual channel : ι → K) : ℝ :=
  finiteHolonomyEnergy fun p q =>
    stableResidualSwapCurvature stable
      (residual p) (residual q) (channel p) (channel q)

/--
For a finite family of unit-bounded channels whose residual norms lie below a
common nonnegative envelope, stable holonomy energy is nonnegative and bounded
by the number of ordered pairs times the square of the pairwise envelope.
The energy vanishes exactly when every pairwise curvature vanishes. A zero
envelope therefore forces zero energy.
-/
theorem finite_stable_holonomy_energy_bound
    {ι : Type u} [Fintype ι]
    (stable : K) (residual channel : ι → K)
    (envelope : ℝ)
    (hEnvelope : 0 ≤ envelope)
    (hChannel : ∀ p, ‖channel p‖ ≤ 1)
    (hResidual : ∀ p, ‖residual p‖ ≤ envelope) :
    0 ≤ stableResidualHolonomyEnergy stable residual channel ∧
    stableResidualHolonomyEnergy stable residual channel ≤
      (Fintype.card ι : ℝ) ^ 2 *
        (2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2) ^ 2 ∧
    (stableResidualHolonomyEnergy stable residual channel = 0 ↔
      ∀ p q,
        stableResidualSwapCurvature stable
          (residual p) (residual q) (channel p) (channel q) = 0) ∧
    (envelope = 0 →
      stableResidualHolonomyEnergy stable residual channel = 0) := by
  classical
  let pairBound : ℝ :=
    2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2
  have hPairBoundNonnegative : 0 ≤ pairBound := by
    dsimp [pairBound]
    positivity
  have hPairBound (p q : ι) :
      ‖stableResidualSwapCurvature stable
          (residual p) (residual q) (channel p) (channel q)‖ ≤ pairBound := by
    have hPair :=
      stable_residual_swap_curvature_bound stable
        (residual p) (residual q) (channel p) (channel q)
        (hChannel p) (hChannel q)
    simpa [pairBound] using
      hPair.2.2 envelope hEnvelope (hResidual p) (hResidual q)
  have hEnergyNonnegative :
      0 ≤ stableResidualHolonomyEnergy stable residual channel := by
    unfold stableResidualHolonomyEnergy finiteHolonomyEnergy
    exact Finset.sum_nonneg fun p hp =>
      Finset.sum_nonneg fun q hq => sq_nonneg _
  have hEnergyBound :
      stableResidualHolonomyEnergy stable residual channel ≤
        (Fintype.card ι : ℝ) ^ 2 * pairBound ^ 2 := by
    unfold stableResidualHolonomyEnergy finiteHolonomyEnergy
    calc
      (∑ p : ι, ∑ q : ι,
          ‖stableResidualSwapCurvature stable
            (residual p) (residual q) (channel p) (channel q)‖ ^ 2) ≤
          ∑ _p : ι, ∑ _q : ι, pairBound ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact
          (sq_le_sq₀ (norm_nonneg _) hPairBoundNonnegative).2
            (hPairBound p q)
      _ = (Fintype.card ι : ℝ) ^ 2 * pairBound ^ 2 := by
        simp [pow_two] <;> ring
  have hZeroCriterion :
      stableResidualHolonomyEnergy stable residual channel = 0 ↔
        ∀ p q,
          stableResidualSwapCurvature stable
            (residual p) (residual q) (channel p) (channel q) = 0 := by
    constructor
    · intro hEnergyZero p q
      have hExpanded :
          (∑ i : ι, ∑ j : ι,
            ‖stableResidualSwapCurvature stable
              (residual i) (residual j) (channel i) (channel j)‖ ^ 2) = 0 := by
        simpa [stableResidualHolonomyEnergy, finiteHolonomyEnergy] using
          hEnergyZero
      have hOuterTermZero :
          (∑ j : ι,
            ‖stableResidualSwapCurvature stable
              (residual p) (residual j) (channel p) (channel j)‖ ^ 2) = 0 := by
        exact
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun i hi =>
              Finset.sum_nonneg fun j hj =>
                sq_nonneg
                  ‖stableResidualSwapCurvature stable
                    (residual i) (residual j) (channel i) (channel j)‖)).1
            hExpanded p (Finset.mem_univ p)
      have hInnerTermZero :
          ‖stableResidualSwapCurvature stable
            (residual p) (residual q) (channel p) (channel q)‖ ^ 2 = 0 := by
        exact
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j hj =>
              sq_nonneg
                ‖stableResidualSwapCurvature stable
                  (residual p) (residual j) (channel p) (channel j)‖)).1
            hOuterTermZero q (Finset.mem_univ q)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hInnerTermZero)
    · intro hCurvatureZero
      simp [stableResidualHolonomyEnergy, finiteHolonomyEnergy,
        hCurvatureZero]
  have hZeroEnvelope :
      envelope = 0 →
        stableResidualHolonomyEnergy stable residual channel = 0 := by
    intro hEnvelopeZero
    have hUpperZero :
        stableResidualHolonomyEnergy stable residual channel ≤ 0 := by
      simpa [pairBound, hEnvelopeZero] using hEnergyBound
    exact le_antisymm hUpperZero hEnergyNonnegative
  refine ⟨hEnergyNonnegative, ?_, hZeroCriterion, hZeroEnvelope⟩
  simpa [pairBound] using hEnergyBound

#print axioms finite_stable_holonomy_energy_bound

end D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy
