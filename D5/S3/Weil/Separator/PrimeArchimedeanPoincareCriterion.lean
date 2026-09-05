/- GID: D5/S3/Weil/Separator/PrimeArchimedeanPoincareCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/PrimeArchimedeanPoincareCriterion
   mirror-E: none(waiver:kernel-verified-poincare-criterion-only)
   anchors: []
   digest: Characterize RH by the Prime-Archimedean Poincare inequality. -/

import D5.S3.Weil.Separator.WeilSquarePositivityCriterion
import D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity
import D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
import D5.S3.Weil.Separator.ArchimedeanConvergence

/-!
# Prime-Archimedean Poincare criterion

The frozen Prime-Archimedean energy identity transports convolution-square
zero-sum positivity to a Poincare inequality at every support radius. Compact
support then supplies a radius for each repository `WeilTestFunction`, giving
the equivalent existential-radius formulation.

Both criteria are relative to supplied `ZeroData`. This module does not assert
that such data exists, so M1-b remains open and these equivalences are not a
proof of the Riemann hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.PrimeArchimedeanPoincareCriterion

open MeasureTheory Set
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.WeilIdentity
open D5.S3.Weil.Separator.ArchimedeanConvergence
open D5.S3.Weil.Separator.WeilSquarePositivityCriterion
open D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

noncomputable section

/-- Every repository Weil test function has a symmetric compact-support radius. -/
theorem exists_supportRadius (f : WeilTestFunction) :
    ∃ L : ℝ, tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-L) L := by
  obtain ⟨L, hL⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨L, ?_⟩
  simpa only [Real.closedBall_eq_Icc, zero_sub, zero_add] using hL

/-- Relative to supplied zero data, RH is equivalent to the Prime-Archimedean
Poincare inequality for every repository Weil test function and every real
radius containing its topological support. -/
theorem rh_iff_primeArchimedeanPoincare (Z : ZeroData) :
    RiemannHypothesis ↔
      ∀ (f : WeilTestFunction) (L : ℝ),
        tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-L) L →
          (2 * totalPrimeWeight L - archimedeanConstant) * l2Mass f ≤
            2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
              archimedeanJumpEnergy f + arithmeticJumpEnergy L f := by
  constructor
  · intro hRH f L hSupport
    let hZero := symmetricConvergent_of_zeroData Z (convolutionSquare f)
    have hPos : 0 ≤ (zeroSum Z (convolutionSquare f) hZero).re :=
      (rh_iff_weilSquarePositivity Z).mp hRH f hZero
    exact
      (prime_archimedean_energy_identity Z f L hSupport hZero
        (archimedeanConvergent_of_weilTestFunction (convolutionSquare f))).2.mp hPos
  · intro hPoincare
    apply (rh_iff_weilSquarePositivity Z).mpr
    intro f hZero
    obtain ⟨L, hSupport⟩ := exists_supportRadius f
    exact
      (prime_archimedean_energy_identity Z f L hSupport hZero
        (archimedeanConvergent_of_weilTestFunction (convolutionSquare f))).2.mpr
        (hPoincare f L hSupport)

/-- Relative to supplied zero data, RH is equivalent to the existence, for
each repository Weil test function, of a support radius at which the
Prime-Archimedean Poincare inequality holds. -/
theorem rh_iff_exists_supportRadius_primeArchimedeanPoincare (Z : ZeroData) :
    RiemannHypothesis ↔
      ∀ f : WeilTestFunction, ∃ L : ℝ,
        tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-L) L ∧
          (2 * totalPrimeWeight L - archimedeanConstant) * l2Mass f ≤
            2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
              archimedeanJumpEnergy f + arithmeticJumpEnergy L f := by
  constructor
  · intro hRH f
    obtain ⟨L, hSupport⟩ := exists_supportRadius f
    refine ⟨L, hSupport, ?_⟩
    exact (rh_iff_primeArchimedeanPoincare Z).mp hRH f L hSupport
  · intro hPoincare
    apply (rh_iff_weilSquarePositivity Z).mpr
    intro f hZero
    obtain ⟨L, hSupport, hInequality⟩ := hPoincare f
    exact
      (prime_archimedean_energy_identity Z f L hSupport hZero
        (archimedeanConvergent_of_weilTestFunction (convolutionSquare f))).2.mpr
        hInequality

-- The forward criterion supplies a checked witness for its full premise pattern.
example (Z : ZeroData) (hRH : RiemannHypothesis) :
    ∀ (f : WeilTestFunction) (L : ℝ),
      tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-L) L →
        (2 * totalPrimeWeight L - archimedeanConstant) * l2Mass f ≤
          2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
            archimedeanJumpEnergy f + arithmeticJumpEnergy L f :=
  (rh_iff_primeArchimedeanPoincare Z).mp hRH

-- The quantified domains and the compact-support conclusion have checked inhabitants.
example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : ∃ L : ℝ,
    tsupport (standardTestFunction : ℝ → ℂ) ⊆ Set.Icc (-L) L :=
  exists_supportRadius standardTestFunction

#print axioms exists_supportRadius
#print axioms rh_iff_primeArchimedeanPoincare
#print axioms rh_iff_exists_supportRadius_primeArchimedeanPoincare

end

end D5.S3.Weil.Separator.PrimeArchimedeanPoincareCriterion
