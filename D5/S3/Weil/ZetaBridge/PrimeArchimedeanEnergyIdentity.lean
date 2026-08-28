/- GID: D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Express the zero-side Weil form as boundary, Archimedean, and prime energies. -/

import D5.S3.Weil.WeilIdentity
import D5.S3.Weil.ZetaBridge.PoleRankOneDecomposition
import D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition

namespace D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity

open MeasureTheory Set
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.WeilIdentity
open D5.S3.Weil.ZetaBridge.PoleRankOneDecomposition
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

noncomputable section

/-- The zero-side explicit formula is the sum of its boundary, continuous-jump, and
finite arithmetic-jump energies minus the coherent mass threshold. Its nonnegativity is
equivalent to the corresponding Prime--Archimedean Poincare inequality. -/
theorem prime_archimedean_energy_identity
    (Z : ZeroData) (f : WeilTestFunction) (L : ℝ)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-L) L)
    (hZero : SymmetricConvergent Z (convolutionSquare f))
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    (zeroSum Z (convolutionSquare f) hZero =
      ((2 * Complex.normSq
          (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
        archimedeanJumpEnergy f + arithmeticJumpEnergy L f -
        (2 * totalPrimeWeight L - archimedeanConstant) * l2Mass f : ℝ) : ℂ)) ∧
    (0 ≤ (zeroSum Z (convolutionSquare f) hZero).re ↔
      (2 * totalPrimeWeight L - archimedeanConstant) * l2Mass f ≤
        2 * Complex.normSq
          (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
        archimedeanJumpEnergy f + arithmeticJumpEnergy L f) := by
  have hExplicit :=
    weil_explicit_formula Z (convolutionSquare f) hZero hArch
  have hPole := pole_rank_one_decomposition f
  have hPrime := (prime_jump_decomposition f L hSupport).1
  have hArchimedean := (archimedean_jump_decomposition f hArch).1
  have hIdentity :
      zeroSum Z (convolutionSquare f) hZero =
        ((2 * Complex.normSq
            (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
          archimedeanJumpEnergy f + arithmeticJumpEnergy L f -
          (2 * totalPrimeWeight L - archimedeanConstant) * l2Mass f : ℝ) : ℂ) := by
    rw [hExplicit, hPole, hPrime, hArchimedean]
    push_cast
    ring
  refine ⟨hIdentity, ?_⟩
  rw [hIdentity]
  simp only [Complex.ofReal_re]
  constructor <;> intro h <;> linarith

#print axioms prime_archimedean_energy_identity

end

end D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity
