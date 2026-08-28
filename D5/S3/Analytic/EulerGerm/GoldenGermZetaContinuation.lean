/- GID: D5/S3/Analytic/EulerGerm/GoldenGermZetaContinuation
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermZetaContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The normalized product continues the golden germ to a larger half-plane. -/

/- Library-search audit trail (2026-08-26):
   * `GoldenGermZetaFactorization.golden_germ_zeta_factorization` is the
     frozen repository theorem supplying agreement on the original convergence
     half-plane, normalized absolute convergence, and real-axis positivity.
   * `GoldenLocalFactor.germLocalFactor` and `GoldenEulerBeta.o5Beta` are the
     canonical repository primitives for the local series and its spectrum.
   * Pinned Mathlib supplies the zeta Euler product used by the predecessor but
     has no theorem for this source-specific continued germ. -/

import D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization

namespace D5.S3.Analytic.EulerGerm.GoldenGermZetaContinuation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization

noncomputable section

/-- The zeta-normalized Euler product determines a unique continuation of the
golden germ to `Re s > 1 / phi^3`. It agrees with the canonical germ product
where that product converges, while retaining absolute convergence of the
normalized factors and strict positivity on the real ray. -/
theorem golden_germ_zeta_continuation :
    let G : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor s p
    (∃! continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 3 < s.re} -> Complex,
      (∀ s, 1 / Real.goldenRatio ^ 2 < s.1.re ->
        continuedGerm s = ∏' p : Nat.Primes, germLocalFactor s.1 p) ∧
      (∀ s, continuedGerm s =
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) * G s.1)) ∧
    (∀ s : Complex, 1 / Real.goldenRatio ^ 3 < s.re ->
      Summable (fun p : Nat.Primes =>
        ‖(1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor s p - 1‖)) ∧
    (∀ sigma : Real, 1 / Real.goldenRatio ^ 3 < sigma ->
      0 < (G (sigma : Complex)).re ∧ (G (sigma : Complex)).im = 0) := by
  dsimp only
  rcases golden_germ_zeta_factorization with ⟨hfactor, hconverges, hpositive⟩
  let continuedGerm :
      {s : Complex // 1 / Real.goldenRatio ^ 3 < s.re} -> Complex := fun s =>
    riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
      ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s.1 * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor s.1 p
  refine ⟨?_, hconverges, hpositive⟩
  refine ⟨continuedGerm, ?_, ?_⟩
  · constructor
    · intro s hs
      exact (hfactor s.1 hs).symm
    · intro s
      rfl
  · intro other hother
    funext s
    rw [hother.2 s]

#print axioms golden_germ_zeta_continuation

end

end D5.S3.Analytic.EulerGerm.GoldenGermZetaContinuation
