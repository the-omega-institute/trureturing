/- GID: D5/S3/Analytic/EulerGerm/GoldenGermProductAbscissa
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermProductAbscissa
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Explicit golden Euler exponent, prime product, and exact convergence boundary. -/

import D5.S3.Analytic.EulerGerm.GermProductConvergence

/- Search audit (2026-08-26):
   * Repository body-shape searches found the canonical exponent `o5Beta`, local
     factor `germLocalFactor`, excited spectrum `goldenSpectrum`, and strict-side
     abscissa theorem `golden_heat_abscissa`; they are reused here.
   * No frozen declaration packages the exponent formula, its first two values,
     the endpoint divergence, and the explicit convergent prime product in one
     public statement.
   * Pinned Mathlib supplies `Nat.Primes.summable_rpow` and the infinite-product
     convergence API, but no exact theorem for this exponent family. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermProductAbscissa

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GermProductConvergence
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Midline.GoldenHeatSpectrum

noncomputable section

/-- The golden exponent is explicit, begins with the second and third golden
powers, and gives a prime-local Euler product whose absolute convergence holds
exactly to the right of `1 / phi^2`. -/
theorem golden_germ_product_abscissa :
    (forall v : Nat,
      o5Beta v = Real.sqrt 5 * (v : Real) + 1 / Real.goldenRatio -
        Int.fract (((v + 1 : Nat) : Real) * Real.goldenRatio)) /\
      o5Beta 1 = Real.goldenRatio ^ 2 /\
      o5Beta 2 = Real.goldenRatio ^ 3 /\
      (forall sigma : Real,
        Summable (fun q : Nat.Primes × Nat =>
          Real.exp (-sigma * goldenSpectrum q)) <->
            1 / Real.goldenRatio ^ 2 < sigma) /\
      (forall s : Complex, 1 / Real.goldenRatio ^ 2 < s.re ->
        HasProd
          (fun p : Nat.Primes =>
            ∑' v : Nat, (p : Complex) ^ (-s * (o5Beta v : Complex)))
          (∏' p : Nat.Primes,
            ∑' v : Nat, (p : Complex) ^ (-s * (o5Beta v : Complex)))) := by
  refine ⟨o5_beta_closed_form, o5_beta_power_law.1,
    o5_beta_power_law.2.1, ?_, ?_⟩
  · intro sigma
    constructor
    · intro hsum
      by_contra hcritical
      have hsigma : sigma ≤ 1 / Real.goldenRatio ^ 2 := le_of_not_gt hcritical
      rcases hsigma.lt_or_eq with hbelow | rfl
      · exact (golden_heat_abscissa.2 sigma hbelow) hsum
      · have hsub : Summable (fun p : Nat.Primes =>
            Real.exp (-(1 / Real.goldenRatio ^ 2) *
              goldenSpectrum (p, 0))) :=
          hsum.comp_injective (fun _ _ h => congrArg Prod.fst h)
        have hbeta : o5Beta 1 = Real.goldenRatio ^ 2 :=
          o5_beta_power_law.1
        have hprime : Summable (fun p : Nat.Primes =>
            (p : Real) ^ (-1 : Real)) := by
          refine hsub.congr fun p => ?_
          rw [goldenSpectrum, Nat.zero_add, hbeta,
            Real.rpow_def_of_pos (by exact_mod_cast p.prop.pos)]
          have hphi : Real.goldenRatio ^ 2 ≠ 0 :=
            pow_ne_zero 2 Real.goldenRatio_ne_zero
          field_simp [hphi]
        have himpossible : (-1 : Real) < -1 :=
          Nat.Primes.summable_rpow.mp hprime
        exact (lt_irrefl (-1 : Real)) himpossible
    · exact golden_heat_abscissa.1 sigma
  · intro s hs
    simpa [germLocalFactor] using
      (germLocalFactor_multipliable s hs).hasProd

end

end D5.S3.Analytic.EulerGerm.GoldenGermProductAbscissa
