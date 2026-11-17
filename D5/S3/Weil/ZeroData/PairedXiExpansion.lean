/- GID: D5/S3/Weil/ZeroData/PairedXiExpansion
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/PairedXiExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The paired xi expansion is an explicit convergent-series hypothesis off its poles. -/

import D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum
import D5.S3.Analytic.Laplace.PairedPoleRegularity
import D5.S3.Zeros.CompletedZeta

/-! The global paired xi expansion as an explicit convergent-series hypothesis. -/

set_option autoImplicit false

namespace D5.S3.Weil.ZeroData.PairedXiExpansion

open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Analytic.Laplace.PairedPoleRegularity (poleTerm)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum)
open D5.S3.Zeros.CompletedZeta (xiReading)

/-- Complex points avoiding both poles attached to each positive ordinate. -/
def PoleFree (S : Spectrum) : Set ℂ :=
  {s | ∀ j : S.index, s ≠ (S.gamma j : ℂ) * Complex.I ∧ s ≠ -((S.gamma j : ℂ) * Complex.I)}

/-- The symmetric Hadamard expansion, with convergence required by `HasSum`. -/
def PairedXiExpansion (hRH : RiemannHypothesis) : Prop :=
  ∀ s : ℂ, s ∈ PoleFree (zetaSpectrum hRH) →
    HasSum (fun j : (zetaSpectrum hRH).index => poleTerm (zetaSpectrum hRH) j s)
      (logDeriv xiReading ((1 / 2 : ℂ) + s))

end D5.S3.Weil.ZeroData.PairedXiExpansion
