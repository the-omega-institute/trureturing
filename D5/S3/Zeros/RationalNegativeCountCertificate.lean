/- GID: D5/S3/Zeros/RationalNegativeCountCertificate
   generality: G
   mirror-B: D5/B/S3/Zeros/RationalNegativeCountCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonempty open negative-count region contains a rational parameter certificate. -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Constructions.SumProd

/- Library-search audit trail (2026-09-05):
   * Repository searches for rational negative-count certificates, moving
     observation scales, radial logarithmic derivatives, and generalized
     open-set witness extraction found no owner of this statement.
   * The closest rational-density result in D5 is
     `CountableNormalJetCriterion.continuous_nonnegative_iff_rat`; it extends a
     closed condition in one variable and does not extract a two-parameter
     witness from an open region.
   * Pinned Mathlib supplies `Rat.denseRange_cast`, `DenseRange.prodMap`, and
     `DenseRange.exists_mem_open`; the proof below uses them directly.
   * The source does not provide the analytic implication from failure of RH
     to a nonempty negative-count region, nor hypotheses from which openness
     can be derived. Both missing bridge facts are explicit premises here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.RationalNegativeCountCertificate

/-- The scale-weighted radial derivative of the logarithm of a two-parameter
counting profile. -/
noncomputable def radialLogDerivative (Q : ℝ → ℝ → ℝ) (q r : ℝ) : ℝ :=
  r * deriv (fun u : ℝ => Real.log (Q q u)) r

/-- The region where the scale and counting profile are positive while the
scale-weighted logarithmic derivative is negative. -/
def negativeCountRegion (Q : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ 0 < Q p.1 p.2 ∧ radialLogDerivative Q p.1 p.2 < 0}

/-- If failure of RH produces a point in an open negative-count region, then
it produces such a certificate at rational observation and scale parameters. -/
theorem rational_negative_count_certificate
    (RH : Prop) (Q : ℝ → ℝ → ℝ)
    (hOpen : IsOpen (negativeCountRegion Q))
    (hFailure : ¬RH → (negativeCountRegion Q).Nonempty) :
    ¬RH →
      ∃ q r : ℚ,
        0 < (r : ℝ) ∧
        0 < Q (q : ℝ) (r : ℝ) ∧
        radialLogDerivative Q (q : ℝ) (r : ℝ) < 0 := by
  intro hNotRH
  have hDense :
      DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  obtain ⟨p, hp⟩ := hDense.exists_mem_open hOpen (hFailure hNotRH)
  exact ⟨p.1, p.2, by simpa [negativeCountRegion] using hp⟩

#print axioms rational_negative_count_certificate

end D5.S3.Zeros.RationalNegativeCountCertificate
