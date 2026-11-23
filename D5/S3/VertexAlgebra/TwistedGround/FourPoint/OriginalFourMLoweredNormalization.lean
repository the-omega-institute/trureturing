/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMLoweredNormalization
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMLoweredNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank-24 determinant and native charge factors of the lowered Wick readout. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCompactLowering

/-! Isolate the native charge summand and its period determinant from the
signed spatial scales and the four lowered oscillator words. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMLoweredNormalization

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticePositiveEnergy (chargeEnergy)
open FourPoint.OriginalFourMActualChart
open OriginalFourMChartProduct (chartPeriod chartTau)
open OriginalFourMOccurrenceWick (liftedScale)
open OriginalFourMCompactLowering (loweredChargeTerm punctureLowering tagOscillators)
open OriginalFourMAssignmentPolynomial (affineReadout)
open OriginalFourMAssignedOccupation (compactCovariance compactMean)
open OriginalFourMSignedOverlap (chart_parameter_ne_one)
open D5.S3.Analytic.OriginalSlitNome (rank24Determinant slitNome)
open OriginalFourMDLipNome (dNome)
open private chartA_nome chartB_nome chart_charge from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
open private d_chart_charge from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
open private dDeterminant from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel

private def determinant (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A | .B => rank24Determinant (parameter c (x : ℂ))
  | .D => dDeterminant true (parameter .D (x : ℂ))

private def nome (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A | .B => slitNome (parameter c (x : ℂ))
  | .D => dNome true (parameter .D (x : ℂ))

open Classical in
/-- The literal charge-energy power and rank-24 determinant multiply the
weighted compact readout of the four original inverse lowering flows. -/
theorem lowered_charge_normalization {X : Type*} (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (hD : c = .D → upperA = true)
    (q : Charge D) (hq : 0 ≤ chargeEnergy D q) (n : X → ℕ) (l : List X)
    (F : Finset (Index D)) :
    loweredChargeTerm D slot colour upperA c x q n l F =
      (((1 - parameter c (x : ℂ)) ^ (3 : ℕ)) *
        (l.map fun a => liftedScale c x (slot a) (n a)).prod) *
        (determinant c x * nome c x ^ (chargeEnergy D q).toNat *
          affineReadout (compactCovariance D c x F) (compactMean D q c x F)
            (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
              tagOscillators D c i F (punctureLowering D c i
                ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))))) := by
  have he : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
      (bilinear D q q : ℂ) / 2) = nome c x ^ (chargeEnergy D q).toNat := by
    cases c with
    | A => exact chart_charge D q hq upperA .A x (chartA_nome upperA hx hx₁)
    | B => exact chart_charge D q hq upperA .B x (chartB_nome upperA hx hx₁)
    | D =>
      obtain rfl := hD rfl
      exact d_chart_charge D q hq hx hx₁
  have hp : determinant c x = ((1 - parameter c (x : ℂ)) ^ (3 : ℕ))⁻¹ *
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ := by
    cases c with
    | A => rfl
    | B => rfl
    | D =>
      obtain rfl := hD rfl
      rfl
  have hz : (1 - parameter c (x : ℂ)) ^ (3 : ℕ) ≠ 0 :=
    pow_ne_zero _ (chart_parameter_ne_one hx hx₁ c)
  rw [loweredChargeTerm, he, hp]
  generalize (1 - parameter c (x : ℂ)) ^ (3 : ℕ) = z at hz ⊢
  field_simp [hz]
  <;> ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMLoweredNormalization
