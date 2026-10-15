/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTargetTheta
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTargetTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All original source and target states satisfy target theta conjugation. -/

import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaNormal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockTargetTheta

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection LatticeHalfFockFockNormalField
open LatticeHalfFockAllStateField LatticeHalfFockTargetThetaCoefficients
open LatticeHalfFockTargetThetaNormal LatticeInvolution

noncomputable section

theorem Corr_reflection (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (shift : ℕ) :
    Corr D (-charge) (sigma D polynomial) shift = sigma D (Corr D charge polynomial shift) := by
  run_tac
    let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy 0).append
      `D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy.Corr_sign
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _ _ _ _))

theorem sigmaTensor_correctionSum (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (corrections : ℕ →₀ Oscillator D) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    sigmaTensor D hu ((Finsupp.lsum ℂ (fun shift : ℕ =>
        (shiftLinear D hu shift).comp (normalPolynomial D hu charge)) corrections).coeff
          exponent vector) =
      (Finsupp.lsum ℂ (fun shift : ℕ =>
        (shiftLinear D hu shift).comp (normalPolynomial D hu (-charge)))
          (Finsupp.mapRange.linearMap (sigmaLinear D) corrections)).coeff exponent
            (sigmaTensor D hu vector) := by
  induction corrections using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, firstProof, secondProof]
  | single shift polynomial =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Finsupp.lsum_single, LinearMap.comp_apply]
    change sigmaTensor D hu ((shiftField D hu shift
      (normalPolynomial D hu charge polynomial)).coeff exponent vector) =
      (shiftField D hu shift (normalPolynomial D hu (-charge)
        (sigma D polynomial))).coeff exponent (sigmaTensor D hu vector)
    simp only [shiftField, HVertexOperator.coeff_of_coeff]
    exact sigmaTensor_normalPolynomial D hu charge polynomial (exponent + 2 * shift) vector

theorem sigmaTensor_correctedPolynomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    sigmaTensor D hu ((correctedPolynomial D hu charge polynomial).coeff exponent vector) =
      (correctedPolynomial D hu (-charge) (sigma D polynomial)).coeff exponent
        (sigmaTensor D hu vector) := by
  have correction : Corr D (-charge) (sigma D polynomial) =
      Finsupp.mapRange.linearMap (sigmaLinear D) (Corr D charge polynomial) := by
    apply Finsupp.ext
    intro shift
    exact Corr_reflection D charge polynomial shift
  simp only [correctedPolynomial, LinearMap.comp_apply]
  rw [correction]
  exact sigmaTensor_correctionSum D hu charge (Corr D charge polynomial) exponent vector

theorem Ytw_target_theta (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    sigmaTensor D hu ((Ytw D hu source).coeff exponent vector) =
      (Ytw D hu (theta D source)).coeff exponent (sigmaTensor D hu vector) := by
  induction source using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, firstProof, secondProof]
  | single charge polynomial =>
    change sigmaTensor D hu ((Ytw D hu (Finsupp.single charge polynomial)).coeff
        exponent vector) =
      (Ytw D hu (thetaLinear D (Finsupp.single charge polynomial))).coeff exponent
        (sigmaTensor D hu vector)
    rw [theta_single]
    simp only [Ytw, Finsupp.lsum_single]
    exact sigmaTensor_correctedPolynomial D hu charge polynomial exponent vector

#print axioms Ytw_target_theta

end
end D5.S3.VertexAlgebra.LatticeHalfFockTargetTheta
