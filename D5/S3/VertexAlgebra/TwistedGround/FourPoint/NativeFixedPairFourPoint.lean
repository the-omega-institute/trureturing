/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedPairFourPoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedPairFourPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even-source coevaluation and finite four-point Wick coefficients for the same-parity Leech field. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledBPZCoevaluation
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairField

/-! The upper branch of Huang, hep-th/9406190v7, §3.4, pp. 22–23, sewn on
the actual Leech fixed source with the original ambient dual basis. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairFourPoint

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeHalfFock LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open ActualLeechHyperbolic (leechData leech_spec)
open ActualChargedAdjoint (actualForm)
open ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open HalfFock.ActualEnergyCovariance (correctedField_signed_output)
open CorrectedInversion (K_R)
open FixedGradedDuality (plusPart_mem_fixedSpace)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open SourceBPZ.SourcePairingLaws (sourcePairing_theta)
open SourceBPZ.OriginalSourceCoevaluation (dualCarrierBasis)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeFixedPairState
open Orbifold.NativeFixedPairField (nu nu_coeff_of_grade nu_coeff_eq_originalI nu_ground_vacuum)
open OriginalFourMChargeCoset (originalI oscillatorLower)
open OriginalFourMEnergyCoefficient (polynomialCoefficient)
open NativeDoubledBPZWick
open NativeDoubledBPZCoevaluation (ambient_coevaluation)
open private energyFiber_sum_eq_charge from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledBPZCoevaluation
open private pairing_plusPart_right_of_fixed_left from
  D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private vacuum_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

local notation "ℒ" => leechData

private theorem I_zpow_neg_two_mul (n : ℤ) : Complex.I ^ (-2 * n) = (-1 : ℂ) ^ n := by
  have htwo : Complex.I ^ (2 : ℤ) = -1 :=
    (zpow_natCast Complex.I 2).trans Complex.I_sq
  have hneg : Complex.I ^ (-2 : ℤ) = -1 := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by decide, zpow_neg, htwo]
    norm_num
  rw [zpow_mul, hneg]

/-- The upper-branch phase of the actual fixed-source functional. -/
theorem fixedPair_phase (M K E : ℕ) (m : ℤ)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    Complex.I ^ (-(3 + (M : ℤ))) * (-1 : ℂ) ^ ((M : ℤ) - m + 2) =
      (-1 : ℂ) ^ (E : ℤ) * Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3) := by
  rw [← I_zpow_neg_two_mul ((M : ℤ) - m + 2), ← I_zpow_neg_two_mul (E : ℤ),
    ← zpow_add₀ Complex.I_ne_zero (-(3 + (M : ℤ))) (-2 * ((M : ℤ) - m + 2)),
    ← zpow_add₀ Complex.I_ne_zero (-2 * (E : ℤ)) ((K : ℤ) - 2 * (M : ℤ) - 3)]
  exact congrArg (fun e : ℤ => Complex.I ^ e) (by omega)

/-- On the actual fixed carrier both BPZ constructions give the same
functional, with the detector in the first form slot on each leg. -/
theorem fixedPairing_eq_bpzPairing (s : Bool) (M K E : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m) (a : FixedCarrier ℒ) :
    fixedPairing s M K m u v a = bpzPairing ℒ leechUnit M K E u.val v.val a.val := by
  simp only [fixedPairing_apply, bpzPairing, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, K_R, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ell _
  have hmode : 2 * (m + (j : ℤ) - (ell : ℤ) - (M : ℤ) - 2) =
      leftExponent M K E j ell := by
    unfold leftExponent
    omega
  have hsign : (-1 : ℂ) ^ ((M : ℤ) - m - (j : ℤ) + (ell : ℤ) + 2) =
      (-1 : ℂ) ^ ((M : ℤ) - m + 2) * (-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) := by
    have hne : (-1 : ℂ) ≠ 0 := by norm_num
    rw [show (M : ℤ) - m - (j : ℤ) + (ell : ℤ) + 2 =
      ((M : ℤ) - m + 2 + ((j : ℤ) + (ell : ℤ))) + 2 * (-(j : ℤ)) by ring,
      zpow_add₀ hne ((M : ℤ) - m + 2 + ((j : ℤ) + (ell : ℤ))) (2 * (-(j : ℤ))),
      (even_two_mul (-(j : ℤ))).neg_one_zpow, mul_one,
      zpow_add₀ hne ((M : ℤ) - m + 2) ((j : ℤ) + (ell : ℤ))]
  rw [hmode, hsign, bpz_phase, ← fixedPair_phase M K E m hE]
  ring

/-- The sign-one Wick convention uses the actual fixed-space projector. -/
theorem sourceProjection_one (D : LatticeData) (a : Carrier D) :
    sourceProjection D 1 a = plusPart D a := by
  simp only [sourceProjection, plusPart, one_smul]

/-- In the signed Wick readout the scalar projection factor is one. -/
theorem projectionFactor_one_of_energy (M K E : ℕ) (m : ℤ)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    projectionFactor 1 ((M : ℤ) + (K : ℤ)) = 1 := by
  have hEven : Even ((M : ℤ) + (K : ℤ)) := ⟨(E : ℤ) + m - 2, by omega⟩
  rw [projectionFactor, hEven.neg_one_zpow]
  norm_num

private theorem nu_coeff_mem_grade (s : Bool) (M K : ℕ) (m E : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hE : 2 * E = (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    ((nu s u).coeff (-2 * m - 2) v).val ∈ grade ℒ E := by
  have hweight : fixedPairWeight M K m = E := by
    unfold fixedPairWeight
    omega
  rw [nu_coeff_of_grade s M K m u v hu hv, ← hweight]
  exact fixedPairState_grade s M K m u v

/-- The projected ambient test evaluates the actual fixed-source coefficient. -/
theorem nu_coeff_sourcePairing (s : Bool) (M K E : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m) (a : Carrier ℒ) :
    sourcePairing ℒ ((nu s u).coeff (-2 * m - 2) v).val a =
      bpzPairing ℒ leechUnit M K E u.val v.val (sourceProjection ℒ 1 a) := by
  let aFixed : FixedCarrier ℒ := ⟨plusPart ℒ a, plusPart_mem_fixedSpace ℒ a⟩
  rw [nu_coeff_of_grade s M K m u v hu hv]
  let x := fixedPairState s M K m u v
  calc
    sourcePairing ℒ x.val a = sourcePairing ℒ x.val aFixed.val :=
      (pairing_plusPart_right_of_fixed_left ℒ (sourcePairing ℒ)
        (sourcePairing_theta ℒ) x.val x.property a).symm
    _ = fixedPairing s M K m u v aFixed := fixedPairState_pairing s M K m u v hu hv aFixed
    _ = bpzPairing ℒ leechUnit M K E u.val v.val (sourceProjection ℒ 1 a) := by
      rw [sourceProjection_one]
      exact fixedPairing_eq_bpzPairing s M K E m u v hE aFixed

/-- Ambient coevaluation of the actual homogeneous same-parity pair field. -/
theorem nu_coeff_coevaluation (s : Bool) (M K E : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    ((nu s u).coeff (-2 * m - 2) v).val =
      ∑ᶠ a : EnergyFiber ℒ (E : ℤ),
        bpzPairing ℒ leechUnit M K E u.val v.val
          (sourceProjection ℒ 1 (carrierBasis ℒ a.val)) • dualCarrierBasis ℒ a.val := by
  rw [ambient_coevaluation ℒ leechUnit leech_spec.2.2.1 (E : ℤ) _
    (nu_coeff_mem_grade s M K m (E : ℤ) u v hu hv hE)]
  apply finsum_congr
  intro a
  rw [nu_coeff_sourcePairing s M K E m u v hu hv hE]

/-- Applying the actual corrected field and ordered twisted form at the right
Laurent exponent gives the whole energy-fiber contraction. -/
theorem nu_fourPoint_energyFiber (s : Bool) (M K E : ℕ) (m eR : ℤ)
    (u v : Twisted ℒ leechUnit s) (w b : ActualTensor ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    actualForm ℒ leechUnit b
        ((correctedField ℒ leechUnit ((nu s u).coeff (-2 * m - 2) v).val).coeff eR w) =
      ∑ᶠ a : EnergyFiber ℒ (E : ℤ),
        bpzPairing ℒ leechUnit M K E u.val v.val
          (sourceProjection ℒ 1 (carrierBasis ℒ a.val)) *
        K_R ℒ leechUnit eR b w (dualCarrierBasis ℒ a.val) := by
  classical
  let := energyFiber_finite ℒ leech_spec.2.2.1 (E : ℤ)
  let := Fintype.ofFinite (EnergyFiber ℒ (E : ℤ))
  change K_R ℒ leechUnit eR b w ((nu s u).coeff (-2 * m - 2) v).val = _
  rw [nu_coeff_coevaluation s M K E m u v hu hv hE]
  simp only [finsum_eq_sum_of_fintype, map_sum, map_smul, smul_eq_mul]

/-- The same contraction grouped by the full charge sublevel, including zero. -/
theorem nu_fourPoint_charge (s : Bool) (M K E : ℕ) (m eR : ℤ)
    (u v : Twisted ℒ leechUnit s) (w b : ActualTensor ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    actualForm ℒ leechUnit b
        ((correctedField ℒ leechUnit ((nu s u).coeff (-2 * m - 2) v).val).coeff eR w) =
      ∑ᶠ q : {q : Charge ℒ // chargeEnergy ℒ q ≤ E},
        fixedChargeCoefficient ℒ leechUnit 1 q.val M K E eR u.val v.val w b := by
  rw [nu_fourPoint_energyFiber s M K E m eR u v w b hu hv hE]
  let f (a : Label ℒ) :=
    bpzPairing ℒ leechUnit M K E u.val v.val
      (sourceProjection ℒ 1 (carrierBasis ℒ a)) *
    K_R ℒ leechUnit eR b w (dualCarrierBasis ℒ a)
  change (∑ᶠ a : EnergyFiber ℒ (E : ℤ), f a.val) = _
  rw [energyFiber_sum_eq_charge ℒ leech_spec.2.2.1 E f]
  apply finsum_congr
  intro q
  simp only [fixedChargeCoefficient, ite_eq_left q.property, f, carrierBasis_apply]

/-- Homogeneous right input and detector force the signed exponent
`N - L - 2*E`. -/
theorem nu_fourPoint_off_right_grade (s : Bool) (M K L N : ℕ) (m E eR : ℤ)
    (u v : Twisted ℒ leechUnit s) (w b : ActualTensor ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w ∈ actualGrade ℒ leechUnit L)
    (hb : b ∈ actualGrade ℒ leechUnit N)
    (hE : 2 * E = (M : ℤ) + (K : ℤ) + 4 - 2 * m)
    (heR : eR ≠ (N : ℤ) - (L : ℤ) - 2 * E) :
    actualForm ℒ leechUnit b
        ((correctedField ℒ leechUnit ((nu s u).coeff (-2 * m - 2) v).val).coeff eR w) = 0 := by
  have hwL := (actualGrade_eigen ℒ leechUnit L w).mp hw
  have hbN := (actualGrade_eigen ℒ leechUnit N b).mp hb
  have hout := correctedField_signed_output ℒ leechUnit E (L : ℤ) eR _
    (nu_coeff_mem_grade s M K m E u v hu hv hE) w
    (by simpa only [Int.cast_natCast] using hwL)
  exact actualForm_oddGrade_orthogonal ℒ leechUnit (N : ℤ) ((L : ℤ) + eR + 2 * E)
    b _ (by simpa only [Int.cast_natCast] using hbN) hout (by omega)

/-- The exact fixed-charge signed Wick coefficient on pure tensors. The
selectors and charge normalization are those of `polynomialCoefficient`. -/
theorem fixedChargeCoefficient_one_eq (q : Charge ℒ) (M K E : ℕ) (m eR : ℤ)
    (hq : chargeEnergy ℒ q ≤ E)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m)
    (P Q R S : Oscillator ℒ) (x y z d : ActualGround ℒ leechUnit) :
    fixedChargeCoefficient ℒ leechUnit 1 q M K E eR
      (P ⊗ₜ[ℂ] x) (Q ⊗ₜ[ℂ] y) (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) =
      ((-1 : ℂ) ^ (E : ℤ) * Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3)) *
        groundFactor ℒ leechUnit q x y z d *
        ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
          ((-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) / ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
            polynomialCoefficient ℒ q E (leftExponent M K E j ell) eR
              ((oscillatorLower ℒ ^ j) P) ((oscillatorLower ℒ ^ ell) Q) R S := by
  rw [fixedChargeCoefficient_eq ℒ leechUnit 1 q M K E hq eR P Q R S x y z d,
    projectionFactor_one_of_energy M K E m hE, one_mul]

/-- For odd/odd input the same coevaluation computes the original orbifold
coefficient. -/
theorem originalI_coeff_coevaluation (M K E : ℕ) (m : ℤ) (u v : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    (originalI ℒ leechUnit leech_spec.2.2.1 m u v).val =
      ∑ᶠ a : EnergyFiber ℒ (E : ℤ),
        bpzPairing ℒ leechUnit M K E u.val v.val
          (sourceProjection ℒ 1 (carrierBasis ℒ a.val)) • dualCarrierBasis ℒ a.val := by
  rw [← nu_coeff_eq_originalI m u v]
  exact nu_coeff_coevaluation true M K E m u v hu hv hE

/-- An actual H,H front pair at energy `E` has left doubled exponent
`2*E-6`. Taking `t = false` and `L = N = 0` gives H,H,H,H.
Taking `t = true` gives H,H,B,B with both right excitations retained. -/
theorem nu_ground_fourPoint_charge (t : Bool) (E L N : ℕ) (eR : ℤ) (u v : TwistedEven)
    (w b : Twisted ℒ leechUnit t)
    (hu : u.val ∈ actualGrade ℒ leechUnit 0)
    (hv : v.val ∈ actualGrade ℒ leechUnit 0)
    (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hb : b.val ∈ actualGrade ℒ leechUnit N) :
    actualForm ℒ leechUnit b.val
        ((correctedField ℒ leechUnit ((nu false u).coeff (2 * (E : ℤ) - 6) v).val).coeff
          eR w.val) =
      if eR = (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) then
        ∑ᶠ q : {q : Charge ℒ // chargeEnergy ℒ q ≤ E},
          fixedChargeCoefficient ℒ leechUnit 1 q.val 0 0 E eR u.val v.val w.val b.val
      else 0 := by
  have hmode : 2 * (E : ℤ) - 6 = -2 * (2 - (E : ℤ)) - 2 := by ring
  rw [hmode]
  by_cases heR : eR = (N : ℤ) - (L : ℤ) - 2 * (E : ℤ)
  · rw [if_pos heR]
    exact nu_fourPoint_charge false 0 0 E (2 - (E : ℤ)) eR u v w.val b.val hu hv (by omega)
  · rw [if_neg heR]
    exact nu_fourPoint_off_right_grade false 0 0 L N (2 - (E : ℤ)) (E : ℤ) eR
      u v w.val b.val hu hv hw hb (by omega) heR

/-- The H,H vacuum coefficient gives the product of the two ordered actual
twisted pairings with upper-branch phase `I`. -/
theorem nu_ground_fourPoint_vacuum (u v : TwistedEven) (w b : ActualTensor ℒ leechUnit)
    (hu : u.val ∈ actualGrade ℒ leechUnit 0)
    (hv : v.val ∈ actualGrade ℒ leechUnit 0) :
    actualForm ℒ leechUnit b
        ((correctedField ℒ leechUnit ((nu false u).coeff (-6) v).val).coeff 0 w) =
      Complex.I * actualForm ℒ leechUnit v.val u.val * actualForm ℒ leechUnit b w := by
  change K_R ℒ leechUnit 0 b w ((nu false u).coeff (-6) v).val = _
  rw [nu_ground_vacuum u v hu hv]
  change K_R ℒ leechUnit 0 b w
    ((Complex.I * actualForm ℒ leechUnit v.val u.val) •
      LatticeAllStateField.vacuum ℒ) = _
  rw [map_smul, smul_eq_mul]
  change _ * actualForm ℒ leechUnit b
    ((correctedField ℒ leechUnit (LatticeAllStateField.vacuum ℒ)).coeff 0 w) = _
  rw [vacuum_coeff, if_pos rfl]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedPairFourPoint
