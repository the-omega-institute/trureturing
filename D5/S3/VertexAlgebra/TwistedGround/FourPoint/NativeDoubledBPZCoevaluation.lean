/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeDoubledBPZCoevaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeDoubledBPZCoevaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ambient coevaluation and finite Gaussian sewing of the native mixed Leech field. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledBPZWick
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

/-!
Finite sewing of the mixed twisted-pair coefficient in the upper branch of
Huang, hep-th/9406190v7, §3.4. The intermediate states are the original
inverse-Wick lattice states, and the right insertion is the signed coefficient
of the actual corrected twisted field.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledBPZCoevaluation

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open ActualLeechHyperbolic (leechData leech_spec)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_nondegenerate)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open SourceBPZ.OriginalSourceCoevaluation (dualCarrierBasis dualCarrierBasis_pairing)
open CorrectedInversion (K_R)
open ActualChargedAdjoint (actualForm)
open ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open HalfFock.ActualEnergyCovariance (correctedField_signed_output)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeMixedPairState (mixedPairWeight mixedPairState_grade)
open Orbifold.NativeMixedPairField (mu mu_coeff_of_grade)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMEnergyCoefficient (polynomialCoefficient)
open OperatorAlgebra (chargeOperator)
open NativeDoubledBPZWick
open private gradeBasis_val from D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
open private left_grade_projection_pairing from D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
open private chargeFiberEquiv oscillatorFiber_finite from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
open private groundForm from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew

set_option maxHeartbeats 4000000 in
-- Allow for elaboration of the finite basis and transported coefficient maps.
/-- The actual ambient BPZ coevaluation at a signed lattice grade. -/
theorem ambient_coevaluation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (E : ℤ)
    (x : Carrier D) (hx : x ∈ grade D E) :
    x = ∑ᶠ a : EnergyFiber D E,
      sourcePairing D x (carrierBasis D a.val) • dualCarrierBasis D a.val := by
  classical
  let := energyFiber_finite D hD E
  let := Fintype.ofFinite (EnergyFiber D E)
  apply sub_eq_zero.mp
  apply (sourcePairing_nondegenerate D hu).1
  intro y
  let p : grade D E := ⟨gradeProjection D E y, gradeProjection_mem D E y⟩
  have hp : (∑ a : EnergyFiber D E,
      carrierCoeffEquiv D y a.val • carrierBasis D a.val) = gradeProjection D E y := by
    have he := congrArg (grade D E).subtype ((gradeBasis D E).sum_repr p)
    simp only [map_sum, map_smul] at he
    calc
      _ = ∑ a : EnergyFiber D E, (gradeBasis D E).repr p a •
          (grade D E).subtype (gradeBasis D E a) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [show (grade D E).subtype (gradeBasis D E a) = carrierBasis D a.val from
          gradeBasis_val D E a]
        have hc : (gradeBasis D E).repr p a = carrierCoeffEquiv D y a.val := by
          change carrierCoeffEquiv D (gradeProjection D E y) a.val = _
          rw [gradeProjection_coeff, ite_eq_left a.property]
        rw [hc]
      _ = _ := he
  have he : (∑ a : EnergyFiber D E,
      carrierCoeffEquiv D y a.val * sourcePairing D x (carrierBasis D a.val)) =
      sourcePairing D x y := by
    have ht := congrArg (sourcePairing D x) hp
    simp only [map_sum, map_smul, smul_eq_mul] at ht
    exact ht.trans (left_grade_projection_pairing D (sourcePairing D)
      (fun h k v w hv hw hne => sourcePairing_grade D h k hne v w hv hw) E x hx y)
  rw [map_sub, LinearMap.sub_apply, ← he, finsum_eq_sum_of_fintype]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, dualCarrierBasis_pairing D hu]
  apply sub_eq_zero.mpr
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

private theorem mu_coeff_mem_grade (s : Bool) (M K : ℕ) (m E : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hE : 2 * E = (M : ℤ) + (K : ℤ) + 3 - 2 * m) :
    ((mu s u).coeff (-2 * m - 3) v).val ∈ grade leechData E := by
  have hweight : mixedPairWeight M K m = E := by
    unfold mixedPairWeight
    omega
  rw [mu_coeff_of_grade s M K m u v hu hv, ← hweight]
  exact mixedPairState_grade s M K m u v

/-- The actual mixed field coefficient at physical exponent `-m-3/2`. -/
theorem mu_coeff_coevaluation (s : Bool) (M K E : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) :
    ((mu s u).coeff (-2 * m - 3) v).val =
      ∑ᶠ a : EnergyFiber leechData (E : ℤ),
        bpzPairing leechData leechUnit M K E u.val v.val
          (sourceProjection leechData (-1) (carrierBasis leechData a.val)) •
        dualCarrierBasis leechData a.val := by
  rw [ambient_coevaluation leechData leechUnit leech_spec.2.2.1 (E : ℤ) _
    (mu_coeff_mem_grade s M K m E u v hu hv hE)]
  apply finsum_congr
  intro a
  rw [mu_coeff_of_grade s M K m u v hu hv,
    projected_bpzPairing_eq_mixedPairState s M K E m u v hu hv hE]

/-- Apply the actual right Laurent coefficient to the finite vector expansion. -/
theorem mu_fourPoint_energyFiber (s : Bool) (M K E : ℕ) (m eR : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w b : ActualTensor leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) :
    actualForm leechData leechUnit b
        ((correctedField leechData leechUnit ((mu s u).coeff (-2 * m - 3) v).val).coeff eR w) =
      ∑ᶠ a : EnergyFiber leechData (E : ℤ),
        bpzPairing leechData leechUnit M K E u.val v.val
          (sourceProjection leechData (-1) (carrierBasis leechData a.val)) *
        K_R leechData leechUnit eR b w (dualCarrierBasis leechData a.val) := by
  classical
  let := energyFiber_finite leechData leech_spec.2.2.1 (E : ℤ)
  let := Fintype.ofFinite (EnergyFiber leechData (E : ℤ))
  change K_R leechData leechUnit eR b w ((mu s u).coeff (-2 * m - 3) v).val = _
  rw [mu_coeff_coevaluation s M K E m u v hu hv hE]
  simp only [finsum_eq_sum_of_fintype, map_sum, map_smul, smul_eq_mul]

/-- For homogeneous right inputs the actual signed field has precisely the
grade constraint of the right Laurent selector. -/
theorem mu_fourPoint_off_right_grade (s : Bool) (M K L N : ℕ) (m E eR : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w b : ActualTensor leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hw : w ∈ actualGrade leechData leechUnit L)
    (hb : b ∈ actualGrade leechData leechUnit N)
    (hE : 2 * E = (M : ℤ) + (K : ℤ) + 3 - 2 * m)
    (heR : eR ≠ (N : ℤ) - (L : ℤ) - 2 * E) :
    actualForm leechData leechUnit b
        ((correctedField leechData leechUnit ((mu s u).coeff (-2 * m - 3) v).val).coeff eR w) =
      0 := by
  have hwL := (actualGrade_eigen leechData leechUnit L w).mp hw
  have hbN := (actualGrade_eigen leechData leechUnit N b).mp hb
  have hout := correctedField_signed_output leechData leechUnit E (L : ℤ) eR _
    (mu_coeff_mem_grade s M K m E u v hu hv hE) w
    (by simpa only [Int.cast_natCast] using hwL)
  exact actualForm_oddGrade_orthogonal leechData leechUnit (N : ℤ) ((L : ℤ) + eR + 2 * E)
    b _ (by simpa only [Int.cast_natCast] using hbN) hout (by omega)

private theorem energyFiber_sum_eq_charge (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (E : ℕ) (f : Label D → ℂ) :
    (∑ᶠ a : EnergyFiber D (E : ℤ), f a.val) =
      ∑ᶠ q : {q : Charge D // chargeEnergy D q ≤ E},
        ∑ᶠ a : {α : Exponent D // oscillatorEnergy α = E - (chargeEnergy D q.val).toNat},
          f (q.val, a.val) := by
  classical
  let := energyFiber_finite D hD (E : ℤ)
  let := Fintype.ofFinite (EnergyFiber D (E : ℤ))
  let Q := {q : Charge D // chargeEnergy D q ≤ E}
  let : Finite Q := (chargeSublevel_finite D hD E).to_subtype
  let := Fintype.ofFinite Q
  let (q : Q) := oscillatorFiber_finite D (E - (chargeEnergy D q.val).toNat)
  let (q : Q) := Fintype.ofFinite {α : Exponent D //
    oscillatorEnergy α = E - (chargeEnergy D q.val).toNat}
  simp only [finsum_eq_sum_of_fintype]
  rw [← (chargeFiberEquiv D hD E).symm.sum_comp, Fintype.sum_sigma]
  rfl

/-- The whole intermediate grade as a sum of actual inverse-Wick contractions
over the charge sublevel, including the zero charge. -/
theorem mu_fourPoint_charge (s : Bool) (M K E : ℕ) (m eR : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (w b : ActualTensor leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) :
    actualForm leechData leechUnit b
        ((correctedField leechData leechUnit ((mu s u).coeff (-2 * m - 3) v).val).coeff eR w) =
      ∑ᶠ q : {q : Charge leechData // chargeEnergy leechData q ≤ E},
        fixedChargeCoefficient leechData leechUnit (-1) q.val M K E eR u.val v.val w b := by
  rw [mu_fourPoint_energyFiber s M K E m eR u v w b hu hv hE]
  let f (a : Label leechData) :=
    bpzPairing leechData leechUnit M K E u.val v.val
      (sourceProjection leechData (-1) (carrierBasis leechData a)) *
    K_R leechData leechUnit eR b w (dualCarrierBasis leechData a)
  change (∑ᶠ a : EnergyFiber leechData (E : ℤ), f a.val) = _
  rw [energyFiber_sum_eq_charge leechData leech_spec.2.2.1 E f]
  apply finsum_congr
  intro q
  simp only [fixedChargeCoefficient, ite_eq_left q.property, f, carrierBasis_apply]

set_option maxHeartbeats 4000000 in
-- Allow for elaboration of the fixed-charge readout under the dependent sum.
/-- At each total energy the actual mixed four-point scalar is the sum of the
original Gaussian coefficients grouped by mod-two charge. The original
polynomial coefficient carries both signed Laurent selectors, all four
occupation factorials and the product of the opposite charge scalars. -/
theorem mu_fourPoint_gaussian_cosets (s : Bool) (M K E : ℕ) (m eR : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (P Q R S : Oscillator leechData) (x y z d : ActualGround leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) :
    actualForm leechData leechUnit (S ⊗ₜ[ℂ] d)
        ((correctedField leechData leechUnit ((mu s u).coeff (-2 * m - 3) v).val).coeff
          eR (R ⊗ₜ[ℂ] z)) =
      (projectionFactor (-1) ((M : ℤ) + (K : ℤ)) *
        ((-1 : ℂ) ^ (E : ℤ) * Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3))) *
      ∑ a : ModTwoCharge leechData,
        (groundForm leechData leechUnit y
          (chargeOperator leechData (groundRepresentation leechData leechUnit) a x) *
        groundForm leechData leechUnit d
          (chargeOperator leechData (groundRepresentation leechData leechUnit) a z)) *
        ∑ᶠ q : {q : Charge leechData // chargeEnergy leechData q ≤ E},
          if reduceCharge leechData q.val = a then
            ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
              ((-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) /
                ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
              polynomialCoefficient leechData q.val E (leftExponent M K E j ell) eR
                ((oscillatorLower leechData ^ j) P) ((oscillatorLower leechData ^ ell) Q) R S
          else 0 := by
  classical
  let Charges := {q : Charge leechData // chargeEnergy leechData q ≤ E}
  let : Finite Charges := (chargeSublevel_finite leechData leech_spec.2.2.1 E).to_subtype
  let := Fintype.ofFinite Charges
  let c := projectionFactor (-1) ((M : ℤ) + (K : ℤ)) *
    ((-1 : ℂ) ^ (E : ℤ) * Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3))
  let coset (q : Charges) := reduceCharge leechData q.val
  let g (a : ModTwoCharge leechData) :=
    groundForm leechData leechUnit y
      (chargeOperator leechData (groundRepresentation leechData leechUnit) a x) *
    groundForm leechData leechUnit d
      (chargeOperator leechData (groundRepresentation leechData leechUnit) a z)
  let f (q : Charges) :=
    ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
      ((-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) / ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
      polynomialCoefficient leechData q.val E (leftExponent M K E j ell) eR
        ((oscillatorLower leechData ^ j) P) ((oscillatorLower leechData ^ ell) Q) R S
  change _ = c * ∑ a : ModTwoCharge leechData,
    g a * ∑ᶠ q : Charges, if coset q = a then f q else 0
  calc
    _ = ∑ q : Charges, c * (g (coset q) * f q) := by
      rw [mu_fourPoint_charge s M K E m eR u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) hu hv hE,
        finsum_eq_sum_of_fintype]
      apply Finset.sum_congr rfl
      intro q _
      rw [huP, hvQ, fixedChargeCoefficient_eq leechData leechUnit (-1) q.val M K E
        q.property eR P Q R S x y z d]
      change c * g (coset q) * f q = c * (g (coset q) * f q)
      exact mul_assoc _ _ _
    _ = c * ∑ a : ModTwoCharge leechData,
        ∑ q ∈ Finset.univ.filter (fun q : Charges => coset q = a),
          g (coset q) * f q := by
      rw [Finset.sum_fiberwise Finset.univ coset (fun q => g (coset q) * f q), Finset.mul_sum]
    _ = _ := by
      simp only [finsum_eq_sum_of_fintype]
      apply congrArg (fun t : ℂ => c * t)
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledBPZCoevaluation
