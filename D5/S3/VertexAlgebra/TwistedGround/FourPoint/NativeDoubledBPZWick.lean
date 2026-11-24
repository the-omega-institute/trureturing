/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeDoubledBPZWick
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeDoubledBPZWick
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed theta reflection and the actual fixed-charge doubled BPZ Wick coefficient. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState
import Batteries.Tactic.OpenPrivate

/-!
The upper-branch BPZ inversion uses Huang, hep-th/9406190v7, §3.4,
pp. 22–23. A rank-24 input at doubled excitation `M` has twice-weight
`M+3`. At lattice energy `E`, the two lowering orders `j, ell` select the
actual TT exponent `K-M-2E+2j-2ell`. Each leg uses the original bilinear
orientation with the detector in the first slot.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledBPZWick

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open OriginalFourMChargeCoset (oscillatorCorrected oscillatorLower corrected_tmul
  oscillatorCoordinate oscillatorCoordinate_tmul)
open OriginalFourMEnergyCoefficient (polynomialCoefficient)
open CorrectedInversion (K_R)
open ActualChargedAdjoint (actualForm)
open OperatorAlgebra (chargeOperator)
open SignedOscillatorWick SourceBPZ.OriginalSourceCoevaluation MvPolynomial
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open ActualLeechHyperbolic (leechData)
open Orbifold.NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit J)
open Orbifold.NativeOddUpperRightSkew (lowering mixedPairing mixedPairing_finite)
open Orbifold.NativeMixedPairState (mixedPairState mixedPairState_pairing)
open private groundAction_reduction groundForm chargeScalar_neg lower_power_tmul from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private actualForm_tmul from D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open private groundAction_neg polynomialCoefficient_eq oscillatorFiber_finite from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
open private T from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private J_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private minusPart_mem sourcePairing_minusPart_right from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState

private theorem reduceCharge_neg (D : LatticeData) (q : Charge D) :
    reduceCharge D (-q) = reduceCharge D q := by
  rw [map_neg]
  funext b
  exact CharTwo.neg_eq _

/-- Signed extension of the original even-mode reflection, using the actual
ground coordinate to extract the oscillator operator. -/
theorem reflected_corrected_signed (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (p x : Oscillator D) (e : ℤ) :
    oscillatorCorrected D hu (-q) e (sigma D p) x =
      (-1 : ℂ)^e • oscillatorCorrected D hu q e p x := by
  let g₁ : ActualGround D hu := fun _ => 1
  let g := groundRepresentation D hu (groundLift D q)⁻¹ g₁
  have hg : groundAction D hu q g = g₁ :=
    (groundRepresentation D hu).self_inv_apply (groundLift D q) g₁
  have h := correctedField_theta D hu (Finsupp.single q p) e
  change (correctedField D hu (thetaLinear D (Finsupp.single q p))).coeff e = _ at h
  rw [theta_single] at h
  have applied := LinearMap.congr_fun h (x ⊗ₜ[ℂ] g)
  change (correctedField D hu (Finsupp.single (-q) (sigma D p))).coeff e (x ⊗ₜ[ℂ] g) =
    (-1 : ℂ)^e • (correctedField D hu (Finsupp.single q p)).coeff e (x ⊗ₜ[ℂ] g) at applied
  rw [corrected_tmul, corrected_tmul, groundAction_neg, hg, chargeScalar_neg] at applied
  have projected := congrArg (oscillatorCoordinate D hu) applied
  simp only [map_smul, oscillatorCoordinate_tmul, show g₁ 0 = 1 from rfl, one_smul]
    at projected
  have hc : chargeScalar D q ≠ 0 := zpow_ne_zero _ (by norm_num)
  apply (smul_right_injective (Oscillator D) hc)
  simpa only [smul_smul, mul_comm ((-1 : ℂ)^e) (chargeScalar D q)] using projected

/-- For signs `1` and `-1` this is the actual lattice even and odd projection. -/
def sourceProjection (D : LatticeData) (ε : ℂ) (a : Carrier D) : Carrier D :=
  (2 : ℂ)⁻¹ • (a + ε • theta D a)

def projectionFactor (ε : ℂ) (e : ℤ) : ℂ := (1 + ε * (-1 : ℂ)^e) / 2

/-- The signed doubled Laurent exponent on the left BPZ leg. -/
def leftExponent (M K E j ell : ℕ) : ℤ :=
  (K : ℤ) - (M : ℤ) - 2*(E : ℤ) + 2*(j : ℤ) - 2*(ell : ℤ)

theorem leftExponent_sign (M K E j ell : ℕ) :
    (-1 : ℂ) ^ leftExponent M K E j ell = (-1 : ℂ) ^ ((M : ℤ) + (K : ℤ)) := by
  let n : ℤ := -(M : ℤ) - (E : ℤ) + (j : ℤ) - (ell : ℤ)
  have h : leftExponent M K E j ell = (M : ℤ) + (K : ℤ) + 2*n := by
    dsimp [leftExponent, n]
    ring
  rw [h, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (even_two_mul n).neg_one_zpow, mul_one]

theorem bpz_phase (M K E j ell : ℕ) :
    Complex.I ^ (-((M : ℤ) + 3) + leftExponent M K E j ell) =
      (-1 : ℂ) ^ (E : ℤ) * Complex.I ^ ((K : ℤ) - 2*(M : ℤ) - 3) *
        (-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) := by
  have hi₂ : Complex.I ^ (2 : ℤ) = -1 :=
    (zpow_natCast Complex.I 2).trans Complex.I_sq
  have hi₄ : Complex.I ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = 2*2 by decide, zpow_mul, hi₂]
    norm_num
  let t : ℤ := -(E : ℤ) - (ell : ℤ)
  have h : -((M : ℤ) + 3) + leftExponent M K E j ell =
      2*(E : ℤ) + ((K : ℤ) - 2*(M : ℤ) - 3) + 2*((j : ℤ) + (ell : ℤ)) + 4*t := by
    dsimp [leftExponent, t]
    ring
  rw [h]
  simp only [zpow_add₀ Complex.I_ne_zero, zpow_mul Complex.I 2,
    zpow_mul Complex.I 4, hi₂, hi₄, one_zpow, mul_one]

private theorem pairing_single_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (e : ℤ) (p P Q : Oscillator D) (x y : ActualGround D hu) :
    K_R D hu e (Q ⊗ₜ[ℂ] y) (P ⊗ₜ[ℂ] x) (Finsupp.single q p) =
      chargeScalar D q * wick D Q (oscillatorCorrected D hu q e p P) *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) (reduceCharge D q) x) := by
  change actualForm D hu (Q ⊗ₜ[ℂ] y)
    ((correctedField D hu (Finsupp.single q p)).coeff e (P ⊗ₜ[ℂ] x)) = _
  rw [corrected_tmul, map_smul, actualForm_tmul, groundAction_reduction]
  simp only [smul_eq_mul]
  ring

private theorem projected_pairing_single (D : LatticeData) (hu : IsUnit D.G.det)
    (ε : ℂ) (q : Charge D) (e : ℤ) (p P Q : Oscillator D) (x y : ActualGround D hu) :
    K_R D hu e (Q ⊗ₜ[ℂ] y) (P ⊗ₜ[ℂ] x) (sourceProjection D ε (Finsupp.single q p)) =
      projectionFactor ε e *
        (chargeScalar D q * wick D Q (oscillatorCorrected D hu q e p P) *
          groundForm D hu y (chargeOperator D (groundRepresentation D hu) (reduceCharge D q) x)) := by
  simp only [sourceProjection, map_smul, map_add, smul_eq_mul]
  change _ * (_ + ε * K_R D hu e (Q ⊗ₜ[ℂ] y) (P ⊗ₜ[ℂ] x)
    (thetaLinear D (Finsupp.single q p))) = _
  rw [theta_single, pairing_single_tmul, pairing_single_tmul, chargeScalar_neg,
    reduceCharge_neg, reflected_corrected_signed, map_smul]
  simp only [projectionFactor, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Ordered factors of the original ground pairing in the common mod-two coset. -/
def groundFactor (D : LatticeData) (hu : IsUnit D.G.det) (q : Charge D)
    (x y z d : ActualGround D hu) : ℂ :=
  groundForm D hu y (chargeOperator D (groundRepresentation D hu) (reduceCharge D q) x) *
    groundForm D hu d (chargeOperator D (groundRepresentation D hu) (reduceCharge D q) z)

/-- Actual projected TT pairings sewn at one charge, with the original dual
oscillator monomial and opposite charge on the right. Above the energy cutoff
the charge contributes zero. -/
def projectedWickKernel (D : LatticeData) (hu : IsUnit D.G.det)
    (ε : ℂ) (q : Charge D) (E : ℕ) (eL eR : ℤ)
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu) : ℂ :=
  if chargeEnergy D q ≤ E then
    ∑ᶠ a : {α : Exponent D // oscillatorEnergy α = E - (chargeEnergy D q).toNat},
      K_R D hu eL (Q ⊗ₜ[ℂ] y) (P ⊗ₜ[ℂ] x)
        (sourceProjection D ε (Finsupp.single q (monomial a.val 1))) *
      K_R D hu eR (S ⊗ₜ[ℂ] d) (R ⊗ₜ[ℂ] z) (dualCarrierBasis D (q, a.val))
  else 0

/-- The fixed-charge kernel for arbitrary finite oscillator polynomials and
signed exponents. The original polynomial coefficient retains both selectors,
all four factorials, the product of charge scalars and the full sewn Gaussian. -/
theorem projectedWickKernel_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (ε : ℂ) (q : Charge D) (E : ℕ) (hq : chargeEnergy D q ≤ E) (eL eR : ℤ)
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu) :
    projectedWickKernel D hu ε q E eL eR P Q R S x y z d =
      projectionFactor ε eL * groundFactor D hu q x y z d *
        polynomialCoefficient D q E eL eR P Q R S := by
  let A := {α : Exponent D // oscillatorEnergy α = E - (chargeEnergy D q).toNat}
  calc
    _ = (projectionFactor ε eL * groundFactor D hu q x y z d) *
        ∑ᶠ a : A, chargeScalar D q * chargeScalar D (-q) *
          wick D Q (oscillatorCorrected D hu q eL (monomial a.val 1) P) *
          wick D S (oscillatorCorrected D hu (-q) eR (dualOscillatorMonomial D a.val) R) := by
      rw [projectedWickKernel, ite_eq_left hq, mul_finsum]
      apply finsum_congr
      intro a
      simp only [projected_pairing_single, dualCarrierBasis, pairing_single_tmul,
        reduceCharge_neg, groundFactor]
      ring
    _ = _ := by rw [polynomialCoefficient_eq D hu q E hq]

/-- The rank-24 upper-branch BPZ functional on the actual source. The indices
`M, K` specify the doubled grades and the two finite lowering cutoffs. -/
def bpzPairing (D : LatticeData) (hu : IsUnit D.G.det)
    (M K E : ℕ) (u v : ActualTensor D hu) : Module.Dual ℂ (Carrier D) :=
  ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
    (Complex.I ^ (-((M : ℤ) + 3) + leftExponent M K E j ell) /
      ((j.factorial : ℂ) * (ell.factorial : ℂ))) •
      K_R D hu (leftExponent M K E j ell) ((T D hu ^ ell) v) ((T D hu ^ j) u)

/-- The part of the BPZ sewing at charge `q` in the original inverse-Wick frame. -/
def fixedChargeCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (ε : ℂ) (q : Charge D) (M K E : ℕ) (eR : ℤ)
    (u v w b : ActualTensor D hu) : ℂ :=
  if chargeEnergy D q ≤ E then
    ∑ᶠ a : {α : Exponent D // oscillatorEnergy α = E - (chargeEnergy D q).toNat},
      bpzPairing D hu M K E u v (sourceProjection D ε (Finsupp.single q (monomial a.val 1))) *
        K_R D hu eR b w (dualCarrierBasis D (q, a.val))
  else 0

/-- The finite fixed-charge BPZ Wick readout. The common projection, phase and
ordered ground factors multiply the two finite inverse lowering sums. -/
theorem fixedChargeCoefficient_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (ε : ℂ) (q : Charge D) (M K E : ℕ) (hq : chargeEnergy D q ≤ E) (eR : ℤ)
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu) :
    fixedChargeCoefficient D hu ε q M K E eR
      (P ⊗ₜ[ℂ] x) (Q ⊗ₜ[ℂ] y) (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) =
      projectionFactor ε ((M : ℤ) + (K : ℤ)) *
        ((-1 : ℂ) ^ (E : ℤ) * Complex.I ^ ((K : ℤ) - 2*(M : ℤ) - 3)) *
        groundFactor D hu q x y z d *
        ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
          ((-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) / ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
            polynomialCoefficient D q E (leftExponent M K E j ell) eR
              ((oscillatorLower D ^ j) P) ((oscillatorLower D ^ ell) Q) R S := by
  classical
  let := oscillatorFiber_finite D (E - (chargeEnergy D q).toNat)
  let := Fintype.ofFinite {α : Exponent D // oscillatorEnergy α = E - (chargeEnergy D q).toNat}
  calc
    _ = ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
        (Complex.I ^ (-((M : ℤ) + 3) + leftExponent M K E j ell) /
          ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
          projectedWickKernel D hu ε q E (leftExponent M K E j ell) eR
            ((oscillatorLower D ^ j) P) ((oscillatorLower D ^ ell) Q) R S x y z d := by
      simp only [fixedChargeCoefficient, bpzPairing, projectedWickKernel, ite_eq_left hq,
        finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        T, lower_power_tmul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ell _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp only [projectedWickKernel_eq D hu ε q E hq, projectionFactor, leftExponent_sign,
        bpz_phase, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro ell _
      ring

/-- At the matched signed source grade the doubled functional is the existing
Leech mixed BPZ functional on the actual odd carrier. -/
theorem bpzPairing_eq_mixedPairing (s : Bool) (M K E : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) (a : OddCarrier leechData) :
    bpzPairing leechData leechUnit M K E u.val v.val a.val = mixedPairing s M m u v a := by
  rw [mixedPairing_finite s M K m u v hv a]
  simp only [bpzPairing, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ell _
  have hmode : leftExponent M K E j ell = -2*((M : ℤ) - m - (j : ℤ) + (ell : ℤ))-3 := by
    dsimp only [leftExponent]
    omega
  rw [hmode, zpow_add₀ Complex.I_ne_zero, show -((M : ℤ) + 3) = -(3 + (M : ℤ)) by ring]
  simp only [K_R, LinearMap.coe_mk, AddHom.coe_mk, J_val, lowering_pow_val, div_eq_mul_inv,
    mul_inv_rev]
  ring

/-- Evaluation on the projected charge source is evaluation of the actual
Leech mixed pair state against that source in the original source pairing. -/
theorem projected_bpzPairing_eq_mixedPairState (s : Bool) (M K E : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) (a : Carrier leechData) :
    bpzPairing leechData leechUnit M K E u.val v.val (sourceProjection leechData (-1) a) =
      sourcePairing leechData (mixedPairState s M K m u v).val a := by
  let b : OddCarrier leechData := ⟨minusPart leechData a, minusPart_mem a⟩
  have hb : sourceProjection leechData (-1) a = b.val := by
    simp only [sourceProjection, minusPart, neg_one_smul, sub_eq_add_neg, b]
  rw [hb, bpzPairing_eq_mixedPairing s M K E m u v hv hE b,
    ← mixedPairState_pairing s M K m u v hu hv b]
  exact sourcePairing_minusPart_right _ _ (mixedPairState s M K m u v).property

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledBPZWick
