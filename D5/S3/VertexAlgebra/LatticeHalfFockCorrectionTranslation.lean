/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Differentiation of the actual finite singleton and pair insertion calculus. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
import Mathlib.RingTheory.Derivation.Lie

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
  LatticeHalfFockCurrentCorrection MvPolynomial
open scoped BigOperators

noncomputable section

private theorem singleton_scalar_derivative (degree : ℕ) :
    (degree : ℂ) * halfBinomial (degree + 1) + pairScalar 1 degree =
      -(degree : ℂ) * halfBinomial degree := by
  rw [half_successor]
  have first : halfBinomial 1 = -1 / 2 := by norm_num [halfBinomial]
  simp only [pairScalar, Nat.cast_one, first, one_mul]
  have denominator : (degree + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero degree
  rw [add_comm (1 : ℂ) (degree : ℂ)]
  field_simp
  ring

private theorem pair_scalar_derivative (first second : ℕ)
    (positiveFirst : 0 < first) (positiveSecond : 0 < second) :
    (first : ℂ) * pairScalar (first + 1) second +
        (second : ℂ) * pairScalar first (second + 1) =
      -((first : ℂ) + (second : ℂ)) * pairScalar first second := by
  simp only [pairScalar, half_successor, Nat.cast_add, Nat.cast_one]
  have firstSucc : (first + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero first
  have secondSucc : (second + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero second
  have total : ((first : ℂ) + (second : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : first + second ≠ 0)
  have totalSucc : ((first : ℂ) + (second : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by omega : first + second + 1 ≠ 0)
  have totalSucc' : (1 + (first : ℂ) + (second : ℂ)) ≠ 0 := by
    convert totalSucc using 1 <;> ring
  have firstSucc' : (1 + (first : ℂ)) ≠ 0 := by
    simpa only [add_comm] using firstSucc
  have secondSucc' : (1 + (second : ℂ)) ≠ 0 := by
    simpa only [add_comm] using secondSucc
  rw [show (first : ℂ) + 1 + (second : ℂ) = first + second + 1 by ring]
  ring_nf
  field_simp [firstSucc, firstSucc', secondSucc, secondSucc', total, totalSucc, totalSucc']
  ring

def successorIndex (D : LatticeData) (index : Index D) : Index D :=
  (index.1, index.2 + 1)

def correctionConnection (D : LatticeData) (charge : Charge D) :
    Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D) :=
  mkDerivation ℂ fun coordinate => match coordinate with
    | none => -(X none ^ 2)
    | some index => (sourceWeight D index : ℂ) • X (some (successorIndex D index)) -
        ∑ colour : Fin D.rank, (charge colour : ℂ) • pairPolynomial D (colour, 0) index

private theorem connection_shift (D : LatticeData) (charge : Charge D) (degree : ℕ) :
    correctionConnection D charge (X none ^ degree) =
      -(degree : ℂ) • X none ^ (degree + 1) := by
  cases degree with
  | zero => simp
  | succ degree =>
    rw [Derivation.leibniz_pow]
    simp only [correctionConnection, mkDerivation_X,
      Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, smul_eq_mul,
      nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, map_neg, map_add, map_one,
      map_natCast, pow_succ]
    ring

private theorem connection_pair (D : LatticeData) (charge : Charge D)
    (first second : Index D) :
    correctionConnection D charge (pairPolynomial D first second) =
      -(sourceWeight D first + sourceWeight D second : ℂ) •
        (pairPolynomial D first second * X none) := by
  simp only [pairPolynomial, Derivation.leibniz, derivation_C, zero_smul, zero_add,
    smul_eq_mul, connection_shift, MvPolynomial.smul_eq_C_mul]
  rw [pow_succ]
  simp only [Nat.cast_add, map_neg, map_mul]
  ring

private theorem connection_singleton (D : LatticeData) (charge : Charge D)
    (index : Index D) :
    correctionConnection D charge (singletonPolynomial D charge index) =
      -(sourceWeight D index : ℂ) • (singletonPolynomial D charge index * X none) := by
  simp only [singletonPolynomial, Derivation.leibniz, derivation_C, zero_smul, zero_add,
    smul_eq_mul, connection_shift, MvPolynomial.smul_eq_C_mul]
  rw [pow_succ]
  simp only [map_neg, map_mul]
  ring

private theorem pair_polynomial_derivative (D : LatticeData) (first second : Index D) :
    (sourceWeight D first : ℂ) • pairPolynomial D (successorIndex D first) second +
        (sourceWeight D second : ℂ) • pairPolynomial D first (successorIndex D second) =
      -(sourceWeight D first + sourceWeight D second : ℂ) •
        (pairPolynomial D first second * X none) := by
  have scalar := pair_scalar_derivative (sourceWeight D first) (sourceWeight D second)
    (by simp [sourceWeight]) (by simp [sourceWeight])
  have lifted := congrArg (fun value : ℂ => (C (value * (D.G first.1 second.1 : ℂ)) *
    (X none ^ (sourceWeight D first + sourceWeight D second) * X none) : CorrectionPolynomial D))
    scalar
  simp only [pairPolynomial, successorIndex, sourceWeight, MvPolynomial.smul_eq_C_mul]
  rw [show first.2 + 1 + 1 + (second.2 + 1) = (first.2 + 1 + (second.2 + 1)) + 1 by omega,
    show first.2 + 1 + (second.2 + 1 + 1) = (first.2 + 1 + (second.2 + 1)) + 1 by omega,
    pow_succ]
  simpa only [sourceWeight, Nat.cast_add, Nat.cast_one, map_add, map_mul, map_neg,
    mul_assoc, add_mul, neg_mul] using lifted

private theorem connection_variable (D : LatticeData) (charge : Charge D) (index : Index D) :
    correctionConnection D charge (X (some index)) =
      (sourceWeight D index : ℂ) • X (some (successorIndex D index)) -
        ∑ colour, (charge colour : ℂ) • pairPolynomial D (colour, 0) index := by
  simp only [correctionConnection, mkDerivation_X]

private theorem correctionConnection_pair_commutator (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : CorrectionPolynomial D) :
    correctionConnection D charge (pairDerivation D index polynomial) -
        pairDerivation D index (correctionConnection D charge polynomial) =
      (sourceWeight D index : ℂ) • pairDerivation D (successorIndex D index) polynomial := by
  have derivations : ⁅correctionConnection D charge, pairDerivation D index⁆ =
      (sourceWeight D index : ℂ) • pairDerivation D (successorIndex D index) := by
    apply MvPolynomial.derivation_ext
    intro coordinate
    cases coordinate with
    | none =>
      rw [Derivation.commutator_apply, Derivation.smul_apply,
        show pairDerivation D index (X none) = 0 by
          simp only [pairDerivation, mkDerivation_X, Option.elim_none],
        show pairDerivation D (successorIndex D index) (X none) = 0 by
          simp only [pairDerivation, mkDerivation_X, Option.elim_none],
        show correctionConnection D charge (X none) = -(X none ^ 2) by
          simp only [correctionConnection, mkDerivation_X],
        map_zero, map_neg, pairDerivation_shift]
      simp
    | some other =>
      simp only [Derivation.commutator_apply, Derivation.smul_apply, pairDerivation_variable,
        connection_variable, map_sub, Derivation.map_smul, map_sum,
        pairDerivation_pair, smul_zero,
        Finset.sum_const_zero, sub_zero]
      have recurrence := pair_polynomial_derivative D index other
      rw [← connection_pair D charge index other] at recurrence
      rw [← recurrence]
      abel
  exact congrArg (fun derivation => derivation polynomial) derivations

private theorem charge_pair (D : LatticeData) (charge : Charge D) (index : Index D) :
    (∑ colour : Fin D.rank, (charge colour : ℂ) • pairPolynomial D (colour, 0) index) =
      C (pairScalar 1 (sourceWeight D index) *
        (bilinear D (unitCharge D index.1) charge : ℂ)) *
          X none ^ (sourceWeight D index + 1) := by
  have pairing : (∑ colour : Fin D.rank,
      (charge colour : ℂ) * (D.G colour index.1 : ℂ)) =
      (bilinear D (unitCharge D index.1) charge : ℂ) := by
    have original : bilinear D (unitCharge D index.1) charge =
        ∑ colour, D.G index.1 colour * charge colour := by simp [bilinear, unitCharge]
    rw [original]
    push_cast
    apply Finset.sum_congr rfl
    intro colour member
    rw [D.symmetric colour index.1]
    ring
  calc
    _ = ∑ colour : Fin D.rank,
        C (pairScalar 1 (sourceWeight D index) *
          ((charge colour : ℂ) * (D.G colour index.1 : ℂ))) *
            X none ^ (sourceWeight D index + 1) := by
      apply Finset.sum_congr rfl
      intro colour member
      simp only [pairPolynomial, sourceWeight, Nat.zero_add, Nat.add_comm 1,
        MvPolynomial.smul_eq_C_mul, map_mul]
      ring
    _ = _ := by
      rw [← Finset.sum_mul, ← map_sum, ← Finset.mul_sum, pairing]

private theorem connection_multiplier (D : LatticeData) (charge : Charge D)
    (index : Index D) :
    correctionConnection D charge (X (some index) + singletonPolynomial D charge index) =
      (sourceWeight D index : ℂ) •
        (X (some (successorIndex D index)) +
          singletonPolynomial D charge (successorIndex D index)) := by
  have scalar := singleton_scalar_derivative (sourceWeight D index)
  have coefficient :
      -(pairScalar 1 (sourceWeight D index) *
          (bilinear D (unitCharge D index.1) charge : ℂ)) -
        (sourceWeight D index : ℂ) * halfBinomial (sourceWeight D index) *
          (bilinear D (unitCharge D index.1) charge : ℂ) =
      (sourceWeight D index : ℂ) * halfBinomial (sourceWeight D index + 1) *
        (bilinear D (unitCharge D index.1) charge : ℂ) := by
    linear_combination -(bilinear D (unitCharge D index.1) charge : ℂ) * scalar
  rw [map_add, connection_variable, charge_pair, connection_singleton]
  simp only [singletonPolynomial, successorIndex, sourceWeight, MvPolynomial.smul_eq_C_mul,
    map_neg, map_mul, map_add, pow_succ]
  have lifted := congrArg (fun value : ℂ => (C value *
    (X none ^ sourceWeight D index * X none) : CorrectionPolynomial D)) coefficient
  simp only [sourceWeight, map_sub, map_neg, map_mul, mul_assoc] at lifted
  linear_combination lifted

private theorem correctionConnection_insertion (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : CorrectionPolynomial D) :
    correctionConnection D charge (insertion D charge index polynomial) =
      (sourceWeight D index : ℂ) • insertion D charge (successorIndex D index) polynomial +
        insertion D charge index (correctionConnection D charge polynomial) := by
  have pair := correctionConnection_pair_commutator D charge index polynomial
  have pair' := sub_eq_iff_eq_add.mp pair
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    smul_eq_mul]
  rw [map_add, Derivation.leibniz, connection_multiplier, pair']
  simp only [smul_eq_mul, MvPolynomial.smul_eq_C_mul]
  ring

def correctedSource (D : LatticeData) (charge : Charge D) :
    Oscillator D →ₗ[ℂ] CorrectionPolynomial D :=
  (optionEquivLeft ℂ (Index D)).symm.toLinearMap.comp (correctionPolynomial D charge)

private theorem correctedSource_eq_lift (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    correctedSource D charge polynomial = correctionLift D charge polynomial := by
  simp only [correctedSource, correctionPolynomial, correctionLift, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]

private theorem correctedSource_X_mul (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : Oscillator D) :
    correctedSource D charge (X index * polynomial) =
      insertion D charge index (correctedSource D charge polynomial) := by
  simpa only [correctedSource_eq_lift, mul_comm (X index) polynomial] using
    correctionLift_X_mul D charge index polynomial

private theorem correctedSource_oscillatorDerivation (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    correctedSource D charge (LatticeSugawaraConformal.oscillatorDerivation D polynomial) =
      correctionConnection D charge (correctedSource D charge polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    simp only [derivation_C, map_zero, correctedSource_eq_lift, correctionLift_C]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionProof =>
    rw [mul_comm polynomial (X index), Derivation.leibniz]
    have generator : LatticeSugawaraConformal.oscillatorDerivation D (X index) =
        (index.2 + 1 : ℂ) • (X (index.1, index.2 + 1) : Oscillator D) := by
      simp only [LatticeSugawaraConformal.oscillatorDerivation, mkDerivation_X]
    rw [generator]
    simp only [smul_eq_mul, map_add, correctedSource_X_mul, inductionProof]
    rw [mul_smul_comm, map_smul, mul_comm polynomial (X (index.1, index.2 + 1)),
      correctedSource_X_mul, correctionConnection_insertion]
    simp only [successorIndex, sourceWeight, Nat.cast_add, Nat.cast_one]
    ac_rfl

private theorem correctedSource_sectorTranslation (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    correctedSource D charge (LatticeSugawaraConformal.sectorTranslation D charge polynomial) =
      correctionConnection D charge (correctedSource D charge polynomial) +
        ∑ colour : Fin D.rank, (charge colour : ℂ) •
          insertion D charge (colour, 0) (correctedSource D charge polynomial) := by
  change correctedSource D charge
    (LatticeSugawaraConformal.oscillatorDerivation D polynomial +
      LatticeSugawaraConformal.chargePolynomial D charge * polynomial) = _
  rw [map_add, correctedSource_oscillatorDerivation]
  congr 1
  rw [LatticeSugawaraConformal.chargePolynomial, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro colour member
  rw [smul_mul_assoc, map_smul, correctedSource_X_mul]

theorem Corr_sectorTranslation (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    Corr D charge (LatticeSugawaraConformal.sectorTranslation D charge polynomial) =
      shiftCoefficients D ((optionEquivLeft ℂ (Index D))
        (correctionConnection D charge (correctedSource D charge polynomial) +
          ∑ colour : Fin D.rank, (charge colour : ℂ) •
            insertion D charge (colour, 0) (correctedSource D charge polynomial))) := by
  rw [← correctedSource_sectorTranslation]
  simp only [Corr, correctedSource, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply]

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation

