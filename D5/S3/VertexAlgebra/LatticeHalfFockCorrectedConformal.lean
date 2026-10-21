/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual corrected conformal state equals the native tensor stress field. -/
/-
Copyright (c) 2025 Kalle Kytölä; additional actual half-integer matrix
implementation copyright (c) 2026. Apache 2.0. Finite-support/contraction
architecture: VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4
through PolynomialFock bfd9ff0f15397a4fb933f36d701a60d325d84b08.
Normal-product organization retains Scott Carnahan (c) 2025, Apache 2.0,
vertexAlg 4453e34ec390e82a0c789c731ada8f9a6e86bdea.
Dong–Nagatomo math/9808088v1 §3.2 pp.12–14; rank/16 on p.19,
proof of 3.13(3), attributed there to FLM. Bakalov–Kac math/0402315v1
(4.4), (4.23)–(4.38). Historical proof mathematics is reused; no novelty claim.
-/

import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeActualConformalState

/-! The finite quadratic correction identifies the actual half-Fock conformal field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCoefficients LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField
open LatticeHalfFockCorrectedField LatticeHalfFock MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private theorem wordField_nil (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) : wordField D hu field [] = field := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [wordField_coefficient]
  change (∑ᶠ _ : Unit, field.coeff exponent vector) = _
  exact finsum_unique _

private theorem polynomialField_one (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) : polynomialField D hu charge 1 = chargedField D hu charge := by
  rw [show (1 : Oscillator D) = MvPolynomial.monomial 0 1 by simp,
    polynomialField_monomial_public,
    show LatticeHalfFockFockNormalField.occurrences D 0 = [] by
      simp [LatticeHalfFockFockNormalField.occurrences], wordField_nil]

/- Zero-charge creation, translation and ground action give the actual identity field. -/
private theorem current_halfCreation_zero_charge (D : LatticeData) :
    halfCreationExponential D 0 = 1 := by
  have series : halfCreationSeries D 0 = 0 := by
    ext degree
    simp [halfCreationSeries]
  rw [halfCreationExponential, series, PowerSeries.subst_zero_eq_C_constantCoeff,
    PowerSeries.constantCoeff_exp]
  simp

private theorem current_halfTranslation_zero_charge (D : LatticeData) (polynomial : Oscillator D) :
    halfTranslatedPolynomial D 0 polynomial = Polynomial.C polynomial := by
  have maps : MvPolynomial.eval₂AlgHom ℂ (halfTranslationVariable D 0) =
      (Polynomial.CAlgHom (R := ℂ) (A := Oscillator D)).comp
        (AlgHom.id ℂ (Oscillator D)) := by
    ext index
    simp [halfTranslationVariable, bilinear]
  rw [halfTranslatedPolynomial, maps]
  rfl

private theorem current_ground_zero_charge (D : LatticeData) (hu : IsUnit D.G.det) :
    groundAction D hu 0 = 1 := by
  have lift : groundLift D 0 = 1 := by
    apply congrArg QuotientGroup.mk
    rfl
  rw [groundAction, lift, map_one]

private theorem current_identity_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (exponent : ℤ) (state : ActualTensor D hu) :
    (FieldNormalProduct.identityField (V := ActualTensor D hu)).coeff exponent state =
      if exponent = 0 then state else 0 := by
  change ((HahnModule.of ℂ).symm
    ((FieldNormalProduct.identityField (V := ActualTensor D hu)) state)).coeff exponent = _
  rw [FieldNormalProduct.identityField, VertexOperator.of_coeff_apply_coeff]
  split_ifs <;> rfl

private theorem current_charged_zero_identity (D : LatticeData) (hu : IsUnit D.G.det) :
    chargedField D hu 0 = FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [chargedField, HVertexOperator.coeff_of_coeff]
  rw [current_identity_coefficient]
  have oscillator (polynomial : Oscillator D) :
      oscillatorCoefficient D 0 exponent polynomial = if exponent = 0 then polynomial else 0 := by
    change (∑ᶠ degree : ℕ, oscillatorTerm D 0 exponent polynomial degree) = _
    rw [finsum_eq_single _ 0]
    · simp only [oscillatorTerm, current_halfTranslation_zero_charge, Polynomial.coeff_C_zero,
        chargeNorm, bilinear, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        add_zero, halfCreationCoeff, current_halfCreation_zero_charge]
      by_cases zero : exponent = 0
      · simp [zero]
      · by_cases negative : exponent < 0
        · simp [negative, zero]
        · have positive : exponent.toNat ≠ 0 := by omega
          simp [negative, positive, zero]
    · intro degree nonzero
      simp only [oscillatorTerm, current_halfTranslation_zero_charge,
        Polynomial.coeff_C, ite_eq_right nonzero, zero_mul]
  induction vector using TensorProduct.induction_on with
  | zero => simp only [map_zero, ite_self]
  | tmul polynomial ground =>
    simp only [chargedCoefficient, chargeScalar, chargeNorm, bilinear, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, neg_zero, zpow_zero, one_smul,
      current_ground_zero_charge, TensorProduct.map_tmul, oscillator, Module.End.one_apply]
    by_cases zero : exponent = 0
    · simp only [zero, ite_true]
    · simp only [ite_eq_right zero, TensorProduct.zero_tmul]
  | add first second inductionFirst inductionSecond =>
    simp only [map_add, inductionFirst, inductionSecond]
    split_ifs <;> simp only [add_zero]


private theorem current_singleton_identity_current (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) :
    singletonLinear D hu (colour, 0) FieldNormalProduct.identityField =
      LatticeHalfFock.tensorCurrentField D (ActualGround D hu) colour := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [singletonLinear_coefficient, LatticeHalfFock.tensorCurrentField,
    HVertexOperator.coeff_of_coeff]
  have term (mode : ℤ) : flatTerm D hu FieldNormalProduct.identityField
      [(colour, 0)] exponent vector (mode, ()) =
      if exponent + 2 * mode + 3 = 0 then
        tensorCurrent D (ActualGround D hu) colour mode vector else 0 := by
    simp only [flatTerm, flatCoefficient, jetCurrent, jetScalar, Finset.range_zero,
      Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one,
      Nat.cast_zero, mul_zero, add_zero, one_smul]
    split_ifs <;> simp_all only [Module.End.mul_apply, current_identity_coefficient,
      ite_true, ite_false, map_zero]
  simp_rw [term]
  by_cases odd : exponent % 2 = 1
  · rw [currentCoeff, ite_eq_left odd]
    have chosen : exponent + 2 * ((-exponent - 3) / 2) + 3 = 0 := by omega
    rw [finsum_eq_single _ ((-exponent - 3) / 2)]
    · rw [ite_eq_left chosen]
      rfl
    · intro mode different
      rw [ite_eq_right (by omega)]
  · have outside (mode : ℤ) : exponent + 2 * mode + 3 ≠ 0 := by omega
    simp only [outside, ite_false, finsum_zero, currentCoeff, ite_eq_right odd]
    change 0 = tensorEndLinear D (ActualGround D hu) 0 vector
    rw [map_zero, LinearMap.zero_apply]

/- Tensor multiplication and current truncation control the pointwise normal pairs. -/
private theorem tensorEnd_mul_local (D : LatticeData) (hu : IsUnit D.G.det)
    (A B : Module.End ℂ (Oscillator D)) :
    tensorEnd D (ActualGround D hu) (A * B) =
      tensorEnd D (ActualGround D hu) A * tensorEnd D (ActualGround D hu) B := by
  apply TensorProduct.ext'
  intro p t
  simp only [tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
    Module.End.mul_apply]

private theorem tensorPair_eq_local (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (left right : ℤ) :
    tensorPair D (ActualGround D hu) i j left right =
      if left < 0 then tensorCurrent D (ActualGround D hu) i left *
        tensorCurrent D (ActualGround D hu) j right
      else tensorCurrent D (ActualGround D hu) j right *
        tensorCurrent D (ActualGround D hu) i left := by
  unfold tensorPair normalPair
  split_ifs <;> exact tensorEnd_mul_local D hu _ _

private theorem tensorPair_finite_local (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (m : ℤ) (v : ActualTensor D hu) :
    Function.HasFiniteSupport
      (fun mode : ℤ => tensorPair D (ActualGround D hu) i j mode (m-mode-1) v) := by
  obtain ⟨R, hR⟩ := tensor_current_truncation D (ActualGround D hu) v
  exact (Set.finite_Icc _ _).subset
    (tensorPair_support_of_bound D (ActualGround D hu) i j m v R hR)

/- Quadratic Corr retains occurrence multiplicities, including i=j. -/
private theorem pair_enumeration (D : LatticeData) (first second : Index D) :
    [first, second].Perm (LatticeAllStateField.occurrences D
      (Finsupp.single first 1 + Finsupp.single second 1)) := by
  rw [← Multiset.coe_eq_coe]
  simp [LatticeAllStateField.occurrences, Finsupp.toMultiset_add]
  rfl

private theorem quadratic_correction (D : LatticeData) (i j : Fin D.rank) :
    Corr D 0 (X (i, 0) * X (j, 0)) =
      Finsupp.single 0 (X (i, 0) * X (j, 0)) +
        Finsupp.single 2 (C ((1 / 8 : ℂ) * (D.G i j : ℂ))) := by
  have source := Corr_monomial_enumeration D 0
    (Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1)
    [(i, 0), (j, 0)] (pair_enumeration D _ _)
  have monomial : monomial (Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1) (1 : ℂ) =
      X (i, 0) * X (j, 0) := by
    simp [MvPolynomial.X]
  rw [monomial] at source
  rw [source]
  have word : correctionWord D 0 [(i, 0), (j, 0)] =
      X (some (i, 0)) * X (some (j, 0)) +
        C ((1 / 8 : ℂ) * (D.G i j : ℂ)) * X none ^ 2 := by
    rw [correctionWord_matching]
    simp [labelledRemainders, correctionWord, insertion, singletonPolynomial,
      bilinear, pairPolynomial, sourceWeight, pairScalar, halfBinomial]
    norm_num
  rw [word, map_add, map_mul, map_mul, map_pow,
    optionEquivLeft_X_some, optionEquivLeft_X_some, optionEquivLeft_C,
    optionEquivLeft_X_none, map_add]
  rw [← Polynomial.C_mul]
  change Finsupp.single 0 (X (i, 0) * X (j, 0)) +
    shiftCoefficients D (Polynomial.C (C ((1 / 8 : ℂ) * (D.G i j : ℂ))) *
      Polynomial.X ^ 2) = _
  apply congrArg (fun tail : ℕ →₀ Oscillator D =>
    Finsupp.single 0 (X (i, 0) * X (j, 0)) + tail)
  apply Finsupp.ext
  intro shift
  change (Polynomial.C (C ((1 / 8 : ℂ) * (D.G i j : ℂ))) *
    Polynomial.X ^ 2).coeff shift = _
  rw [Polynomial.coeff_C_mul_X_pow]
  simp only [Finsupp.single_apply, eq_comm]

private theorem normal_polynomial_pair (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) :
    polynomialField D hu 0 (X (i, 0) * X (j, 0)) =
      singletonLinear D hu (i, 0) (tensorCurrentField D (ActualGround D hu) j) := by
  rw [polynomialField_X_mul,
    show (X (j, 0) : Oscillator D) = X (j, 0) * 1 by rw [mul_one],
    polynomialField_X_mul, polynomialField_one, current_charged_zero_identity,
    current_singleton_identity_current]

private theorem shiftField_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) : shiftField D hu 0 field = field := by
  apply HVertexOperator.coeff_inj
  funext exponent
  rw [shiftField_coefficient_public]
  simp only [Nat.cast_zero, mul_zero, add_zero]

private theorem quadratic_field (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) :
    correctedField D hu (Finsupp.single 0 (X (i, 0) * X (j, 0))) =
      singletonLinear D hu (i, 0) (tensorCurrentField D (ActualGround D hu) j) +
        ((1 / 8 : ℂ) * (D.G i j : ℂ)) •
          shiftField D hu 2 FieldNormalProduct.identityField := by
  rw [correctedField, Finsupp.lsum_single]
  change (Finsupp.lsum ℂ (fun s : ℕ =>
    (shiftField D hu s).comp (polynomialField D hu 0)))
      (Corr D 0 (X (i, 0) * X (j, 0))) = _
  rw [quadratic_correction, map_add]
  simp only [Finsupp.lsum_single, LinearMap.comp_apply, shiftField_zero,
    normal_polynomial_pair]
  have constant : C ((1 / 8 : ℂ) * (D.G i j : ℂ)) =
      ((1 / 8 : ℂ) * (D.G i j : ℂ)) • (1 : Oscillator D) := by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]
  rw [constant, map_smul, polynomialField_one, current_charged_zero_identity, map_smul]

private theorem normal_pair_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (e : ℤ) (v : ActualTensor D hu) :
    (singletonLinear D hu (i, 0) (tensorCurrentField D (ActualGround D hu) j)).coeff e v =
      if e % 2 = 0 then
        ∑ᶠ mode : ℤ, tensorPair D (ActualGround D hu) i j mode (((-e-4)/2)-mode-1) v
      else 0 := by
  classical
  rw [singletonLinear_coefficient]
  by_cases even : e % 2 = 0
  · rw [ite_eq_left even]
    have identification (mode : ℤ) : flatTerm D hu
        (tensorCurrentField D (ActualGround D hu) j) [(i, 0)] e v (mode, ()) =
        tensorPair D (ActualGround D hu) i j mode (((-e-4)/2)-mode-1) v := by
      have parity : (e + 2 * mode + 3) % 2 = 1 := by omega
      have index : (-(e + 2 * mode + 3)-3)/2 = (-e-4)/2-mode-1 := by omega
      simp only [flatTerm, flatCoefficient, jetCurrent, jetScalar,
        Finset.range_zero, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one,
        div_one, one_smul, Nat.cast_zero, mul_zero, add_zero,
        tensorCurrentField, HVertexOperator.coeff_of_coeff, currentCoeff,
        ite_eq_left parity, index, tensorPair_eq_local]
      split_ifs <;> rfl
    have finite := tensorPair_finite_local D hu i j ((-e-4)/2) v
    have support : Function.support (fun mode : ℤ => flatTerm D hu
        (tensorCurrentField D (ActualGround D hu) j) [(i, 0)] e v (mode, ())) ⊆
        finite.toFinset := by
      intro mode member
      apply finite.mem_toFinset.mpr
      change tensorPair D (ActualGround D hu) i j mode (((-e-4)/2)-mode-1) v ≠ 0
      rw [← identification mode]
      exact member
    rw [finsum_eq_sum_of_support_subset _ support, finsum_eq_sum _ finite]
    exact Finset.sum_congr rfl (fun mode member => identification mode)
  · rw [ite_eq_right even]
    have parity (mode : ℤ) : (e + 2 * mode + 3) % 2 ≠ 1 := by omega
    have zero (mode : ℤ) : flatTerm D hu (tensorCurrentField D (ActualGround D hu) j)
        [(i, 0)] e v (mode, ()) = 0 := by
      simp only [flatTerm, flatCoefficient, tensorCurrentField,
        HVertexOperator.coeff_of_coeff, Nat.cast_zero, mul_zero, add_zero,
        currentCoeff, ite_eq_right (parity mode)]
      split_ifs <;> simp [tensorEnd]
    simp only [zero, finsum_zero]

private theorem shift_identity_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (v : ActualTensor D hu) :
    (shiftField D hu 2 FieldNormalProduct.identityField).coeff e v =
      if e = -4 then v else 0 := by
  rw [shiftField_coefficient_public, current_identity_coefficient]
  simp only [Nat.cast_ofNat,
    show (e + 2 * (2 : ℤ) = 0) ↔ e = -4 by omega]

private theorem raw_trace_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ℤ) (v : ActualTensor D hu) :
    (correctedField D hu (LatticeActualConformalState.omega D H)).coeff e v =
      (if e % 2 = 0 then tensorRawL D (ActualGround D hu) H ((-e-4)/2) v else 0) +
        (if e = -4 then ((∑ i, ∑ j, H i j * (D.G i j : ℂ)) / 16) • v else 0) := by
  classical
  unfold LatticeActualConformalState.omega LatticeActualConformalState.conformalPolynomial
  rw [← Finsupp.smul_single, map_smul]
  simp_rw [Finsupp.single_finsetSum, map_sum, ← Finsupp.smul_single, map_smul,
    quadratic_field]
  simp only [map_smul, map_sum, map_add, Pi.smul_apply, Pi.add_apply,
    Finset.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, normal_pair_coeff, shift_identity_coeff]
  by_cases even : e % 2 = 0
  · rw [ite_eq_left even, tensor_rawL_finsum]
    simp only [ite_eq_left even, smul_add, Finset.sum_add_distrib]
    by_cases shifted : e = -4
    · simp only [ite_eq_left shifted]
      congr 1
      simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv,
        Finset.sum_mul, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i member
      apply Finset.sum_congr rfl
      intro j member
      congr 1
      ring
    · simp [ite_eq_right shifted]
  · have shifted : e ≠ -4 := by intro equality; subst e; norm_num at even
    simp only [ite_eq_right even, ite_eq_right shifted, smul_zero, add_zero, Finset.sum_const_zero]

/- The left inverse fixes the Gram contraction, including the empty rank. -/
private theorem inverse_trace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) :
    ∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l*(D.G i l : ℂ) = (D.rank : ℂ) := by
  have row (i : Fin D.rank) : ∑ l, H i l*(D.G i l : ℂ) = 1 := by
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i i) hHG
    simpa [Matrix.mul_apply, gramComplex, D.symmetric i] using h
  simp_rw [row]
  simp

/-- The actual corrected quadratic source gives every coefficient of the native
half-integer tensor stress field, with its exact rank/16 vacuum shift.
The only matrix premise is the genuine left inverse; rank zero is included. -/
theorem correctedField_omega (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) :
    correctedField D hu (LatticeActualConformalState.omega D H) =
      tensorStressField D (ActualGround D hu) H := by
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro v
  rw [raw_trace_coeff, inverse_trace D H hHG]
  rw [tensorStressField, HVertexOperator.coeff_of_coeff]
  by_cases even : e % 2 = 0
  · have shifted : (-e-4)/2 = 0 ↔ e = -4 := by omega
    change _ = (tensorEndLinear D (ActualGround D hu) (stressCoeff D H e)) v
    simp only [stressCoeff, ite_eq_left even, L, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, shifted]
    change tensorRawL D (ActualGround D hu) H ((-e-4)/2) v +
      (if e = -4 then ((D.rank : ℂ) / 16) • v else 0) =
      tensorRawL D (ActualGround D hu) H ((-e-4)/2) v +
        (if e = -4 then (D.rank : ℂ) / 16 else 0) • tensorEnd D (ActualGround D hu) 1 v
    congr 1
    split_ifs
    · change ((D.rank : ℂ) / 16) • v =
        ((D.rank : ℂ) / 16) • (TensorProduct.map LinearMap.id LinearMap.id) v
      rw [TensorProduct.map_id, LinearMap.id_apply]
    · simp only [zero_smul]
  · have shifted : e ≠ -4 := by intro equality; subst e; norm_num at even
    simp only [stressCoeff, ite_eq_right even, ite_eq_right shifted, add_zero]
    change 0 = tensorEndLinear D (ActualGround D hu) 0 v
    rw [map_zero, LinearMap.zero_apply]

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
