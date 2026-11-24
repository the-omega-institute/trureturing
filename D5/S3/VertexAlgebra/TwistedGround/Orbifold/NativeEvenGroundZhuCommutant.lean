/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeEvenGroundZhuCommutant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeEvenGroundZhuCommutant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed charged zero modes and their scalar commutant on the actual even twisted top. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance
import D5.S3.VertexAlgebra.HalfFock.GroundCompression
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy

/-!
The invariant exponential sum acts on the even twisted top by twice the native
charged normalization times the selected ground operator. The integral lifts of
mod-two charges therefore act by nonzero multiples of the ground operator basis.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedMonodromy
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace LatticeHalfFockParityT
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockGroundCompression (iota pi ground_retraction)
open TwistedGround.OperatorAlgebra

open private creation_zero from
  D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

noncomputable section

variable (D : LatticeData) (hu : IsUnit D.G.det)

private theorem oddWeight_eq_zero_iff (m : OddMonomial D) : oddWeight D m = 0 ↔ m = 0 := by
  constructor
  · intro h
    ext i
    have hi := oddFiber_exponent_bound D 0 ⟨m, h⟩ i
    exact Nat.eq_zero_of_le_zero hi
  · rintro rfl
    exact map_zero (Finsupp.weight (LatticeHalfFockChargedCoefficients.omega D))

private theorem vacuum_mem_grade (x : ActualGround D hu) :
    iota D hu x ∈ actualGrade D hu 0 := by
  apply (actual_grade_mem_iff_repr_support D hu 0 _).mpr
  rintro ⟨m, b⟩ hb
  apply (oddWeight_eq_zero_iff D m).mpr
  by_contra hm
  have hz : ((actualAmbientBasis D hu).repr (iota D hu x)) (m, b) = 0 := by
    simp only [actualAmbientBasis, iota, TensorProduct.mk_apply,
      Module.Basis.tensorProduct_repr_tmul_apply]
    change _ • (1 : Oscillator D).coeff m = 0
    rw [MvPolynomial.coeff_one, ite_eq_right (Ne.symm hm), smul_zero]
  exact Finsupp.mem_support_iff.mp hb hz

private theorem gradeZero_le_vacuum_range :
    actualGrade D hu 0 ≤ LinearMap.range (iota D hu) := by
  rw [actual_grade_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨⟨m, hm⟩, b⟩, rfl⟩
  refine ⟨Pi.single b 1, ?_⟩
  have hm0 := (oddWeight_eq_zero_iff D m).mp hm
  subst m
  rw [actualGradeVector, actual_basis_apply]
  simp [iota]

private def evenTopVacuum : ActualGround D hu →ₗ[ℂ] twistedTop D hu false :=
  LinearMap.codRestrict _ (LinearMap.codRestrict (paritySpace D hu (paritySign false))
    (iota D hu) (fun x => by
      change iota D hu x ∈ LinearMap.ker (actualParity D hu - (1 : ℂ) • LinearMap.id)
      have h := actualParity_on_actualGrade D hu 0 ⟨iota D hu x, vacuum_mem_grade D hu x⟩
      simpa only [pow_zero, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero] using h))
    (fun x => vacuum_mem_grade D hu x)

/-- The actual even top is the vacuum tensor of the selected ground representation.
The inverse reads the constant oscillator coefficient. -/
def evenTopGroundEquiv : ActualGround D hu ≃ₗ[ℂ] twistedTop D hu false := by
  let read := (pi D hu).comp
    ((paritySpace D hu (paritySign false)).subtype.comp (twistedTop D hu false).subtype)
  refine LinearEquiv.ofLinearMap (evenTopVacuum D hu) read ?_ ?_
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    change iota D hu (pi D hu v.val.val) = v.val.val
    obtain ⟨x, hx⟩ := gradeZero_le_vacuum_range D hu v.property
    change iota D hu x = v.val.val at hx
    rw [← hx]
    exact congrArg (iota D hu) (LinearMap.congr_fun (ground_retraction D hu) x)
  · exact ground_retraction D hu

@[simp] theorem evenTopGroundEquiv_val (x : ActualGround D hu) :
    ((evenTopGroundEquiv D hu) x).val.val = (1 : Oscillator D) ⊗ₜ[ℂ] x := rfl

@[simp] theorem evenTopGroundEquiv_symm_apply (v : twistedTop D hu false) :
    (evenTopGroundEquiv D hu).symm v = pi D hu v.val.val := rfl

/-- The weight of the invariant exponential sum in the actual untwisted grading. -/
theorem fixedChargedVacuum_grade (c : Charge D) :
    (fixedChargedVacuum D c).val ∈ grade D (chargeEnergy D c) := by
  have hg (a : Charge D) : Finsupp.single a (1 : Oscillator D) ∈ grade D (chargeEnergy D a) := by
    simpa only [Nat.cast_zero, add_zero] using
      Lattice.ActualZhuCurrentRelations.single_weighted_grade D a 1 0
        (MvPolynomial.isWeightedHomogeneous_one ℂ (oscillatorWeight D))
  have hn : chargeEnergy D (-c) = chargeEnergy D c := by
    change chargeNorm D (-c) / 2 = chargeNorm D c / 2
    rw [norm_neg]
  exact Submodule.add_mem _ (hg c) (hn ▸ hg (-c))

variable (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

/-- The actual Zhu zero mode of the invariant exponential sum on the even twisted top. -/
def fixedChargedTopZero (c : Charge D) : Module.End ℂ (twistedTop D hu false) :=
  fixedTopZero false (fixedChargedVacuum D c) (chargeEnergy D c).toNat
    (by simpa only [Int.toNat_of_nonneg (chargeEnergy_nonneg D hD c)] using
      fixedChargedVacuum_grade D c)

/-- The exact doubled-coordinate zero mode after conjugation to the selected ground space. -/
theorem fixedChargedTopZero_conj (c : Charge D) :
    (evenTopGroundEquiv D hu).symm.conjAlgEquiv ℂ (fixedChargedTopZero D hu hD c) =
      ((2 : ℂ) * chargeScalar D c) • groundAction D hu c := by
  apply LinearMap.ext
  intro x
  change (evenTopGroundEquiv D hu).symm
      (fixedChargedTopZero D hu hD c ((evenTopGroundEquiv D hu) x)) = _
  apply (evenTopGroundEquiv D hu).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  change (correctedField D hu (fixedChargedVacuum D c).val).coeff
      (2 * (-(((chargeEnergy D c).toNat : ℤ) - 1) - 1))
      (((evenTopGroundEquiv D hu) x).val.val) = _
  rw [Int.toNat_of_nonneg (chargeEnergy_nonneg D hD c)]
  have he : 2 * (-(chargeEnergy D c - 1) - 1) = -chargeNorm D c := by
    have h := two_chargeEnergy D c
    change 2 * chargeEnergy D c = chargeNorm D c at h
    omega
  rw [he, evenTopGroundEquiv_val, evenTopGroundEquiv_val]
  change (correctedField D hu (Finsupp.single c 1 + Finsupp.single (-c) 1)).coeff
      (-chargeNorm D c) ((1 : Oscillator D) ⊗ₜ[ℂ] x) = _
  simp only [map_add, Pi.add_apply, LinearMap.add_apply,
    corrected_singleton_coeff_charged, chargedField, HVertexOperator.coeff_of_coeff,
    charged_vacuum_coefficient, norm_neg, neg_add_cancel, creation_zero, ground_neg]
  rw [show chargeScalar D (-c) = chargeScalar D c by simp only [chargeScalar, norm_neg],
    ← add_smul, ← two_mul, LinearMap.smul_apply, TensorProduct.tmul_smul]

/-- The native normalization of the fixed charged zero mode is nonzero. -/
theorem fixedChargedScalar_ne_zero (c : Charge D) :
    (2 : ℂ) * chargeScalar D c ≠ 0 :=
  mul_ne_zero (by norm_num) (zpow_ne_zero _ (by norm_num))

private theorem selectedGroundAlgebra :
    Nonempty (GroundAlgebra D (groundRank D hu) (groundRepresentation D hu)) := by
  have selected := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))
  exact actual_operator_algebra D hu (groundRank D hu) selected.1
    (groundRepresentation D hu) selected.2.2.1

/-- The commutant of the actual fixed charged Zhu zero modes on the even top is scalar. -/
theorem fixedChargedTopZero_scalar_commutant (A : Module.End ℂ (twistedTop D hu false)) :
    (∀ c : Charge D, A * fixedChargedTopZero D hu hD c = fixedChargedTopZero D hu hD c * A) ↔
      ∃ z : ℂ, A = z • 1 := by
  constructor
  · intro h
    obtain ⟨algebra⟩ := selectedGroundAlgebra D hu
    let E := (evenTopGroundEquiv D hu).symm.conjAlgEquiv ℂ
    have hcomm (a : ModTwoCharge D) :
        E A * chargeOperator D (groundRepresentation D hu) a =
          chargeOperator D (groundRepresentation D hu) a * E A := by
      let c := integralLift D a
      have hc := congrArg E (h c)
      rw [map_mul, map_mul] at hc
      change E A * (evenTopGroundEquiv D hu).symm.conjAlgEquiv ℂ
        (fixedChargedTopZero D hu hD c) =
        (evenTopGroundEquiv D hu).symm.conjAlgEquiv ℂ (fixedChargedTopZero D hu hD c) * E A at hc
      rw [fixedChargedTopZero_conj, mul_smul_comm, smul_mul_assoc] at hc
      exact smul_right_injective (Module.End ℂ (ActualGround D hu)) (fixedChargedScalar_ne_zero D c) hc
    obtain ⟨z, hz⟩ := (algebra.scalar_commutant (E A)).mp hcomm
    refine ⟨z, E.injective ?_⟩
    simpa only [map_smul, map_one] using hz
  · rintro ⟨z, rfl⟩ c
    rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- Zero modes of the integral mod-two representatives already span the full endomorphism space. -/
theorem fixedChargedTopZero_span :
    Submodule.span ℂ (Set.range (fun a : ModTwoCharge D =>
      fixedChargedTopZero D hu hD (integralLift D a))) = ⊤ := by
  obtain ⟨algebra⟩ := selectedGroundAlgebra D hu
  let E := (evenTopGroundEquiv D hu).symm.conjAlgEquiv ℂ
  apply (Submodule.map_injective_of_injective (f := E.toLinearMap) E.injective)
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr E.surjective, Submodule.map_span]
  refine top_unique ?_
  rw [← algebra.full_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  let c := integralLift D a
  let k := (2 : ℂ) * chargeScalar D c
  have hc : E (fixedChargedTopZero D hu hD c) ∈
      Submodule.span ℂ (E.toLinearMap '' Set.range (fun b : ModTwoCharge D =>
        fixedChargedTopZero D hu hD (integralLift D b))) :=
    Submodule.subset_span ⟨_, ⟨a, rfl⟩, rfl⟩
  have hop : E (fixedChargedTopZero D hu hD c) =
      k • chargeOperator D (groundRepresentation D hu) a := fixedChargedTopZero_conj D hu hD c
  rw [hop] at hc
  have hscaled := Submodule.smul_mem _ k⁻¹ hc
  rwa [smul_smul, inv_mul_cancel₀ (fixedChargedScalar_ne_zero D c), one_smul] at hscaled

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
