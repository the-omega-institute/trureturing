/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged singleton coefficients by ground recurrence and creation induction. -/

/- Classical twisted-lattice coefficient calculation, adapted from the
   cut-zero proof cone of OriginalTranslation and its FirstDescendant,
   FirstDescendantCuts, ChargedTranslation and ChargedTranslationExtension
   suppliers. The owning Scribe gives their source digests and attribution.
   Inherited half-Fock construction: copyright (c) 2025 Kalle Kytölä;
   additional actual half-integer matrix implementation copyright (c) 2026.
   Released under Apache 2.0. No mathematical novelty is claimed. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

/-! The charged singleton physical coefficient law on the actual tensor carrier. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFock MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private def currentCombination (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (mode : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  ∑ colour, h colour • tensorCurrent D (ActualGround D hu) colour mode

/-- A finite linear combination of the existing canonical word-field coefficients. -/
private def weightedWord (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent : ℤ) :
    Module.End ℂ (ActualTensor D hu) :=
  ∑ colour, h colour • (wordField D hu (chargedField D hu a) [(colour, 0)]).coeff exponent

/-- The actual singleton flat terms, before their pointwise finite summation. -/
private def modeSummand (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent mode : ℤ)
    (vector : ActualTensor D hu) : ActualTensor D hu :=
  ∑ colour, h colour •
    flatTerm D hu (chargedField D hu a) [(colour, 0)] exponent vector (mode, ())

private theorem singleton_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (colour : Fin D.rank) (exponent : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (fun mode : ℤ =>
      flatTerm D hu (chargedField D hu a) [(colour, 0)] exponent vector (mode, ())) :=
  (flatTerm_finite D hu (chargedField D hu a) [(colour, 0)] exponent vector).fun_comp_of_injective (fun _ _ equality => (Prod.mk.inj equality).1)

private theorem modeSummand_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (fun mode => modeSummand D hu h a exponent mode vector) := by
  classical
  exact Function.HasFiniteSupport.sum (fun colour =>
    (singleton_finite D hu a colour exponent vector).fun_comp (smul_zero (h colour))) Finset.univ

private theorem weightedWord_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent : ℤ) (vector : ActualTensor D hu) :
    weightedWord D hu h a exponent vector =
      ∑ᶠ mode : ℤ, modeSummand D hu h a exponent mode vector := by
  classical
  have singleton (colour : Fin D.rank) :
      (∑ᶠ modes : ModeTuple D [(colour, 0)],
        flatTerm D hu (chargedField D hu a) [(colour, 0)] exponent vector modes) =
      ∑ᶠ mode : ℤ,
        flatTerm D hu (chargedField D hu a) [(colour, 0)] exponent vector (mode, ()) := by
    symm
    apply finsum_eq_of_bijective (fun mode : ℤ => (mode, ()))
    · constructor
      · intro first second equality
        exact (Prod.mk.inj equality).1
      · rintro ⟨mode, tail⟩
        cases tail
        exact ⟨mode, rfl⟩
    · intro mode
      rfl
  simp only [weightedWord, LinearMap.sum_apply, LinearMap.smul_apply,
    wordField_coefficient, singleton, modeSummand]
  rw [finsum_sum_comm Finset.univ _ (fun colour _ =>
    (singleton_finite D hu a colour exponent vector).fun_comp (smul_zero (h colour)))]
  apply Finset.sum_congr rfl
  intro colour member
  exact smul_finsum' (h colour) (singleton_finite D hu a colour exponent vector)

private theorem modeSummand_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent mode : ℤ)
    (vector : ActualTensor D hu) :
    modeSummand D hu h a exponent mode vector =
      if mode < 0 then
        currentCombination D hu h mode
          (chargedCoefficient D hu a (exponent + 2 * mode + 3) vector)
      else chargedCoefficient D hu a (exponent + 2 * mode + 3)
        (currentCombination D hu h mode vector) := by
  classical
  have coefficient (n : ℤ) :
      (chargedField D hu a).coeff n = chargedCoefficient D hu a n := by
    rw [chargedField, HVertexOperator.coeff_of_coeff]
  by_cases negative : mode < 0 <;>
    simp only [modeSummand, flatTerm, flatCoefficient, jetCurrent, jetScalar,
      Finset.range_zero, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one,
      div_one, one_smul, Nat.cast_zero, mul_zero, add_zero, coefficient,
      negative, reduceIte, currentCombination, LinearMap.sum_apply,
      LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul]

private def creationDerivativeTerm (D : LatticeData) (charge : Charge D) (degree : ℤ)
    (offset : ℕ) : Oscillator D :=
  (∑ colour : Fin D.rank, (charge colour : ℂ) • X (colour, offset)) *
    halfCreationCoeff D charge (degree - 1 - 2 * offset)

private theorem creationDerivativeTerm_finite (D : LatticeData) (charge : Charge D)
    (degree : ℤ) : Function.HasFiniteSupport (creationDerivativeTerm D charge degree) := by
  apply (Finset.range (degree.toNat + 1)).finite_toSet.subset
  intro offset member
  by_contra outside
  have bound : degree - 1 - 2 * (offset : ℤ) < 0 := by
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
    omega
  exact member (by simp [creationDerivativeTerm, halfCreationCoeff, bound])

set_option maxHeartbeats 2000000 in
private theorem creation_derivative_natural (D : LatticeData) (charge : Charge D)
    (degree : ℕ) :
    (degree + 1 : ℂ) • PowerSeries.coeff (degree + 1) (halfCreationExponential D charge) =
      (2 : ℂ) • ∑ offset ∈ Finset.range (degree / 2 + 1),
        creationDerivativeTerm D charge (degree + 1) offset := by
  have differentiated := congrArg (PowerSeries.coeff degree) (exponential_derivative D charge)
  rw [PowerSeries.coeff_derivative, mul_comm (halfCreationExponential D charge),
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at differentiated
  have scalar : (degree + 1 : Oscillator D) =
      algebraMap ℂ (Oscillator D) (degree + 1 : ℂ) := by simp
  rw [scalar, mul_comm _ (algebraMap ℂ (Oscillator D) (degree + 1 : ℂ)),
    ← Algebra.smul_def] at differentiated
  rw [differentiated]
  simp only [series_derivative_coeff, ite_mul, zero_mul,
    smul_mul_assoc]
  rw [← Finset.sum_filter]
  rw [← Finset.smul_sum]
  apply congrArg (fun polynomial : Oscillator D => (2 : ℂ) • polynomial)
  symm
  apply Finset.sum_bij (fun offset _ => 2 * offset)
  · intro offset member
    simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
    omega
  · intro first firstMember second secondMember equality
    omega
  · intro index member
    simp only [Finset.mem_filter, Finset.mem_range] at member
    refine ⟨index / 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro offset member
    have bound : 2 * offset ≤ degree := by
      simp only [Finset.mem_range] at member
      omega
    have equality : (degree : ℤ) + 1 - 1 - 2 * offset =
        ((degree - 2 * offset : ℕ) : ℤ) := by
      omega
    simp only [creationDerivativeTerm, equality, halfCreationCoeff,
      ite_eq_right (by omega : ¬ ((degree - 2 * offset : ℕ) : ℤ) < 0),
      Int.toNat_natCast, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

private theorem creation_physical_recurrence (D : LatticeData) (charge : Charge D)
    (degree : ℤ) :
    ((degree : ℂ) / 2) • halfCreationCoeff D charge degree =
      ∑ᶠ offset : ℕ, creationDerivativeTerm D charge degree offset := by
  by_cases positive : 0 < degree
  · have natural : degree = ((degree - 1).toNat + 1 : ℕ) := by omega
    have differentiated := creation_derivative_natural D charge (degree - 1).toNat
    rw [show ((degree - 1).toNat : ℤ) + 1 = degree by omega] at differentiated
    have contained : Function.support (creationDerivativeTerm D charge degree) ⊆
        Finset.range ((degree - 1).toNat / 2 + 1) := by
      intro offset member
      by_contra outside
      have bound : degree - 1 - 2 * (offset : ℤ) < 0 := by
        simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
        omega
      exact member (by simp [creationDerivativeTerm, halfCreationCoeff, bound])
    rw [finsum_eq_sum_of_support_subset _ contained]
    have coefficient : halfCreationCoeff D charge degree =
        PowerSeries.coeff ((degree - 1).toNat + 1) (halfCreationExponential D charge) := by
      simp only [halfCreationCoeff, ite_eq_right (by omega : ¬ degree < 0)]
      rw [show degree.toNat = (degree - 1).toNat + 1 by omega]
    rw [coefficient]
    have factor : (degree : ℂ) / 2 = (1 / 2 : ℂ) * ((degree - 1).toNat + 1 : ℂ) := by
      have cast : (degree : ℂ) = ((degree - 1).toNat + 1 : ℂ) := by exact_mod_cast natural
      rw [cast]
      ring
    rw [factor, mul_smul, differentiated, smul_smul]
    norm_num
  · have allZero : creationDerivativeTerm D charge degree = 0 := by
      funext offset
      simp [creationDerivativeTerm, halfCreationCoeff,
        show degree - 1 - 2 * (offset : ℤ) < 0 by omega]
    rw [allZero]
    by_cases zero : degree = 0
    · subst degree
      simp
    · simp [halfCreationCoeff, show degree < 0 by omega]

private theorem ground_left_term (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (ground : ActualGround D hu) (offset : ℕ) :
    modeSummand D hu (fun colour => (charge colour : ℂ)) charge exponent (-(offset : ℤ) - 1)
      ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
      chargeScalar D charge •
        (creationDerivativeTerm D charge (exponent + chargeNorm D charge + 2) offset ⊗ₜ[ℂ]
          groundAction D hu charge ground) := by
  rw [modeSummand_eq, ite_eq_left (by omega : -(offset : ℤ) - 1 < 0)]
  simp only [charged_vacuum_coefficient, currentCombination,
    LinearMap.sum_apply, LinearMap.smul_apply, map_smul]
  simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
    current_negative, LinearMap.mulLeft_apply]
  rw [show exponent + 2 * (-(offset : ℤ) - 1) + 3 + chargeNorm D charge =
      exponent + chargeNorm D charge + 2 - 1 - 2 * offset by omega]
  simp only [creationDerivativeTerm, Finset.sum_mul, smul_mul_assoc,
    TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', Finset.smul_sum]


private theorem ground_right_term (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (ground : ActualGround D hu) (offset : ℕ) :
    modeSummand D hu (fun colour => (charge colour : ℂ)) charge exponent offset
      ((1 : Oscillator D) ⊗ₜ[ℂ] ground) = 0 := by
  have currentZero : currentCombination D hu (fun colour => (charge colour : ℂ))
      (offset : ℤ) ((1 : Oscillator D) ⊗ₜ[ℂ] ground) = 0 := by
    have vanished (colour : Fin D.rank) : current D colour offset (1 : Oscillator D) = 0 :=
      current_vanish D colour 1 _ (by simp [bound])
    simp [currentCombination, tensorCurrent, tensorEnd, vanished]
  rw [modeSummand_eq, ite_eq_right (by omega : ¬ (offset : ℤ) < 0), currentZero, map_zero]

private theorem ground_reindex (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (ground : ActualGround D hu) :
    (∑ᶠ mode : ℤ, modeSummand D hu (fun colour => (charge colour : ℂ)) charge
      exponent mode ((1 : Oscillator D) ⊗ₜ[ℂ] ground)) =
    ∑ᶠ offset : ℕ, modeSummand D hu (fun colour => (charge colour : ℂ)) charge
      exponent (-(offset : ℤ) - 1) ((1 : Oscillator D) ⊗ₜ[ℂ] ground) := by
  let term := fun mode : ℤ => modeSummand D hu (fun colour => (charge colour : ℂ))
    charge exponent mode ((1 : Oscillator D) ⊗ₜ[ℂ] ground)
  have negative_range : Set.range (fun offset : ℕ => -(offset : ℤ) - 1) = Set.Iio 0 := by
    ext mode
    constructor
    · rintro ⟨offset, rfl⟩
      simp only [Set.mem_Iio]
      omega
    · intro member
      refine ⟨(-mode - 1).toNat, ?_⟩
      have cast := Int.toNat_of_nonneg (show 0 ≤ -mode - 1 by
        simp only [Set.mem_Iio] at member; omega)
      dsimp only
      omega
  calc
    _ = ∑ᶠ mode ∈ Set.Iio (0 : ℤ), term mode := by
      apply finsum_congr
      intro mode
      by_cases negative : mode < 0
      · simp [finsum_eq_if, negative, term]
      · have nonnegative : 0 ≤ mode := by omega
        have cast : (mode.toNat : ℤ) = mode := Int.toNat_of_nonneg nonnegative
        have zero := ground_right_term D hu charge exponent ground mode.toNat
        rw [cast] at zero
        simp [negative, term, zero]
    _ = _ := by
      rw [← negative_range]
      exact finsum_mem_range (fun first second equal => by omega)

/-- On a charged ground, the nonnegative current cut vanishes.  The
    remaining finite sum is the actual exponential derivative coefficient,
    not a field-translation assumption. -/
private theorem weightedWord_ground (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (ground : ActualGround D hu) :
    weightedWord D hu (fun colour => (charge colour : ℂ)) charge exponent
        ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
      (((exponent + chargeNorm D charge + 2 : ℤ) : ℂ) / 2) •
        chargedCoefficient D hu charge (exponent + 2) ((1 : Oscillator D) ⊗ₜ[ℂ] ground) := by
  let tensorMap : Oscillator D →ₗ[ℂ] ActualTensor D hu :=
    chargeScalar D charge •
      (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu)).flip
        (groundAction D hu charge ground)
  have summed := tensorMap.toAddMonoidHom.map_finsum
    (creationDerivativeTerm_finite D charge (exponent + chargeNorm D charge + 2))
  change tensorMap (∑ᶠ offset : ℕ,
      creationDerivativeTerm D charge (exponent + chargeNorm D charge + 2) offset) =
    (∑ᶠ offset : ℕ, chargeScalar D charge •
      (creationDerivativeTerm D charge (exponent + chargeNorm D charge + 2) offset ⊗ₜ[ℂ]
        groundAction D hu charge ground)) at summed
  have vacuum := charged_vacuum_coefficient D hu charge (exponent + 2) ground
  rw [show exponent + 2 + chargeNorm D charge =
      exponent + chargeNorm D charge + 2 by omega] at vacuum
  change chargedCoefficient D hu charge (exponent + 2) ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
    tensorMap (halfCreationCoeff D charge (exponent + chargeNorm D charge + 2)) at vacuum
  rw [weightedWord_sum, ground_reindex]
  simp only [ground_left_term]
  rw [← summed, ← creation_physical_recurrence, map_smul, ← vacuum]

private theorem charged_creation_relation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (exponent : ℤ) (vector : ActualTensor D hu) :
    chargedCoefficient D hu charge exponent
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (chargedCoefficient D hu charge exponent vector) -
      (bilinear D (unitCharge D index.1) charge : ℂ) •
        chargedCoefficient D hu charge (exponent + 2 * index.2 + 1) vector := by
  have ward := congrArg (fun operator : Module.End ℂ (ActualTensor D hu) => operator vector)
    (charged_tensor_current_ward D hu index.1 charge (-(index.2 : ℤ) - 1) exponent)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at ward
  rw [show exponent - (2 * (-(index.2 : ℤ) - 1) + 1) =
      exponent + 2 * index.2 + 1 by omega] at ward
  exact eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp ward).symm

private theorem tensor_creation_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (index : Index D) (mode : ℤ) (vector : ActualTensor D hu) :
    tensorCurrent D (ActualGround D hu) colour mode
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) -
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (tensorCurrent D (ActualGround D hu) colour mode vector) =
      (if mode = (index.2 : ℤ) then frequency mode * (D.G colour index.1 : ℂ) else 0) •
        vector := by
  induction vector using TensorProduct.inductionOn with
  | tmul polynomial ground =>
    simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [← TensorProduct.sub_tmul, current_heisenberg_apply]
    by_cases same : mode = (index.2 : ℤ)
    · rw [ite_eq_left (by omega : mode + (-(index.2 : ℤ) - 1) + 1 = 0), ite_eq_left same,
        ← TensorProduct.smul_tmul']
    · rw [ite_eq_right (by omega : mode + (-(index.2 : ℤ) - 1) + 1 ≠ 0), ite_eq_right same]
      simp
  | add first second firstProof secondProof =>
    simp only [map_add, add_sub_add_comm, firstProof, secondProof, smul_add]

private theorem combination_creation_relation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (mode : ℤ) (vector : ActualTensor D hu) :
    currentCombination D hu (fun colour => (charge colour : ℂ)) mode
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (currentCombination D hu (fun colour => (charge colour : ℂ)) mode vector) +
      (if mode = (index.2 : ℤ) then
        frequency mode * (bilinear D (unitCharge D index.1) charge : ℂ) else 0) • vector := by
  apply sub_eq_iff_eq_add'.mp
  simp only [currentCombination, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, ← smul_sub, ← Finset.sum_sub_distrib, tensor_creation_commutator,
    smul_smul, ← Finset.sum_smul]
  congr 1
  by_cases same : mode = (index.2 : ℤ)
  · simp only [ite_eq_left same]
    rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D (unitCharge D index.1)]
    simp only [bilinear, unitCharge, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Int.cast_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro colour member
    simp only [Finset.mem_univ, ite_true, Int.cast_mul]
    ring
  · simp [same]

private theorem modeSummand_creation_relation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (exponent mode : ℤ) (vector : ActualTensor D hu) :
    modeSummand D hu (fun colour => (charge colour : ℂ)) charge exponent mode
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (modeSummand D hu (fun colour => (charge colour : ℂ)) charge exponent mode vector) -
      (bilinear D (unitCharge D index.1) charge : ℂ) •
        modeSummand D hu (fun colour => (charge colour : ℂ)) charge
          (exponent + 2 * index.2 + 1) mode vector +
      if mode = (index.2 : ℤ) then
        (frequency mode * (bilinear D (unitCharge D index.1) charge : ℂ)) •
          chargedCoefficient D hu charge (exponent + 2 * index.2 + 3) vector else 0 := by
  by_cases negative : mode < 0
  · have distinct : mode ≠ (index.2 : ℤ) := by omega
    simp only [modeSummand_eq, ite_eq_left negative, ite_eq_right distinct, add_zero]
    rw [charged_creation_relation, map_sub, map_smul, combination_creation_relation]
    simp only [ite_eq_right distinct, zero_smul, add_zero]
    rw [show exponent + 2 * mode + 3 + 2 * index.2 + 1 =
        exponent + 2 * index.2 + 1 + 2 * mode + 3 by omega]
  · simp only [modeSummand_eq, ite_eq_right negative]
    rw [combination_creation_relation, map_add, map_smul, charged_creation_relation]
    rw [show exponent + 2 * mode + 3 + 2 * index.2 + 1 =
        exponent + 2 * index.2 + 1 + 2 * mode + 3 by omega]
    by_cases same : mode = (index.2 : ℤ)
    · rw [ite_eq_left same, ite_eq_left same, same]
    · simp only [ite_eq_right same, zero_smul, add_zero]

private theorem weightedWord_creation_relation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (exponent : ℤ) (vector : ActualTensor D hu) :
    weightedWord D hu (fun colour => (charge colour : ℂ)) charge exponent
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (weightedWord D hu (fun colour => (charge colour : ℂ)) charge exponent vector) -
      (bilinear D (unitCharge D index.1) charge : ℂ) •
        weightedWord D hu (fun colour => (charge colour : ℂ)) charge
          (exponent + 2 * index.2 + 1) vector +
      (frequency index.2 * (bilinear D (unitCharge D index.1) charge : ℂ)) •
        chargedCoefficient D hu charge (exponent + 2 * index.2 + 3) vector := by
  let creator := tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
  let base := fun mode => modeSummand D hu (fun colour => (charge colour : ℂ))
    charge exponent mode vector
  let shifted := fun mode => modeSummand D hu (fun colour => (charge colour : ℂ))
    charge (exponent + 2 * index.2 + 1) mode vector
  let deltaTerm := fun mode : ℤ => if mode = (index.2 : ℤ) then
    (frequency mode * (bilinear D (unitCharge D index.1) charge : ℂ)) •
      chargedCoefficient D hu charge (exponent + 2 * index.2 + 3) vector else 0
  have baseFinite := modeSummand_finite D hu (fun colour => (charge colour : ℂ))
    charge exponent vector
  have shiftedFinite := modeSummand_finite D hu (fun colour => (charge colour : ℂ))
    charge (exponent + 2 * index.2 + 1) vector
  change Function.HasFiniteSupport base at baseFinite
  change Function.HasFiniteSupport shifted at shiftedFinite
  have deltaFinite : Function.HasFiniteSupport deltaTerm := by
    apply (Set.finite_singleton (index.2 : ℤ)).subset
    intro mode member
    by_contra distinct
    have different : mode ≠ (index.2 : ℤ) := by simpa using distinct
    exact member (by simp [deltaTerm, different])
  simp only [weightedWord_sum]
  change (∑ᶠ mode : ℤ, modeSummand D hu (fun colour => (charge colour : ℂ))
      charge exponent mode (creator vector)) =
    creator (∑ᶠ mode : ℤ, base mode) -
      (bilinear D (unitCharge D index.1) charge : ℂ) • (∑ᶠ mode : ℤ, shifted mode) + _
  have mapped := creator.toAddMonoidHom.map_finsum baseFinite
  change creator (∑ᶠ mode : ℤ, base mode) = ∑ᶠ mode : ℤ, creator (base mode) at mapped
  rw [mapped, smul_finsum' _ shiftedFinite]
  rw [← finsum_sub_distrib (baseFinite.fun_comp creator.map_zero)
    (shiftedFinite.fun_comp (smul_zero (bilinear D (unitCharge D index.1) charge : ℂ)))]
  have single : (∑ᶠ mode : ℤ, deltaTerm mode) =
      (frequency index.2 * (bilinear D (unitCharge D index.1) charge : ℂ)) •
        chargedCoefficient D hu charge (exponent + 2 * index.2 + 3) vector := by
    rw [finsum_eq_single _ (index.2 : ℤ)]
    · simp [deltaTerm]
    · intro mode distinct
      simp [deltaTerm, distinct]
  have differenceFinite : Function.HasFiniteSupport (fun mode => creator (base mode) -
      (bilinear D (unitCharge D index.1) charge : ℂ) • shifted mode) :=
    (baseFinite.fun_comp creator.map_zero).sub
      (shiftedFinite.fun_comp (smul_zero (bilinear D (unitCharge D index.1) charge : ℂ)))
  rw [← single, ← finsum_add_distrib differenceFinite deltaFinite]
  apply finsum_congr
  intro mode
  exact modeSummand_creation_relation D hu charge index exponent mode vector

set_option maxHeartbeats 2000000 in
private theorem weightedWord_polynomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (ground : ActualGround D hu) :
    ∀ exponent : ℤ,
      weightedWord D hu (fun colour => (charge colour : ℂ)) charge exponent
          (polynomial ⊗ₜ[ℂ] ground) =
        (((exponent + chargeNorm D charge + 2 : ℤ) : ℂ) / 2) •
          chargedCoefficient D hu charge (exponent + 2) (polynomial ⊗ₜ[ℂ] ground) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    intro exponent
    have constant : (C scalar : Oscillator D) ⊗ₜ[ℂ] ground =
        scalar • ((1 : Oscillator D) ⊗ₜ[ℂ] ground) := by
      rw [TensorProduct.smul_tmul', MvPolynomial.smul_eq_C_mul, mul_one]
    rw [constant, map_smul, map_smul, weightedWord_ground, smul_comm]
  | add first second firstProof secondProof =>
    intro exponent
    simp only [TensorProduct.add_tmul, map_add, firstProof, secondProof, smul_add]
  | mul_X polynomial index previous =>
    intro exponent
    have created : (polynomial * X index) ⊗ₜ[ℂ] ground =
        tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
          (polynomial ⊗ₜ[ℂ] ground) := by
      simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
        current_negative, LinearMap.mulLeft_apply]
      rw [mul_comm]
    rw [created, weightedWord_creation_relation, previous exponent,
      previous (exponent + 2 * index.2 + 1), charged_creation_relation, map_smul]
    rw [show exponent + 2 + 2 * index.2 + 1 = exponent + 2 * index.2 + 3 by omega]
    rw [show exponent + 2 * index.2 + 1 + 2 = exponent + 2 * index.2 + 3 by omega]
    simp only [frequency, smul_sub, smul_smul]
    push_cast
    module

private theorem weightedWord_all_tensor (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (vector : ActualTensor D hu) :
    weightedWord D hu (fun colour => (charge colour : ℂ)) charge exponent vector =
      (((exponent + chargeNorm D charge + 2 : ℤ) : ℂ) / 2) •
        chargedCoefficient D hu charge (exponent + 2) vector := by
  induction vector using TensorProduct.inductionOn with
  | tmul polynomial ground => exact weightedWord_polynomial D hu charge polynomial ground exponent
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof, smul_add]

/- proof_shape: charged_seed_physical_coefficient: content
   admission_basis: escape-witness
   escape_witness: The charge-weighted cut-zero coefficient is propagated from
   the ground exponential through arbitrary oscillator creation, using both
   shifted induction hypotheses and the Heisenberg correction. No seed or
   translation law is assumed. Scalar and support adapters are consumed only.
   Literature status: classical twisted-lattice construction; no novelty. -/
theorem charged_seed_physical_coefficient
    (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (e : ℤ) (v : ActualTensor D hu) :
    (∑ colour : Fin D.rank, (charge colour : ℂ) •
      (wordField D hu (chargedField D hu charge) [(colour, 0)]).coeff e v) -
        ((chargeNorm D charge : ℂ) / 2) •
          chargedCoefficient D hu charge (e + 2) v =
      (((e + 2 : ℤ) : ℂ) / 2) •
        chargedCoefficient D hu charge (e + 2) v := by
  have invariant := weightedWord_all_tensor D hu charge e v
  simp only [weightedWord, LinearMap.sum_apply, LinearMap.smul_apply] at invariant
  rw [invariant]
  push_cast
  module

end

end D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical
