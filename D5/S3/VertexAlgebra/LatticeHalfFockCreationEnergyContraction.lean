/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCreationEnergyContraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCreationEnergyContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite energy contractions of the original retained correction polynomial. -/

import D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectionTranslation LatticeHalfFockCurrentCorrection
open LatticeActualAnnihilation ActualSeriesDerivation MvPolynomial
open scoped BigOperators

noncomputable section

local macro "ordinary_exponential_derivative_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal.exponential_derivative))

local macro "ordinary_logarithm_derivative_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal.logarithm_derivative_coeff))

local macro "corrected_source_multiplication_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation.correctedSource_X_mul))

local macro "native_correction_source_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
    `D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian.native_correction_source))

def correctedCreationEnergy (D : LatticeData) (source charge : Charge D) (energy : ℤ) :
    CorrectionPolynomial D :=
  correctedSource D charge (creationCoeff D source energy)

def energyPairKernel (D : LatticeData) (index : Index D) (frequency : ℕ) :
    CorrectionPolynomial D :=
  C (pairScalar (sourceWeight D index) (frequency + 1)) *
    X none ^ (sourceWeight D index + (frequency + 1))

private theorem correctedSource_lift (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    correctedSource D charge polynomial = correctionLift D charge polynomial := by
  simp only [correctedSource, correctionPolynomial, correctionLift, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]

private theorem correctedSource_partial (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : Oscillator D) :
    pderiv (some index) (correctedSource D charge polynomial) =
      correctedSource D charge (pderiv index polynomial) := by
  simp only [correctedSource_lift, correctionLift_partial]

private theorem creation_partial_series (D : LatticeData) (source : Charge D)
    (index : Index D) :
    seriesDerivation D (pderiv index) (creationSeries D source) =
      PowerSeries.monomial (index.2 + 1)
        (C ((source index.1 : ℂ) / (index.2 + 1 : ℂ))) := by
  classical
  apply PowerSeries.ext
  intro energy
  simp only [series_coeff, creationSeries, PowerSeries.coeff_mk]
  by_cases zero : energy = 0
  · subst energy
    simp [PowerSeries.coeff_monomial, Nat.succ_ne_zero]
  · simp only [dif_neg zero, Derivation.map_smul, map_sum, pderiv_X, Pi.single_apply,
      PowerSeries.coeff_monomial]
    by_cases same : index.2 + 1 = energy
    · have frequency : energy - 1 = index.2 := by omega
      rw [frequency, if_pos same.symm]
      simp [Prod.ext_iff, same.symm, MvPolynomial.smul_eq_C_mul, div_eq_mul_inv, mul_comm]
    · have distinct (coordinate : Fin D.rank) : (coordinate, energy - 1) ≠ index := by
        intro equality
        have frequency := congrArg Prod.snd equality
        omega
      simp [if_neg (Ne.symm same), distinct]

private theorem creation_energy_partial (D : LatticeData) (source : Charge D)
    (index : Index D) (energy : ℤ) :
    pderiv index (creationCoeff D source energy) =
      ((source index.1 : ℂ) / (index.2 + 1 : ℂ)) •
        creationCoeff D source (energy - (index.2 + 1 : ℕ)) := by
  by_cases negative : energy < 0
  · have shifted : energy - (index.2 + 1 : ℕ) < 0 := by omega
    rw [creationCoeff, dif_pos negative, map_zero, creationCoeff, dif_pos shifted, smul_zero]
  · have coefficient := congrArg (PowerSeries.coeff energy.toNat)
      (actual_exponential_derivation D (pderiv index) source)
    rw [creation_partial_series] at coefficient
    simp only [series_coeff, PowerSeries.monomial_eq_C_mul_X_pow,
      ← mul_assoc, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C] at coefficient
    rw [creationCoeff, dif_neg negative, coefficient]
    by_cases enough : (index.2 + 1 : ℕ) ≤ energy
    · have naturalBound : index.2 + 1 ≤ energy.toNat := by omega
      have shifted : ¬ energy - (index.2 + 1 : ℕ) < 0 := by omega
      have indexEquality : (energy - (index.2 + 1 : ℕ)).toNat =
          energy.toNat - (index.2 + 1) := by omega
      rw [if_pos naturalBound, creationCoeff, dif_neg shifted, indexEquality,
        MvPolynomial.smul_eq_C_mul, mul_comm]
    · have naturalBound : ¬ index.2 + 1 ≤ energy.toNat := by omega
      have shifted : energy - (index.2 + 1 : ℕ) < 0 := by omega
      rw [if_neg naturalBound, creationCoeff, dif_pos shifted, smul_zero]

private theorem derivation_vars_sum (D : LatticeData)
    (derivation : Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D))
    (polynomial : CorrectionPolynomial D) :
    derivation polynomial = ∑ coordinate ∈ polynomial.vars,
      derivation (X coordinate) * pderiv coordinate polynomial := by
  classical
  let finiteDerivation : Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D) :=
    ∑ coordinate ∈ polynomial.vars,
    derivation (X coordinate) • pderiv coordinate
  have applyFinite (argument : CorrectionPolynomial D) :
      finiteDerivation argument = ∑ coordinate ∈ polynomial.vars,
        derivation (X coordinate) * pderiv coordinate argument := by
    have identity := congrFun (map_sum
      (Derivation.coeFnAddMonoidHom (R := ℂ) (A := CorrectionPolynomial D)
        (M := CorrectionPolynomial D))
      (fun coordinate => derivation (X coordinate) • pderiv coordinate) polynomial.vars) argument
    simpa only [finiteDerivation, Derivation.coeFnAddMonoidHom_apply,
      Finset.sum_apply, Derivation.smul_apply, smul_eq_mul] using identity
  have equality : derivation polynomial = finiteDerivation polynomial := by
    apply MvPolynomial.derivation_eq_of_forall_mem_vars
    intro coordinate member
    rw [applyFinite]
    simp [pderiv_X, Pi.single_apply, member]
  exact equality.trans (applyFinite polynomial)

private theorem pair_variable (D : LatticeData) (index other : Index D) :
    pairDerivation D index (X (some other)) = pairPolynomial D index other := by
  simp [pairDerivation, mkDerivation_X]

private theorem pair_none (D : LatticeData) (index : Index D) :
    pairDerivation D index (X none) = 0 := by
  simp [pairDerivation, mkDerivation_X]

private theorem retained_partial_above_energy (D : LatticeData) (source charge : Charge D)
    (energy : ℕ) (index : Index D) (above : energy ≤ index.2) :
    pderiv (some index) (correctedCreationEnergy D source charge energy) = 0 := by
  rw [correctedCreationEnergy, correctedSource_partial, creation_energy_partial]
  have negative : (energy : ℤ) - (index.2 + 1 : ℕ) < 0 := by omega
  rw [creationCoeff, dif_pos negative, smul_zero, map_zero]

private theorem pair_derivative_finite (D : LatticeData) (source charge : Charge D)
    (energy : ℕ) (index : Index D) :
    pairDerivation D index (correctedCreationEnergy D source charge energy) =
      ∑ frequency ∈ Finset.range energy, ∑ coordinate : Fin D.rank,
        pairPolynomial D index (coordinate, frequency) *
          pderiv (some (coordinate, frequency)) (correctedCreationEnergy D source charge energy) := by
  classical
  let polynomial := correctedCreationEnergy D source charge energy
  let active := (Finset.univ.product (Finset.range energy)).image
    (fun other : Index D => some other)
  let contribution := fun other : Option (Index D) =>
    pairDerivation D index (X other) * pderiv other polynomial
  have outsideVars (other : Option (Index D)) (outside : other ∉ polynomial.vars) :
      contribution other = 0 := by
    simp [contribution, pderiv_eq_zero_of_notMem_vars outside]
  have outsideActive (other : Option (Index D)) (outside : other ∉ active) :
      contribution other = 0 := by
    cases other with
    | none => simp [contribution, pair_none]
    | some other =>
      have above : energy ≤ other.2 := by
        by_contra less
        apply outside
        apply Finset.mem_image.mpr
        exact ⟨other, Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩, rfl⟩
      simp [contribution, polynomial, retained_partial_above_energy D source charge energy other above]
  have first := Finset.sum_subset
    (Finset.subset_union_left : polynomial.vars ⊆ polynomial.vars ∪ active)
    (fun other _ outside => outsideVars other outside)
  have second := Finset.sum_subset
    (Finset.subset_union_right : active ⊆ polynomial.vars ∪ active)
    (fun other _ outside => outsideActive other outside)
  rw [derivation_vars_sum]
  change (∑ other ∈ polynomial.vars, contribution other) = _
  rw [first, ← second]
  simp only [active]
  rw [Finset.sum_image (fun first _ second _ equality => Option.some.inj equality)]
  have productIdentity :
      (∑ other ∈ Finset.univ.product (Finset.range energy), contribution (some other)) =
        ∑ coordinate : Fin D.rank, ∑ frequency ∈ Finset.range energy,
          contribution (some (coordinate, frequency)) :=
    Finset.sum_product Finset.univ (Finset.range energy) (fun other => contribution (some other))
  rw [productIdentity, Finset.sum_comm]
  simp only [contribution, pair_variable]
  rfl

private theorem pair_derivative_weighted (D : LatticeData) (source charge : Charge D)
    (energy : ℕ) (index : Index D) :
    pairDerivation D index (correctedCreationEnergy D source charge energy) =
      ∑ frequency ∈ Finset.range energy, energyPairKernel D index frequency *
        correctedSource D charge (annihilate D index.1 frequency (creationCoeff D source energy)) := by
  rw [pair_derivative_finite]
  apply Finset.sum_congr rfl
  intro frequency member
  simp only [correctedCreationEnergy, correctedSource_partial, annihilate,
    LatticeSugawaraCurrents.weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  change pairPolynomial D index (coordinate, frequency) * correctedSource D charge
      (pderiv (coordinate, frequency) (creationCoeff D source energy)) =
    energyPairKernel D index frequency * correctedSource D charge
      ((D.G index.1 coordinate : ℂ) • pderiv (coordinate, frequency) (creationCoeff D source energy))
  rw [map_smul]
  simp only [RingHom.id_apply, pairPolynomial, sourceWeight, energyPairKernel,
    MvPolynomial.smul_eq_C_mul]
  rw [map_mul]
  ring

theorem actual_retained_creation_energy_contraction (D : LatticeData)
    (source charge : Charge D) (energy : ℕ) (index : Index D) :
    pairDerivation D index (correctedCreationEnergy D source charge energy) =
      ∑ frequency ∈ Finset.range energy,
        (((frequency + 1 : ℂ)⁻¹ * (bilinear D (unitCharge D index.1) source : ℂ)) •
          energyPairKernel D index frequency) *
          correctedCreationEnergy D source charge ((energy : ℤ) - (frequency + 1 : ℕ)) := by
  rw [pair_derivative_weighted]
  apply Finset.sum_congr rfl
  intro frequency member
  rw [annihilation_creation, map_smul]
  simp only [correctedCreationEnergy, RingHom.id_apply, smul_mul_assoc, mul_smul_comm]

private theorem ordinary_creation_energy_recurrence (D : LatticeData)
    (source : Charge D) (energy : ℕ) :
    (energy + 1 : ℂ) • creationCoeff D source (energy + 1 : ℕ) =
      ∑ frequency ∈ Finset.range (energy + 1), ∑ coordinate : Fin D.rank,
        (source coordinate : ℂ) •
          (X (coordinate, frequency) * creationCoeff D source ((energy - frequency : ℕ) : ℤ)) := by
  have identity := congrArg (PowerSeries.coeff energy)
    (ordinary_exponential_derivative_supplier D source)
  rw [PowerSeries.coeff_derivative, mul_comm (creationExponential D source),
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at identity
  simp only [ordinary_logarithm_derivative_supplier, Prod.fst, Prod.snd,
    Finset.sum_mul, smul_mul_assoc] at identity
  have scalar : (energy + 1 : Oscillator D) =
      algebraMap ℂ (Oscillator D) (energy + 1 : ℂ) := by simp
  have natural (level : ℕ) : creationCoeff D source level =
      PowerSeries.coeff level (creationExponential D source) := by
    rw [creationCoeff, dif_neg (by omega), Int.toNat_natCast]
  simp only [natural]
  simpa only [Algebra.smul_def, scalar, mul_comm, Nat.succ_eq_add_one] using identity

theorem actual_retained_creation_energy_recurrence (D : LatticeData)
    (source charge : Charge D) (energy : ℕ) :
    (energy + 1 : ℂ) • correctedCreationEnergy D source charge (energy + 1 : ℕ) =
      ∑ frequency ∈ Finset.range (energy + 1), ∑ coordinate : Fin D.rank,
        (source coordinate : ℂ) • insertion D charge (coordinate, frequency)
          (correctedCreationEnergy D source charge ((energy - frequency : ℕ) : ℤ)) := by
  have identity := congrArg (correctedSource D charge)
    (ordinary_creation_energy_recurrence D source energy)
  simpa only [map_sum, map_smul, RingHom.id_apply,
    corrected_source_multiplication_supplier, correctedCreationEnergy] using identity

private theorem retained_expanded_energy_recurrence (D : LatticeData)
    (source charge : Charge D) (energy : ℕ) :
    (energy + 1 : ℂ) • correctedCreationEnergy D source charge (energy + 1 : ℕ) =
      ∑ frequency ∈ Finset.range (energy + 1), ∑ coordinate : Fin D.rank,
        (source coordinate : ℂ) •
          ((X (some (coordinate, frequency)) + singletonPolynomial D charge (coordinate, frequency)) *
              correctedCreationEnergy D source charge ((energy - frequency : ℕ) : ℤ) +
            ∑ pairedFrequency ∈ Finset.range (energy - frequency),
              (((pairedFrequency + 1 : ℂ)⁻¹ *
                  (bilinear D (unitCharge D coordinate) source : ℂ)) •
                  energyPairKernel D (coordinate, frequency) pairedFrequency) *
                correctedCreationEnergy D source charge
                  (((energy - frequency : ℕ) : ℤ) - (pairedFrequency + 1 : ℕ))) := by
  rw [actual_retained_creation_energy_recurrence]
  apply Finset.sum_congr rfl
  intro frequency member
  apply Finset.sum_congr rfl
  intro coordinate _
  apply congrArg (fun polynomial : CorrectionPolynomial D => (source coordinate : ℂ) • polynomial)
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  rw [actual_retained_creation_energy_contraction]

theorem actual_native_creation_energy_recurrence (D : LatticeData) (hu : IsUnit D.G.det)
    (source charge : Charge D) (energy : ℕ) :
    (energy + 1 : ℂ) • LatticeHalfFockAllStateField.Ytw D hu
        (Finsupp.single charge (creationCoeff D source (energy + 1 : ℕ))) =
      ∑ frequency ∈ Finset.range (energy + 1), ∑ coordinate : Fin D.rank,
        (source coordinate : ℂ) •
          (LatticeHalfFockScalarLabelledGaussian.nativeCorrectionEvaluation D hu charge
            ((X (some (coordinate, frequency)) + singletonPolynomial D charge (coordinate, frequency)) *
              correctedCreationEnergy D source charge ((energy - frequency : ℕ) : ℤ)) +
            ∑ pairedFrequency ∈ Finset.range (energy - frequency),
              LatticeHalfFockScalarLabelledGaussian.nativeCorrectionEvaluation D hu charge
                ((((pairedFrequency + 1 : ℂ)⁻¹ *
                    (bilinear D (unitCharge D coordinate) source : ℂ)) •
                    energyPairKernel D (coordinate, frequency) pairedFrequency) *
                  correctedCreationEnergy D source charge
                    (((energy - frequency : ℕ) : ℤ) - (pairedFrequency + 1 : ℕ)))) := by
  have identity := congrArg
    (LatticeHalfFockScalarLabelledGaussian.nativeCorrectionEvaluation D hu charge)
    (retained_expanded_energy_recurrence D source charge energy)
  simpa only [correctedCreationEnergy, map_sum, map_smul, map_add, RingHom.id_apply,
    native_correction_source_supplier] using identity

local macro "corrected_source_initial_supplier" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
  `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation.correctedSource_one))

def scalarEnergyEvaluation (D : LatticeData) : CorrectionPolynomial D →ₐ[ℂ] ℂ :=
  aeval (fun index : Option (Index D) => index.elim 1 (fun _ => 0))

def actualEnergyScalar (D : LatticeData) (source charge : Charge D) (energy : ℕ) : ℂ :=
  scalarEnergyEvaluation D (correctedCreationEnergy D source charge energy)

def chargedEnergyLogCoefficient (D : LatticeData) (first second : Charge D) (energy : ℕ) : ℂ :=
  ((bilinear D first first : ℂ) + (bilinear D first second : ℂ)) * halfBinomial energy /
      (energy : ℂ) +
    (bilinear D first first : ℂ) / (2 * (energy : ℂ)) *
      ∑ frequency ∈ Finset.range (energy - 1),
        halfBinomial (frequency + 1) * halfBinomial (energy - (frequency + 1))

private theorem coordinate_pairing (D : LatticeData) (source charge : Charge D) :
    (∑ coordinate : Fin D.rank,
      (source coordinate : ℂ) * (bilinear D (unitCharge D coordinate) charge : ℂ)) =
        (bilinear D source charge : ℂ) := by
  classical
  have integer : (∑ coordinate : Fin D.rank,
      source coordinate * bilinear D (unitCharge D coordinate) charge) =
        bilinear D source charge := by
    simp [bilinear, unitCharge, Finset.mul_sum, ite_mul, mul_assoc]
  exact_mod_cast integer

private theorem scalar_creation_initial (D : LatticeData) (source charge : Charge D) :
    actualEnergyScalar D source charge 0 = 1 := by
  have logarithm : PowerSeries.constantCoeff (creationSeries D source) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have initial : PowerSeries.coeff 0 (creationExponential D source) = 1 := by
    rw [creationExponential, PowerSeries.coeff_subst'
      (PowerSeries.HasSubst.of_constantCoeff_zero' logarithm), finsum_eq_single _ 0]
    · simp
    · intro degree nonzero
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, logarithm]
      simp [nonzero]
  have ordinary : creationCoeff D source 0 = 1 := by
    simpa [creationCoeff, PowerSeries.coeff_zero_eq_constantCoeff] using initial
  rw [actualEnergyScalar, correctedCreationEnergy, Nat.cast_zero, ordinary]
  change scalarEnergyEvaluation D (correctedSource D charge 1) = 1
  rw [corrected_source_initial_supplier, map_one]

private theorem scalar_energy_raw_recurrence (D : LatticeData)
    (source charge : Charge D) (energy : ℕ) :
    (energy + 1 : ℂ) * actualEnergyScalar D source charge (energy + 1) =
      ∑ frequency ∈ Finset.range (energy + 1),
        (bilinear D source charge : ℂ) * halfBinomial (frequency + 1) *
          actualEnergyScalar D source charge (energy - frequency) +
      ∑ frequency ∈ Finset.range (energy + 1),
        ∑ pairedFrequency ∈ Finset.range (energy - frequency),
          ((bilinear D source source : ℂ) * (pairedFrequency + 1 : ℂ)⁻¹ *
            pairScalar (frequency + 1) (pairedFrequency + 1)) *
              actualEnergyScalar D source charge (energy - frequency - (pairedFrequency + 1)) := by
  classical
  have identity := congrArg (scalarEnergyEvaluation D)
    (retained_expanded_energy_recurrence D source charge energy)
  simp only [map_smul, RingHom.id_apply, map_sum, map_add, map_mul, map_pow,
    scalarEnergyEvaluation, aeval_X, aeval_C, singletonPolynomial, energyPairKernel,
    Option.elim, one_pow, zero_add, mul_one, smul_eq_mul] at identity
  change (energy + 1 : ℂ) * actualEnergyScalar D source charge (energy + 1) =
    ∑ frequency ∈ Finset.range (energy + 1), ∑ coordinate : Fin D.rank,
    (source coordinate : ℂ) *
      (halfBinomial (frequency + 1) * (bilinear D (unitCharge D coordinate) charge : ℂ) *
          actualEnergyScalar D source charge (energy - frequency) +
        ∑ pairedFrequency ∈ Finset.range (energy - frequency),
          ((pairedFrequency + 1 : ℂ)⁻¹ *
              (bilinear D (unitCharge D coordinate) source : ℂ) *
              pairScalar (frequency + 1) (pairedFrequency + 1)) *
            scalarEnergyEvaluation D (correctedCreationEnergy D source charge
              (((energy - frequency : ℕ) : ℤ) - (pairedFrequency + 1 : ℕ)))) at identity
  rw [identity]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro frequency _
    simp_rw [show ∀ coordinate : Fin D.rank,
      (source coordinate : ℂ) *
          (halfBinomial (frequency + 1) * (bilinear D (unitCharge D coordinate) charge : ℂ) *
            actualEnergyScalar D source charge (energy - frequency)) =
        ((source coordinate : ℂ) * (bilinear D (unitCharge D coordinate) charge : ℂ)) *
          (halfBinomial (frequency + 1) *
            actualEnergyScalar D source charge (energy - frequency)) by intro coordinate; ring]
    rw [← Finset.sum_mul, coordinate_pairing]
    ring
  · apply Finset.sum_congr rfl
    intro frequency _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro pairedFrequency member
    have bound := Finset.mem_range.mp member
    have difference : ((energy - frequency : ℕ) : ℤ) - (pairedFrequency + 1 : ℕ) =
        ((energy - frequency - (pairedFrequency + 1) : ℕ) : ℤ) := by omega
    rw [difference]
    change (∑ coordinate : Fin D.rank,
      (source coordinate : ℂ) *
        (((pairedFrequency + 1 : ℂ)⁻¹ * (bilinear D (unitCharge D coordinate) source : ℂ) *
            pairScalar (frequency + 1) (pairedFrequency + 1)) *
          actualEnergyScalar D source charge (energy - frequency - (pairedFrequency + 1)))) = _
    simp_rw [show ∀ coordinate : Fin D.rank,
      (source coordinate : ℂ) *
        (((pairedFrequency + 1 : ℂ)⁻¹ * (bilinear D (unitCharge D coordinate) source : ℂ) *
            pairScalar (frequency + 1) (pairedFrequency + 1)) *
          actualEnergyScalar D source charge (energy - frequency - (pairedFrequency + 1))) =
      ((source coordinate : ℂ) * (bilinear D (unitCharge D coordinate) source : ℂ)) *
        ((pairedFrequency + 1 : ℂ)⁻¹ * pairScalar (frequency + 1) (pairedFrequency + 1) *
          actualEnergyScalar D source charge (energy - frequency - (pairedFrequency + 1))) by
        intro coordinate; ring]
    rw [← Finset.sum_mul, coordinate_pairing]
    ring

private theorem finite_triangle_diagonals (function : ℕ → ℕ → ℂ) (energy : ℕ) :
    (∑ frequency ∈ Finset.range (energy + 1),
      ∑ pairedFrequency ∈ Finset.range (energy - frequency), function frequency pairedFrequency) =
        ∑ total ∈ Finset.range energy, ∑ frequency ∈ Finset.range (total + 1),
          function frequency (total - frequency) := by
  induction energy with
  | zero => simp
  | succ energy induction =>
    rw [Finset.sum_range_succ]
    have last : energy + 1 - (energy + 1) = 0 := by omega
    rw [last, Finset.sum_range_zero, add_zero]
    have expand :
        (∑ frequency ∈ Finset.range (energy + 1),
          ∑ pairedFrequency ∈ Finset.range (energy + 1 - frequency),
            function frequency pairedFrequency) =
          (∑ frequency ∈ Finset.range (energy + 1),
            ∑ pairedFrequency ∈ Finset.range (energy - frequency), function frequency pairedFrequency) +
          ∑ frequency ∈ Finset.range (energy + 1), function frequency (energy - frequency) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro frequency member
      have bound := Finset.mem_range.mp member
      rw [show energy + 1 - frequency = (energy - frequency) + 1 by omega,
        Finset.sum_range_succ]
    rw [expand, induction]
    exact (Finset.sum_range_succ (fun total =>
      ∑ frequency ∈ Finset.range (total + 1), function frequency (total - frequency)) energy).symm

private theorem scalar_ordered_pair_half (energy : ℕ) :
    (∑ frequency ∈ Finset.range (energy + 1),
      (frequency + 1 : ℂ) / (energy + 2 : ℂ) *
        halfBinomial (frequency + 1) * halfBinomial (energy - frequency + 1)) =
      (1 / 2 : ℂ) * ∑ frequency ∈ Finset.range (energy + 1),
        halfBinomial (frequency + 1) * halfBinomial (energy - frequency + 1) := by
  have reflected := Finset.sum_range_reflect
    (fun frequency => (frequency + 1 : ℂ) / (energy + 2 : ℂ) *
      halfBinomial (frequency + 1) * halfBinomial (energy - frequency + 1)) (energy + 1)
  have reflection :
      (∑ frequency ∈ Finset.range (energy + 1),
        (((energy - frequency : ℕ) : ℂ) + 1) / (energy + 2 : ℂ) *
          halfBinomial (frequency + 1) * halfBinomial (energy - frequency + 1)) =
        ∑ frequency ∈ Finset.range (energy + 1),
          (frequency + 1 : ℂ) / (energy + 2 : ℂ) *
            halfBinomial (frequency + 1) * halfBinomial (energy - frequency + 1) := by
    rw [← reflected]
    apply Finset.sum_congr rfl
    intro frequency member
    have bound := Finset.mem_range.mp member
    rw [show energy + 1 - 1 - frequency = energy - frequency by omega,
      show energy - (energy - frequency) = frequency by omega]
    ring
  have denominator : (energy + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : energy + 2 ≠ 0)
  have doubled :
      2 * (∑ frequency ∈ Finset.range (energy + 1),
        (frequency + 1 : ℂ) / (energy + 2 : ℂ) *
          halfBinomial (frequency + 1) * halfBinomial (energy - frequency + 1)) =
        ∑ frequency ∈ Finset.range (energy + 1),
          halfBinomial (frequency + 1) * halfBinomial (energy - frequency + 1) := by
    rw [two_mul]
    conv_lhs =>
      rhs
      rw [← reflection]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro frequency member
    have bound := Finset.mem_range.mp member
    have indexSum : (frequency : ℂ) + (energy - frequency : ℕ) = (energy : ℂ) := by
      exact_mod_cast (by omega : frequency + (energy - frequency) = energy)
    field_simp
    linear_combination
      halfBinomial (frequency + 1) * halfBinomial (energy - frequency + 1) * indexSum
  linear_combination (1 / 2 : ℂ) * doubled

private theorem scalar_pair_energy_collapsed (D : LatticeData)
    (source charge : Charge D) (energy : ℕ) :
    (∑ frequency ∈ Finset.range (energy + 1),
      ∑ pairedFrequency ∈ Finset.range (energy - frequency),
        ((bilinear D source source : ℂ) * (pairedFrequency + 1 : ℂ)⁻¹ *
          pairScalar (frequency + 1) (pairedFrequency + 1)) *
            actualEnergyScalar D source charge (energy - frequency - (pairedFrequency + 1))) =
      ∑ total ∈ Finset.range energy,
        ((bilinear D source source : ℂ) / 2 *
          ∑ frequency ∈ Finset.range (total + 1),
            halfBinomial (frequency + 1) * halfBinomial (total - frequency + 1)) *
          actualEnergyScalar D source charge (energy - total - 1) := by
  rw [finite_triangle_diagonals]
  apply Finset.sum_congr rfl
  intro total member
  have totalBound := Finset.mem_range.mp member
  have normalized :
      (∑ frequency ∈ Finset.range (total + 1),
        ((bilinear D source source : ℂ) * (((total - frequency : ℕ) : ℂ) + 1)⁻¹ *
          pairScalar (frequency + 1) (total - frequency + 1)) *
            actualEnergyScalar D source charge (energy - frequency - (total - frequency + 1))) =
        (bilinear D source source : ℂ) *
          (∑ frequency ∈ Finset.range (total + 1),
            (frequency + 1 : ℂ) / (total + 2 : ℂ) *
              halfBinomial (frequency + 1) * halfBinomial (total - frequency + 1)) *
            actualEnergyScalar D source charge (energy - total - 1) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro frequency frequencyMember
    have bound := Finset.mem_range.mp frequencyMember
    rw [show energy - frequency - (total - frequency + 1) = energy - total - 1 by omega]
    have denominator : (((total - frequency : ℕ) : ℂ) + 1) ≠ 0 := by
      exact_mod_cast (by omega : total - frequency + 1 ≠ 0)
    have indexSum : (frequency : ℂ) + (total - frequency : ℕ) = (total : ℂ) := by
      exact_mod_cast (by omega : frequency + (total - frequency) = total)
    simp only [pairScalar, Nat.cast_add, Nat.cast_one]
    have wholeSum : (frequency + 1 : ℂ) + (((total - frequency : ℕ) : ℂ) + 1) =
        (total + 2 : ℂ) := by linear_combination indexSum
    rw [wholeSum]
    field_simp
  rw [normalized, scalar_ordered_pair_half]
  ring

private theorem weighted_energy_log (D : LatticeData) (first second : Charge D)
    (frequency : ℕ) :
    (frequency + 1 : ℂ) * chargedEnergyLogCoefficient D first second (frequency + 1) =
      ((bilinear D first first : ℂ) + (bilinear D first second : ℂ)) *
          halfBinomial (frequency + 1) +
        (bilinear D first first : ℂ) / 2 * ∑ pairedFrequency ∈ Finset.range frequency,
          halfBinomial (pairedFrequency + 1) * halfBinomial (frequency - pairedFrequency) := by
  have denominator : (frequency + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero frequency)
  have difference (pairedFrequency : ℕ) :
      frequency + 1 - (pairedFrequency + 1) = frequency - pairedFrequency := by omega
  simp only [chargedEnergyLogCoefficient, Nat.add_sub_cancel, difference, Nat.sub_zero,
    Nat.cast_add, Nat.cast_one]
  field_simp

theorem actual_creation_energy_gaussian_recurrence (D : LatticeData)
    (first second : Charge D) (energy : ℕ) :
    (energy : ℂ) * actualEnergyScalar D first (first + second) energy =
      ∑ frequency ∈ Finset.range energy,
        ((frequency + 1 : ℂ) * chargedEnergyLogCoefficient D first second (frequency + 1)) *
          actualEnergyScalar D first (first + second) (energy - (frequency + 1)) := by
  cases energy with
  | zero => simp
  | succ energy =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [scalar_energy_raw_recurrence, scalar_pair_energy_collapsed]
    have pairing : (bilinear D first (first + second) : ℂ) =
        (bilinear D first first : ℂ) + (bilinear D first second : ℂ) := by
      simp only [LatticeActualGeneratorLocality.bilinear_add_right, Int.cast_add]
    simp_rw [weighted_energy_log, add_mul, Finset.sum_add_distrib,
      show ∀ frequency : ℕ, energy + 1 - (frequency + 1) = energy - frequency by
        intro frequency; omega]
    congr 1
    · rw [pairing]
      simp only [add_mul, Finset.sum_add_distrib]
    · rw [Finset.sum_range_succ']
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro total _
      congr 1
      · apply congrArg (fun sum : ℂ => (bilinear D first first : ℂ) / 2 * sum)
        apply Finset.sum_congr rfl
        intro frequency member
        have bound := Finset.mem_range.mp member
        rw [show total + 1 - frequency = total - frequency + 1 by omega]

#print axioms actual_creation_energy_gaussian_recurrence

def chargedEnergyLog (D : LatticeData) (first second : Charge D) : PowerSeries ℂ :=
  PowerSeries.mk (chargedEnergyLogCoefficient D first second)

def chargedEnergyGaussian (D : LatticeData) (first second : Charge D) : PowerSeries ℂ :=
  (PowerSeries.exp ℂ).subst (chargedEnergyLog D first second)

private theorem charged_log_zero (D : LatticeData) (first second : Charge D) :
    PowerSeries.constantCoeff (chargedEnergyLog D first second) = 0 := by
  change chargedEnergyLogCoefficient D first second 0 = 0
  simp [chargedEnergyLogCoefficient]

private theorem charged_log_has_substitution (D : LatticeData) (first second : Charge D) :
    PowerSeries.HasSubst (chargedEnergyLog D first second) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (charged_log_zero D first second)

private theorem charged_gaussian_initial (D : LatticeData) (first second : Charge D) :
    PowerSeries.coeff 0 (chargedEnergyGaussian D first second) = 1 := by
  rw [chargedEnergyGaussian, PowerSeries.coeff_subst'
    (charged_log_has_substitution D first second), finsum_eq_single _ 0]
  · simp
  · intro degree nonzero
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      charged_log_zero, zero_pow nonzero, smul_zero]

private theorem charged_gaussian_recurrence (D : LatticeData) (first second : Charge D)
    (energy : ℕ) :
    (energy + 1 : ℂ) * PowerSeries.coeff (energy + 1) (chargedEnergyGaussian D first second) =
      ∑ frequency ∈ Finset.range (energy + 1),
        ((frequency + 1 : ℂ) * chargedEnergyLogCoefficient D first second (frequency + 1)) *
          PowerSeries.coeff (energy - frequency) (chargedEnergyGaussian D first second) := by
  have derivative : PowerSeries.derivative ℂ (chargedEnergyGaussian D first second) =
      PowerSeries.derivative ℂ (chargedEnergyLog D first second) *
        chargedEnergyGaussian D first second := by
    rw [chargedEnergyGaussian, PowerSeries.derivative_subst
      (charged_log_has_substitution D first second), PowerSeries.derivative_exp, mul_comm]
  have coefficient := congrArg (PowerSeries.coeff energy) derivative
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at coefficient
  simpa only [PowerSeries.coeff_derivative, chargedEnergyLog, PowerSeries.coeff_mk,
    mul_comm (PowerSeries.coeff (energy + 1) (chargedEnergyGaussian D first second)),
    mul_comm (chargedEnergyLogCoefficient D first second _)] using coefficient

theorem actual_creation_energy_gaussian_closed (D : LatticeData)
    (first second : Charge D) (energy : ℕ) :
    actualEnergyScalar D first (first + second) energy =
      PowerSeries.coeff energy (chargedEnergyGaussian D first second) := by
  induction energy using Nat.strong_induction_on with
  | h energy induction =>
    cases energy with
    | zero => rw [scalar_creation_initial, charged_gaussian_initial]
    | succ energy =>
      have nonzero : (energy + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero energy
      apply mul_left_cancel₀ nonzero
      have actual := actual_creation_energy_gaussian_recurrence D first second (energy + 1)
      rw [Nat.cast_add, Nat.cast_one] at actual
      rw [actual, charged_gaussian_recurrence]
      apply Finset.sum_congr rfl
      intro frequency member
      have bound := Finset.mem_range.mp member
      rw [show energy + 1 - (frequency + 1) = energy - frequency by omega,
        induction (energy - frequency) (by omega)]

#print axioms actual_creation_energy_gaussian_closed

#print axioms actual_retained_creation_energy_contraction
#print axioms actual_retained_creation_energy_recurrence
#print axioms actual_native_creation_energy_recurrence

end

end D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
