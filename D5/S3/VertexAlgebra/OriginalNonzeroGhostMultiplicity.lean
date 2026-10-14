/- GID: D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual transverse fixed-level range has a finite native basis with two ghost partners and their genuine J degrees.
-/

import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis17
import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction15
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.SMul

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport LatticePositiveEnergy
open scoped BigOperators TensorProduct

noncomputable section

def transverseLevelIndex (D : LatticeData) (xAxis yAxis : Fin D.rank) (level : ℤ) : Type :=
  {index : NativeIndex D //
    (∀ frequency : ℕ, index.1 (xAxis, frequency) = 0) ∧
    (∀ frequency : ℕ, index.1 (yAxis, frequency) = 0) ∧
    index.2 ⊆ {3} ∧
    nativeLevel D index.1 index.2 = level}

def transverseLevelWord (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D)
    (xAxis yAxis : Fin D.rank) (level : ℤ)
    (index : transverseLevelIndex D xAxis yAxis level) : State D :=
  nativeWord D frame beta index.1

def nativeTransverseEnergySpace (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ) : Submodule ℂ (State D) :=
  LinearMap.range (chargeEmbedding D beta) ⊓
    LinearMap.range (P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis) ⊓
      LinearMap.ker
        ((M D H 0 + G D 0) -
          (chosenH D beta + (level : ℂ) - 1) • (LinearMap.id : Module.End ℂ (State D)))

theorem transverseLevelIndex_finite (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (level : ℤ) (nonnegative : 0 ≤ level) :
    Finite (transverseLevelIndex D xAxis yAxis level) := by
  classical
  let powersBound := {powers : Index D →₀ ℕ // oscillatorEnergy powers ≤ level.toNat}
  let ghostBound := {subset : Finset ℕ // subset ⊆ ({3} : Finset ℕ)}
  letI : Finite powersBound := oscillatorLeFinite D level.toNat
  have ghostSetFinite :
      ({subset : Finset ℕ | subset ⊆ ({3} : Finset ℕ)} : Set (Finset ℕ)).Finite := by
    rw [show ({subset : Finset ℕ | subset ⊆ ({3} : Finset ℕ)} : Set (Finset ℕ)) =
      ({∅, {3}} : Set (Finset ℕ)) by
        ext subset
        simp [Finset.subset_singleton_iff]]
    exact Set.toFinite _
  letI : Finite ghostBound := by
    change Finite {subset : Finset ℕ // subset ⊆ ({3} : Finset ℕ)}
    exact ghostSetFinite.to_subtype
  let embedding : transverseLevelIndex D xAxis yAxis level → powersBound × ghostBound :=
    fun index =>
      (⟨index.1.1, by
        have levelWeight :
            (Finsupp.weight (frequencyWeight D) index.1.1 : ℤ) ≤ level := by
          have levelEquality := index.2.2.2.2
          dsimp [nativeLevel] at levelEquality
          have polarizedNonnegative :=
            native_polarizedLevel_nonnegative (subset := index.1.2)
          omega
        have levelWeightNat : oscillatorEnergy index.1.1 ≤ level.toNat := by
          change Finsupp.weight (frequencyWeight D) index.1.1 ≤ level.toNat
          apply Int.ofNat_le.mp
          simpa [Int.toNat_of_nonneg nonnegative] using levelWeight
        exact levelWeightNat⟩,
        ⟨index.1.2, index.2.2.2.1⟩)
  refine Finite.of_injective embedding ?_
  intro first second equality
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun value : powersBound => value.1) (congrArg Prod.fst equality)
  · exact congrArg (fun value : ghostBound => value.1) (congrArg Prod.snd equality)

theorem transverseLevelIndex_empty_of_negative (D : LatticeData)
    (xAxis yAxis : Fin D.rank) (level : ℤ) (negative : level < 0) :
    IsEmpty (transverseLevelIndex D xAxis yAxis level) := by
  constructor
  intro index
  have nonnegativeLevel := nativeLevel_nonnegative D xAxis yAxis index.1.1 index.1.2
  have levelEquality := index.2.2.2.2
  omega

theorem transverseLevelWord_charge (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (index : transverseLevelIndex D xAxis yAxis level) :
    transverseLevelWord D frame beta xAxis yAxis level index ∈
      LinearMap.range (chargeEmbedding D beta) := by
  exact (chargeEmbedding_range_iff D beta _).mpr
    (nativeWord_sector D frame beta index.1)

theorem transverseLevelWord_projected (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (index : transverseLevelIndex D xAxis yAxis level) :
    transverseLevelWord D frame beta xAxis yAxis level index ∈
      LinearMap.range (P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis) := by
  rw [native_P_range_transverse_epsilon D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis]
  apply Submodule.subset_span
  refine ⟨beta, index.1.1, index.1.2, index.2.1, index.2.2.1, index.2.2.2.1, ?_⟩
  rfl

theorem transverseLevelWord_energy (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (index : transverseLevelIndex D xAxis yAxis level) :
    ((M D H 0 + G D 0) -
        (chosenH D beta + (level : ℂ) - 1) • (LinearMap.id : Module.End ℂ (State D)))
      (transverseLevelWord D frame beta xAxis yAxis level index) = 0 := by
  simp only [transverseLevelWord, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, nativeWord_T0 D H frame leftGramInverse rightGramInverse beta,
    index.2.2.2.2, smul_smul]
  module

theorem transverseLevelWord_mem_space (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (index : transverseLevelIndex D xAxis yAxis level) :
    transverseLevelWord D frame beta xAxis yAxis level index ∈
      nativeTransverseEnergySpace D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta xAxis yAxis level := by
  refine ⟨⟨transverseLevelWord_charge D frame inverse leftFrameInverse rightFrameInverse beta
      xAxis yAxis level index, transverseLevelWord_projected D frame inverse leftFrameInverse
      rightFrameInverse beta xAxis yAxis level index⟩, ?_⟩
  exact transverseLevelWord_energy D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis level index

theorem transverseLevelWord_linearIndependent (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ) :
    LinearIndependent ℂ (transverseLevelWord D frame beta xAxis yAxis level) := by
  exact (nativeWord_linearIndependent D frame inverse leftFrameInverse rightFrameInverse beta).comp
    (fun index : transverseLevelIndex D xAxis yAxis level => index.1)
    (fun first second equality => Subtype.ext equality)

theorem transverseEpsilon_coeff_zero (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (state : State D)
    (member : state ∈ transverseEpsilonSpace D frame xAxis yAxis)
    (index : NativeIndex D)
    (notGood : ¬((∀ frequency : ℕ, index.1 (xAxis, frequency) = 0) ∧
      (∀ frequency : ℕ, index.1 (yAxis, frequency) = 0) ∧ index.2 ⊆ {3})) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta state index = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ member
  · rintro generator ⟨charge, powers, subset, xZero, yZero, onlyEpsilon, generatorEq⟩
    have different : index ≠ (powers, subset) := by
      intro equality
      apply notGood
      subst equality
      exact ⟨xZero, yZero, onlyEpsilon⟩
    by_cases chargeEq : charge = beta
    · subst charge
      rw [generatorEq]
      have nativeStateEq : nativeState D frame beta powers 1 subset =
          nativeWord D frame beta (powers, subset) := by
        simp [nativeState, nativeWord]
      rw [nativeStateEq, nativeCoefficients_word]
      simp [different]
    · rw [generatorEq]
      simp [nativeCoefficients, chargeExtraction, nativeState, chargeEq]
  · simp
  · intro first second _ _ firstZero secondZero
    simp [map_add, firstZero, secondZero]
  · intro scalar vector _ vectorZero
    simp [map_smul, vectorZero]

theorem nativeTransverseEnergySpace_span (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ) :
    Submodule.span ℂ (Set.range (transverseLevelWord D frame beta xAxis yAxis level)) =
      nativeTransverseEnergySpace D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta xAxis yAxis level := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    exact transverseLevelWord_mem_space D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level index
  · rintro state ⟨⟨chargeMember, projectedMember⟩, energyMember⟩
    have sectorEquality := (chargeEmbedding_range_iff D beta state).mp chargeMember
    have expansion := native_sector_finite_expansion D frame inverse leftFrameInverse
      rightFrameInverse beta state sectorEquality
    rw [← expansion]
    apply Submodule.sum_mem
    intro index indexMember
    have coefficientNonzero :
        nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta state index ≠ 0 :=
      Finsupp.mem_support_iff.mp indexMember
    have levelIndex := nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse
      beta H leftGramInverse rightGramInverse level state sectorEquality (by
        have kernelEquality := LinearMap.mem_ker.mp energyMember
        change ((M D H 0 + G D 0) -
          (chosenH D beta + (level : ℂ) - 1) •
            (LinearMap.id : Module.End ℂ (State D))) state = 0 at kernelEquality
        have equality := sub_eq_zero.mp kernelEquality
        simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] using equality)
      index
      coefficientNonzero
    have epsilonMember : state ∈ transverseEpsilonSpace D frame xAxis yAxis := by
      rw [← native_P_range_transverse_epsilon D frame inverse leftFrameInverse
        rightFrameInverse xAxis yAxis]
      exact projectedMember
    have good : (∀ frequency : ℕ, index.1 (xAxis, frequency) = 0) ∧
        (∀ frequency : ℕ, index.1 (yAxis, frequency) = 0) ∧ index.2 ⊆ {3} := by
      by_contra notGood
      exact coefficientNonzero
        (transverseEpsilon_coeff_zero D frame inverse leftFrameInverse rightFrameInverse beta
          xAxis yAxis state epsilonMember index notGood)
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨⟨index, good.1, good.2.1, good.2.2, levelIndex⟩, rfl⟩

def nativeTransverseEnergyBasis (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ) :
    Module.Basis (transverseLevelIndex D xAxis yAxis level) ℂ
      (nativeTransverseEnergySpace D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta xAxis yAxis level) :=
    (Module.Basis.span (transverseLevelWord_linearIndependent D frame inverse leftFrameInverse
    rightFrameInverse beta xAxis yAxis level)).map
    (LinearEquiv.ofEq
      (Submodule.span ℂ (Set.range (transverseLevelWord D frame beta xAxis yAxis level)))
      (nativeTransverseEnergySpace D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta xAxis yAxis level)
      (nativeTransverseEnergySpace_span D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta xAxis yAxis level))

theorem nativeTransverseEnergyBasis_apply (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (index : transverseLevelIndex D xAxis yAxis level) :
    (nativeTransverseEnergyBasis D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level index : State D) =
      transverseLevelWord D frame beta xAxis yAxis level index := by
  simp only [nativeTransverseEnergyBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.span_apply]

theorem nativeTransverseEnergy_finrank (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (nonnegative : 0 ≤ level) :
    Module.finrank ℂ (nativeTransverseEnergySpace D H frame inverse leftGramInverse
      rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level) =
      Nat.card (transverseLevelIndex D xAxis yAxis level) := by
  letI : Finite (transverseLevelIndex D xAxis yAxis level) :=
    transverseLevelIndex_finite D xAxis yAxis level nonnegative
  letI : Fintype (transverseLevelIndex D xAxis yAxis level) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis
    (nativeTransverseEnergyBasis D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level)

theorem nativeTransverseEnergy_negative_level (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (negative : level < 0) :
    nativeTransverseEnergySpace D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level = ⊥ := by
  have empty := transverseLevelIndex_empty_of_negative D xAxis yAxis level negative
  letI : IsEmpty (transverseLevelIndex D xAxis yAxis level) := empty
  rw [← nativeTransverseEnergySpace_span D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis level]
  exact Submodule.span_eq_bot.mpr (by
    rintro _ ⟨index, rfl⟩
    exact False.elim (IsEmpty.false index))

theorem nativeWord_J (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D)
    (index : NativeIndex D) :
    LatticeBcGhostBrstGhostNumber.J D (nativeWord D frame beta index) =
      ((1 + epsilonCount index.2 + (thetaCount index.2 : ℤ) -
        (etaCount index.2 : ℤ) : ℤ) : ℂ) • nativeWord D frame beta index := by
  simp only [nativeWord, LatticeBcGhostBrstGhostNumber.J, TensorProduct.map_tmul,
    LinearMap.id_apply, polarized_J, TensorProduct.tmul_smul]

theorem transverseLevelWord_J_degree (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D)
    (xAxis yAxis : Fin D.rank) (level : ℤ)
    (index : transverseLevelIndex D xAxis yAxis level) :
    LatticeBcGhostBrstGhostNumber.J D
        (transverseLevelWord D frame beta xAxis yAxis level index) =
      (if index.1.2 = ∅ then (1 : ℂ) else 2) •
        transverseLevelWord D frame beta xAxis yAxis level index := by
  have subsetCases := (Finset.subset_singleton_iff.mp index.2.2.2.1)
  rcases subsetCases with empty | singleton
  · simp [transverseLevelWord, nativeWord_J, epsilonCount, thetaCount, etaCount, empty]
  · norm_num [transverseLevelWord, nativeWord_J, epsilonCount, thetaCount, etaCount,
      singleton, Finset.filter_insert, Finset.filter_singleton]

theorem nativeTransverseEnergyBasis_J_degree (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (index : transverseLevelIndex D xAxis yAxis level) :
    LatticeBcGhostBrstGhostNumber.J D
        (nativeTransverseEnergyBasis D H frame inverse leftGramInverse rightGramInverse
          leftFrameInverse rightFrameInverse beta xAxis yAxis level index : State D) =
      (if index.1.2 = ∅ then (1 : ℂ) else 2) •
        (nativeTransverseEnergyBasis D H frame inverse leftGramInverse rightGramInverse
          leftFrameInverse rightFrameInverse beta xAxis yAxis level index : State D) := by
  rw [nativeTransverseEnergyBasis_apply, transverseLevelWord_J_degree]

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
