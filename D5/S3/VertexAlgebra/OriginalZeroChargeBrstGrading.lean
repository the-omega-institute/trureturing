/- GID: D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalZeroChargeBrstGrading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native integer ghost number and complete exceptional graded quotient dimensions. -/

import D5.S3.VertexAlgebra.OriginalZeroChargeBrstCohomology
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalZeroChargeBrstGrading

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalZeroChargeEnergyBasis OriginalZeroChargeBrstComplex OriginalZeroChargeBrstCohomology
open scoped BigOperators

noncomputable section

private def diagonal {index : Type*} (degree : index → ℤ) :
    Module.End ℂ (index →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun label => (degree label : ℂ) • Finsupp.single label 1)

private theorem diagonal_apply {index : Type*} (degree : index → ℤ)
    (coefficients : index →₀ ℂ) (label : index) :
    diagonal degree coefficients label = (degree label : ℂ) * coefficients label := by
  classical
  refine coefficients.induction_linear ?_ ?_ ?_
  · simp
  · intro first second firstEquation secondEquation
    simp [map_add, firstEquation, secondEquation, mul_add]
  · intro site value
    by_cases equal : site = label
    · subst site
      simp [diagonal, mul_comm]
    · simp [diagonal, Ne.symm equal]

def sectorNumber (D : LatticeData) : Module.End ℂ (sector D) :=
  (sectorBasis D).constr ℂ (fun index => (indexDegree D index : ℂ) • sectorBasis D index)

private theorem sectorNumber_coordinates (D : LatticeData) (state : sector D) :
    (sectorBasis D).repr (sectorNumber D state) =
      diagonal (indexDegree D) ((sectorBasis D).repr state) := by
  have operators : (sectorBasis D).repr.toLinearMap.comp (sectorNumber D) =
      (diagonal (indexDegree D)).comp (sectorBasis D).repr.toLinearMap := by
    apply (sectorBasis D).ext
    intro index
    simp [sectorNumber, diagonal]
  exact congrArg (fun operator : sector D →ₗ[ℂ] (BasisIndex D →₀ ℂ) => operator state) operators

theorem sectorNumber_native (D : LatticeData) (state : sector D) :
    (sectorNumber D state : State D) =
      LatticeBcGhostBrstGhostNumber.J D (state : State D) := by
  have operators : (sector D).subtype.comp (sectorNumber D) =
      (LatticeBcGhostBrstGhostNumber.J D).comp (sector D).subtype := by
    apply (sectorBasis D).ext
    intro index
    simp [sectorNumber, J_sectorBasis]
  exact congrArg (fun operator : sector D →ₗ[ℂ] State D => operator state) operators

private theorem sectorNumber_cycle (D : LatticeData) (state : cycles D) :
    sectorNumber D (state : sector D) ∈ cycles D := by
  rw [cycles_iff, sectorNumber_coordinates, diagonal_apply]
  simp [(cycles_iff D _).mp state.2]

def cycleNumber (D : LatticeData) : Module.End ℂ (cycles D) :=
  ((sectorNumber D).comp (cycles D).subtype).codRestrict (cycles D)
    (sectorNumber_cycle D)

private theorem quotientCoordinates_number (D : LatticeData) (state : cycles D) :
    quotientCoordinates D (cycleNumber D state) =
      diagonal (fun index : survivingLabels D => indexDegree D index.1)
        (quotientCoordinates D state) := by
  ext index
  change (sectorBasis D).repr (sectorNumber D (state : sector D)) index.1 = _
  rw [sectorNumber_coordinates, diagonal_apply, diagonal_apply]
  rfl

def cohomologyNumber (D : LatticeData) : Module.End ℂ (Cohomology D) :=
  (cohomologyCoordinates D).symm.toLinearMap.comp
    ((diagonal (fun index : survivingLabels D => indexDegree D index.1)).comp
      (cohomologyCoordinates D).toLinearMap)

private theorem coordinates_class (D : LatticeData) (state : cycles D) :
    cohomologyCoordinates D (Submodule.Quotient.mk state) = quotientCoordinates D state := by
  simp [cohomologyCoordinates, Submodule.quotEquivOfEq_mk]

theorem cohomologyNumber_native (D : LatticeData) (state : cycles D) :
    cohomologyNumber D (Submodule.Quotient.mk state) =
      Submodule.Quotient.mk (cycleNumber D state) := by
  apply (cohomologyCoordinates D).injective
  simp only [cohomologyNumber, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, coordinates_class, quotientCoordinates_number]

def degreeLabels (D : LatticeData) (degree : ℤ) : Set (survivingLabels D) :=
  {index | indexDegree D index.1 = degree}

abbrev gradedCohomology (D : LatticeData) (degree : ℤ) : Submodule ℂ (Cohomology D) :=
  (Finsupp.supported ℂ ℂ (degreeLabels D degree)).comap
    (cohomologyCoordinates D).toLinearMap

theorem mem_graded_iff_number (D : LatticeData) (degree : ℤ) (state : Cohomology D) :
    state ∈ gradedCohomology D degree ↔ cohomologyNumber D state = (degree : ℂ) • state := by
  change cohomologyCoordinates D state ∈ Finsupp.supported ℂ ℂ (degreeLabels D degree) ↔ _
  rw [Finsupp.mem_supported']
  constructor
  · intro support
    apply (cohomologyCoordinates D).injective
    ext index
    simp only [cohomologyNumber, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, diagonal_apply]
    by_cases same : indexDegree D index.1 = degree
    · rw [same]
    · simp [support index same]
  · intro equation index outside
    have coefficient := congrArg (fun value : survivingLabels D →₀ ℂ => value index)
      (congrArg (cohomologyCoordinates D) equation)
    simp only [cohomologyNumber, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
      diagonal_apply] at coefficient
    have unequal : (indexDegree D index.1 : ℂ) ≠ (degree : ℂ) := by
      exact_mod_cast outside
    exact (mul_eq_zero.mp (by
      rw [sub_mul, coefficient, sub_self] :
        ((indexDegree D index.1 : ℂ) - (degree : ℂ)) *
          cohomologyCoordinates D state index = 0)).resolve_left (sub_ne_zero.mpr unequal)

def gradedCoordinates (D : LatticeData) (degree : ℤ) :
    gradedCohomology D degree ≃ₗ[ℂ] (degreeLabels D degree →₀ ℂ) :=
  (LinearEquiv.ofSubmodule' (cohomologyCoordinates D)
    (Finsupp.supported ℂ ℂ (degreeLabels D degree))).trans (Finsupp.supportedEquivFinsupp _)

def gradedBasis (D : LatticeData) (degree : ℤ) :
    Module.Basis (degreeLabels D degree) ℂ (gradedCohomology D degree) :=
  Module.Basis.ofRepr (gradedCoordinates D degree)

abbrev SurvivorIndex (D : LatticeData) := Bool ⊕ (Fin D.rank × Bool)

private def survivorIndex (D : LatticeData) : SurvivorIndex D → survivingLabels D
  | .inl false => ⟨.inl .empty, by simp, by simp⟩
  | .inl true => ⟨.inl .triple, by simp, by simp⟩
  | .inr (axis, includeZero) => ⟨.inr (axis, includeZero), by simp, by simp⟩

private def survivorInverse (D : LatticeData) (index : survivingLabels D) : SurvivorIndex D := by
  rcases index with ⟨ghost | value, allowed⟩
  · cases ghost
    · exact .inl false
    · exact False.elim (allowed.1 rfl)
    · exact False.elim (allowed.2 rfl)
    · exact .inl true
  · exact .inr value

def survivorEquiv (D : LatticeData) : SurvivorIndex D ≃ survivingLabels D where
  toFun := survivorIndex D
  invFun := survivorInverse D
  left_inv index := by
    rcases index with includeTriple | ⟨axis, includeZero⟩
    · cases includeTriple <;> rfl
    · rfl
  right_inv index := by
    apply Subtype.ext
    rcases index with ⟨ghost | ⟨axis, includeZero⟩, allowed⟩
    · cases ghost <;> simp [survivorInverse, survivorIndex, survivingLabels] at allowed ⊢
    · rfl

private def survivorDegree (D : LatticeData) : SurvivorIndex D → ℤ
  | .inl includeTriple => if includeTriple then 3 else 0
  | .inr (_, includeZero) => if includeZero then 2 else 1

private theorem survivorEquiv_degree (D : LatticeData) (index : SurvivorIndex D) :
    indexDegree D (survivorEquiv D index).1 = survivorDegree D index := by
  rcases index with includeTriple | ⟨axis, includeZero⟩
  · cases includeTriple <;> rfl
  · rfl

instance (D : LatticeData) : Fintype (survivingLabels D) := Fintype.ofFinite _

instance (D : LatticeData) (degree : ℤ) : Fintype (degreeLabels D degree) := Fintype.ofFinite _

instance (D : LatticeData) (degree : ℤ) : FiniteDimensional ℂ (gradedCohomology D degree) :=
  Module.Finite.of_basis (gradedBasis D degree)

theorem graded_finrank (D : LatticeData) (degree : ℤ) :
    Module.finrank ℂ (gradedCohomology D degree) =
      if degree = 0 then 1 else if degree = 1 then D.rank else
        if degree = 2 then D.rank else if degree = 3 then 1 else 0 := by
  classical
  rw [Module.finrank_eq_card_basis (gradedBasis D degree)]
  have equivalence : {index : SurvivorIndex D // survivorDegree D index = degree} ≃
      degreeLabels D degree := (survivorEquiv D).subtypeEquiv (fun index => by
        exact (survivorEquiv_degree D index).symm ▸ Iff.rfl)
  rw [← Fintype.card_congr equivalence, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [SurvivorIndex, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool,
    survivorDegree, Bool.false_eq_true, ↓reduceIte]
  by_cases zero : degree = 0
  · subst degree
    simp
  by_cases one : degree = 1
  · subst degree
    simp
  by_cases two : degree = 2
  · subst degree
    simp
  by_cases three : degree = 3
  · subst degree
    simp
  · simp [zero, one, two, three, Ne.symm zero, Ne.symm one, Ne.symm two, Ne.symm three]

private theorem representativeState_number (D : LatticeData)
    (coefficients : survivingLabels D →₀ ℂ) :
    sectorNumber D (representativeState D coefficients) =
      representativeState D
        (diagonal (fun index : survivingLabels D => indexDegree D index.1) coefficients) := by
  have operators : (sectorNumber D).comp (representativeState D) =
      (representativeState D).comp
        (diagonal (fun index : survivingLabels D => indexDegree D index.1)) := by
    apply Finsupp.lhom_ext
    intro index scalar
    simp [representativeState, sectorNumber, diagonal,
      Finsupp.mapDomain_single, smul_smul, mul_comm]
  exact congrArg
    (fun operator : (survivingLabels D →₀ ℂ) →ₗ[ℂ] sector D => operator coefficients) operators

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
theorem homogeneous_representative (D : LatticeData) (degree : ℤ) (state : Cohomology D)
    (homogeneous : state ∈ gradedCohomology D degree) :
    let native := representative D (cohomologyCoordinates D state)
    Submodule.Quotient.mk native = state ∧
      LatticeBcGhostBrstGhostNumber.J D ((native : sector D) : State D) =
        (degree : ℂ) • ((native : sector D) : State D) ∧
      cohomologyNumber D state = Submodule.Quotient.mk (cycleNumber D native) := by
  dsimp only
  have classEquation : Submodule.Quotient.mk
      (representative D (cohomologyCoordinates D state)) = state := by
    apply (cohomologyCoordinates D).injective
    rw [coordinates_class, coordinates_representative]
  have coefficients := congrArg (cohomologyCoordinates D)
    ((mem_graded_iff_number D degree state).mp homogeneous)
  simp only [cohomologyNumber, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, map_smul] at coefficients
  have sectorEquation : sectorNumber D (representativeState D (cohomologyCoordinates D state)) =
      (degree : ℂ) • representativeState D (cohomologyCoordinates D state) := by
    rw [representativeState_number, coefficients, map_smul]
  refine ⟨classEquation, ?_, ?_⟩
  · change LatticeBcGhostBrstGhostNumber.J D
        (representativeState D (cohomologyCoordinates D state) : State D) =
      (degree : ℂ) • (representativeState D (cohomologyCoordinates D state) : State D)
    simpa only [sectorNumber_native, Submodule.coe_smul]
      using congrArg (fun value : sector D => (value : State D)) sectorEquation
  · calc
      cohomologyNumber D state = cohomologyNumber D
          (Submodule.Quotient.mk (representative D (cohomologyCoordinates D state))) :=
        congrArg (cohomologyNumber D) classEquation.symm
      _ = _ := cohomologyNumber_native D (representative D (cohomologyCoordinates D state))

private theorem original_Q_homogeneous (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (state : State D) (degree : ℤ)
    (homogeneous : LatticeBcGhostBrstGhostNumber.J D state = (degree : ℂ) • state) :
    LatticeBcGhostBrstGhostNumber.J D (Q D H state) =
      ((degree + 1 : ℤ) : ℂ) • Q D H state := by
  have equation := congrArg (fun operator : Module.End ℂ (State D) => operator state)
    (LatticeBcGhostBrstGhostNumber.J_Q_commutator D H)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, homogeneous, map_smul] at equation
  rw [sub_eq_iff_eq_add] at equation
  simpa [Int.cast_add, Int.cast_one, add_smul, add_comm] using equation

theorem original_boundary_homogeneous_preimage (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (degree : ℤ) (state : sector D) (boundary : state ∈ boundaries D)
    (homogeneous : LatticeBcGhostBrstGhostNumber.J D (state : State D) =
      (degree : ℂ) • (state : State D)) :
    ∃ preimage : sector D, Q D H (preimage : State D) = (state : State D) ∧
      LatticeBcGhostBrstGhostNumber.J D (preimage : State D) =
        ((degree - 1 : ℤ) : ℂ) • (preimage : State D) ∧
      Q D H (state : State D) = 0 := by
  rw [boundaries_eq_span] at boundary
  obtain ⟨scalar, equation⟩ := Submodule.mem_span_singleton.mp boundary
  by_cases zeroScalar : scalar = 0
  · have zeroState : state = 0 := by simpa [zeroScalar] using equation.symm
    exact ⟨0, by simp [zeroState], by simp, by simp [zeroState]⟩
  let preimage : sector D := (scalar / 2) • sectorBasis D (.inl .zeroMode)
  have nativePreimage : Q D H (preimage : State D) = (state : State D) := by
    rw [← differential_native D H leftInverse rightInverse]
    have sectorPreimage : differential D preimage = state := by
      rw [← equation]
      simp [preimage, differential_basis, smul_smul]
    exact congrArg Subtype.val sectorPreimage
  have preimageNumber : LatticeBcGhostBrstGhostNumber.J D (preimage : State D) =
      (1 : ℂ) • (preimage : State D) := by
    simp [preimage, J_sectorBasis, indexDegree]
  have imageNumber := original_Q_homogeneous D H (preimage : State D) 1
    (by simpa only [Int.cast_one] using preimageNumber)
  rw [nativePreimage] at imageNumber
  have sectorEquality : (2 : ℂ) • state = (degree : ℂ) • state := by
    apply Subtype.val_injective
    simpa only [Submodule.coe_smul, Int.reduceAdd, Int.cast_ofNat]
      using imageNumber.symm.trans homogeneous
  have coefficient := congrArg
    (fun value : sector D => (sectorBasis D).repr value (.inl .pair)) sectorEquality
  rw [← equation] at coefficient
  simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at coefficient
  have complexDegree : (degree : ℂ) = 2 := (mul_right_cancel₀ zeroScalar coefficient).symm
  have actualDegree : degree = 2 := by exact_mod_cast complexDegree
  refine ⟨preimage, nativePreimage, ?_, ?_⟩
  · simpa [actualDegree] using preimageNumber
  · rw [← nativePreimage]
    exact original_Q_squared_on_sector D H leftInverse rightInverse preimage

#print axioms cohomologyNumber_native
#print axioms mem_graded_iff_number
#print axioms graded_finrank
#print axioms homogeneous_representative
#print axioms original_boundary_homogeneous_preimage

end
end D5.S3.VertexAlgebra.OriginalZeroChargeBrstGrading
