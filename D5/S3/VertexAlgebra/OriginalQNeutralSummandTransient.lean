import D5.S3.VertexAlgebra.OriginalQLiteralQuotientTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQFiniteHplCheck OriginalBrstReassembly

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
  (critical : D.rank = 26)

theorem chosenH_zero : chosenH D 0 = 0 := by
  simp [chosenH, complexCharge, gramPair]

theorem original_zero_charge_projection :
    chargeProjection D 0 = LatticeBcGhostNeutralCohomology.neutralChargeProjection D := by
  apply (fullBasis D).ext
  intro label
  rw [original_charge_projection_basis]
  change (if label.1.1 = 0 then LatticeBcGhostNeutralCohomology.Support.stateBasis D label else 0) =
    LatticeBcGhostNeutralCohomology.neutralChargeProjection D
      (LatticeBcGhostNeutralCohomology.Support.stateBasis D label)
  exact (LatticeBcGhostNeutralCohomology.neutralChargeProjection_basis D label).symm

theorem original_neutral_sector :
    originalEnergySector D H 0 1 = LatticeBcGhostNeutralCohomology.E0 D H := by
  ext state
  change (chargeProjection D 0 state = state ∧
    (M D H 0 + G D 0) state = (chosenH D 0 + ((1 : ℤ) : ℂ) - 1) • state) ↔ _
  rw [chosenH_zero, original_zero_charge_projection]
  simpa only [Int.cast_one, zero_add, sub_self, zero_smul] using
    (LatticeBcGhostNeutralCohomology.mem_E0_iff D H state).symm

local notation "original" => LatticeBcGhostNeutralCohomology.OriginalCohomology D H
local notation "neutral" => LatticeBcGhostNeutralCohomology.AbsoluteCohomology D H
local notation "inclusion" => LatticeBcGhostNeutralCohomology.absoluteToOriginal D H
local notation "originalP" => originalCohomologyProjection D H leftGramInverse rightGramInverse critical 0 1

theorem original_neutral_inclusion_fixed (quotient : neutral) :
    originalP (inclusion quotient) = inclusion quotient := by
  refine Quotient.inductionOn quotient ?_
  intro cycle
  change originalP ((LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
    (LatticeBcGhostNeutralCohomology.originalCycleInclusion D H cycle)) =
    (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
      (LatticeBcGhostNeutralCohomology.originalCycleInclusion D H cycle)
  rw [original_projection_representative]
  congr 1
  apply Subtype.ext
  exact ambient_energy_projection_fixed D H leftGramInverse rightGramInverse 0 1
    ((original_neutral_sector D H).symm ▸ cycle.property.1)

theorem original_neutral_projection_range : LinearMap.range originalP = LinearMap.range inclusion := by
  ext quotient
  constructor
  · rintro ⟨preimage, rfl⟩
    obtain ⟨cycle, rfl⟩ := (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ_surjective preimage
    let projected : LatticeBcGhostNeutralCohomology.Cycles D H :=
      ⟨ambientEnergyProjection D 0 1 cycle.val,
        (original_neutral_sector D H) ▸
          ambient_energy_projection_mem D H leftGramInverse rightGramInverse 0 1 cycle.val,
        (trueCycleMap (Q D H) (Q D H) (ambientEnergyProjection D 0 1)
          (ambient_energy_projection_Q D H leftGramInverse rightGramInverse 0 1).symm cycle).property⟩
    refine ⟨(LatticeBcGhostNeutralCohomology.Boundaries D H).mkQ projected, ?_⟩
    rfl
  · rintro ⟨preimage, rfl⟩
    exact ⟨inclusion preimage, original_neutral_inclusion_fixed D H leftGramInverse rightGramInverse critical preimage⟩

def neutralOriginalSummandEquiv : neutral ≃ₗ[ℂ] LinearMap.range originalP :=
  (LinearEquiv.ofInjective inclusion (LatticeBcGhostNeutralCohomology.absoluteToOriginal_injective D H)).trans
    (LinearEquiv.ofEq _ _ (original_neutral_projection_range D H leftGramInverse rightGramInverse critical).symm)

theorem neutral_original_equiv_inclusion (quotient : neutral) :
    (neutralOriginalSummandEquiv D H leftGramInverse rightGramInverse critical quotient).val = inclusion quotient := rfl

theorem original_neutral_J (quotient : neutral) :
    originalJ D H leftGramInverse rightGramInverse critical (inclusion quotient) =
    inclusion (LatticeBcGhostNeutralCohomology.absoluteJ D H leftGramInverse rightGramInverse critical quotient) := by
  refine Quotient.inductionOn quotient ?_
  intro cycle
  rfl

def originalNeutralBasis : Module.Basis (LatticeBcGhostNeutralCohomology.AbsoluteIndex D) ℂ
    (LinearMap.range originalP) :=
  (LatticeBcGhostNeutralCohomology.absoluteBasis D H leftGramInverse rightGramInverse critical).map
    (neutralOriginalSummandEquiv D H leftGramInverse rightGramInverse critical)

def nativeOriginalCycle (index : LatticeBcGhostNeutralCohomology.AbsoluteIndex D) :
    LatticeBcGhostNeutralCohomology.OriginalCycles D H :=
  ⟨LatticeBcGhostNeutralCohomology.native D
    (LatticeBcGhostNeutralCohomology.absoluteNativeIndex D index), by
      change Q D H (LatticeBcGhostNeutralCohomology.native D
        (LatticeBcGhostNeutralCohomology.absoluteNativeIndex D index)) = 0
      rw [LatticeBcGhostNeutralCohomology.Q_native D H leftGramInverse rightGramInverse]
      cases index <;> simp [LatticeBcGhostNeutralCohomology.absoluteNativeIndex]⟩

theorem original_neutral_basis_representative (index : LatticeBcGhostNeutralCohomology.AbsoluteIndex D) :
    (originalNeutralBasis D H leftGramInverse rightGramInverse critical index).val =
      (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
        (nativeOriginalCycle D H leftGramInverse rightGramInverse index) := by
  rw [originalNeutralBasis, Module.Basis.map_apply, neutral_original_equiv_inclusion,
    LatticeBcGhostNeutralCohomology.absoluteBasis_apply]
  change (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
    (LatticeBcGhostNeutralCohomology.originalCycleInclusion D H
      (LatticeBcGhostNeutralCohomology.absoluteRepresentCycle D H leftGramInverse rightGramInverse
        ((LatticeBcGhostNeutralCohomology.absoluteFunctionEquiv D).symm (Pi.single index 1)))) = _
  congr 1
  apply Subtype.ext
  exact LatticeBcGhostNeutralCohomology.absolute_basis_representative D index

theorem original_neutral_basis_degree (index : LatticeBcGhostNeutralCohomology.AbsoluteIndex D) :
    originalJ D H leftGramInverse rightGramInverse critical
      (originalNeutralBasis D H leftGramInverse rightGramInverse critical index).val =
    (LatticeBcGhostNeutralCohomology.ghostDegree D
      (LatticeBcGhostNeutralCohomology.absoluteNativeIndex D index) : ℂ) •
      (originalNeutralBasis D H leftGramInverse rightGramInverse critical index).val := by
  rw [original_neutral_basis_representative, originalJ_representative, ← map_smul]
  congr 1
  apply Subtype.ext
  exact LatticeBcGhostNeutralCohomology.J_native D
    (LatticeBcGhostNeutralCohomology.absoluteNativeIndex D index)

def originalNeutralGrade (degree : ℤ) : Submodule ℂ original :=
  LinearMap.range originalP ⊓ LinearMap.ker
    (originalJ D H leftGramInverse rightGramInverse critical - (degree : ℂ) • LinearMap.id)

theorem original_neutral_grade_map (degree : ℤ) :
    (LatticeBcGhostNeutralCohomology.AbsoluteGrade D H leftGramInverse rightGramInverse critical degree).map
      inclusion = originalNeutralGrade D H leftGramInverse rightGramInverse critical degree := by
  ext quotient
  constructor
  · rintro ⟨neutralClass, eigen, rfl⟩
    refine ⟨(original_neutral_projection_range D H leftGramInverse rightGramInverse critical).symm ▸
      ⟨neutralClass, rfl⟩, ?_⟩
    change originalJ D H leftGramInverse rightGramInverse critical (inclusion neutralClass) -
      (degree : ℂ) • inclusion neutralClass = 0
    rw [original_neutral_J, ← map_smul, ← map_sub]
    change LatticeBcGhostNeutralCohomology.absoluteJ D H leftGramInverse rightGramInverse critical neutralClass -
      (degree : ℂ) • neutralClass = 0 at eigen
    rw [eigen, map_zero]
  · rintro ⟨rangeMember, eigen⟩
    rw [original_neutral_projection_range D H leftGramInverse rightGramInverse critical] at rangeMember
    obtain ⟨neutralClass, rfl⟩ := rangeMember
    refine ⟨neutralClass, ?_, rfl⟩
    change LatticeBcGhostNeutralCohomology.absoluteJ D H leftGramInverse rightGramInverse critical neutralClass -
      (degree : ℂ) • neutralClass = 0
    apply LatticeBcGhostNeutralCohomology.absoluteToOriginal_injective D H
    change originalJ D H leftGramInverse rightGramInverse critical (inclusion neutralClass) -
      (degree : ℂ) • inclusion neutralClass = 0 at eigen
    simpa only [map_sub, map_smul, map_zero, original_neutral_J] using eigen

def neutralOriginalGradeEquiv (degree : ℤ) :
    LatticeBcGhostNeutralCohomology.AbsoluteGrade D H leftGramInverse rightGramInverse critical degree ≃ₗ[ℂ]
      originalNeutralGrade D H leftGramInverse rightGramInverse critical degree :=
  (LinearEquiv.ofInjective
    ((inclusion).comp (LatticeBcGhostNeutralCohomology.AbsoluteGrade D H leftGramInverse rightGramInverse
      critical degree).subtype)
    ((LatticeBcGhostNeutralCohomology.absoluteToOriginal_injective D H).comp Subtype.val_injective)).trans
    (LinearEquiv.ofEq _ _ (by
      rw [LinearMap.range_comp, Submodule.range_subtype,
        original_neutral_grade_map D H leftGramInverse rightGramInverse critical degree]))

theorem original_neutral_graded_dimensions :
    Module.finrank ℂ (originalNeutralGrade D H leftGramInverse rightGramInverse critical 0) = 1 ∧
    Module.finrank ℂ (originalNeutralGrade D H leftGramInverse rightGramInverse critical 1) = D.rank ∧
    Module.finrank ℂ (originalNeutralGrade D H leftGramInverse rightGramInverse critical 2) = D.rank ∧
    Module.finrank ℂ (originalNeutralGrade D H leftGramInverse rightGramInverse critical 3) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← (neutralOriginalGradeEquiv D H leftGramInverse rightGramInverse critical 0).finrank_eq]
    exact LatticeBcGhostNeutralCohomology.absolute_ghost_0_finrank D H leftGramInverse rightGramInverse critical
  · rw [← (neutralOriginalGradeEquiv D H leftGramInverse rightGramInverse critical 1).finrank_eq]
    exact LatticeBcGhostNeutralCohomology.absolute_ghost_1_finrank D H leftGramInverse rightGramInverse critical
  · rw [← (neutralOriginalGradeEquiv D H leftGramInverse rightGramInverse critical 2).finrank_eq]
    exact LatticeBcGhostNeutralCohomology.absolute_ghost_2_finrank D H leftGramInverse rightGramInverse critical
  · rw [← (neutralOriginalGradeEquiv D H leftGramInverse rightGramInverse critical 3).finrank_eq]
    exact LatticeBcGhostNeutralCohomology.absolute_ghost_3_finrank D H leftGramInverse rightGramInverse critical

theorem original_neutral_grade_outside (degree : ℤ)
    (notZero : degree ≠ 0) (notOne : degree ≠ 1) (notTwo : degree ≠ 2) (notThree : degree ≠ 3) :
    originalNeutralGrade D H leftGramInverse rightGramInverse critical degree = ⊥ := by
  rw [← original_neutral_grade_map D H leftGramInverse rightGramInverse critical degree,
    LatticeBcGhostNeutralCohomology.absolute_grade_outside D H leftGramInverse rightGramInverse
      critical degree notZero notOne notTwo notThree, Submodule.map_bot]

#print axioms original_neutral_sector
#print axioms neutralOriginalSummandEquiv
#print axioms original_neutral_J
#print axioms original_neutral_basis_degree
#print axioms original_neutral_graded_dimensions
#print axioms original_neutral_grade_outside

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
