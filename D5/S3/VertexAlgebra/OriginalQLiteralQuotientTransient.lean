import D5.S3.VertexAlgebra.OriginalQAmbientMassShellCohomologyTransient
import D5.S3.VertexAlgebra.LatticeBcGhostNeutralCohomology
import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyGhostGrading

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge OriginalQFiniteHplCheck


noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
  (critical : D.rank = 26)

local notation "square" =>
  LatticeBcGhostBrstNilpotence.nilpotent D H leftGramInverse rightGramInverse critical
local notation "ambient" => actualAmbientCohomology D H leftGramInverse rightGramInverse critical
local notation "original" => LatticeBcGhostNeutralCohomology.OriginalCohomology D H

theorem literal_original_boundaries :
    trueBoundaries (Q D H) square = LatticeBcGhostNeutralCohomology.OriginalBoundaries D H := by
  ext cycle
  constructor
  · rintro ⟨preimage, equality⟩
    exact ⟨preimage, congrArg Subtype.val equality⟩
  · rintro ⟨preimage, equality⟩
    exact ⟨preimage, Subtype.ext equality⟩

def ambientOriginalEquiv : ambient ≃ₗ[ℂ] original :=
  Submodule.Quotient.equiv (trueBoundaries (Q D H) square)
    (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H) (LinearEquiv.refl ℂ (LinearMap.ker (Q D H))) (by
      simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id] using
        literal_original_boundaries D H leftGramInverse rightGramInverse critical)

theorem ambient_original_representative (cycle : LinearMap.ker (Q D H)) :
    ambientOriginalEquiv D H leftGramInverse rightGramInverse critical
      (Submodule.Quotient.mk cycle) = (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ cycle := rfl

def originalCohomologyProjection (beta : Charge D) (level : ℤ) : Module.End ℂ original :=
  (ambientOriginalEquiv D H leftGramInverse rightGramInverse critical).toLinearMap.comp
    ((ambientCohomologyProjection D H leftGramInverse rightGramInverse critical beta level).comp
      (ambientOriginalEquiv D H leftGramInverse rightGramInverse critical).symm.toLinearMap)

theorem original_projection_representative (beta : Charge D) (level : ℤ)
    (cycle : LatticeBcGhostNeutralCohomology.OriginalCycles D H) :
    originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level
      ((LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ cycle) =
    (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
      (trueCycleMap (Q D H) (Q D H) (ambientEnergyProjection D beta level)
        (ambient_energy_projection_Q D H leftGramInverse rightGramInverse beta level).symm cycle) := rfl

theorem original_projection_transport (beta : Charge D) (level : ℤ) (quotient : ambient) :
    originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level
      (ambientOriginalEquiv D H leftGramInverse rightGramInverse critical quotient) =
    ambientOriginalEquiv D H leftGramInverse rightGramInverse critical
      (ambientCohomologyProjection D H leftGramInverse rightGramInverse critical beta level quotient) := by
  change ambientOriginalEquiv D H leftGramInverse rightGramInverse critical
    (ambientCohomologyProjection D H leftGramInverse rightGramInverse critical beta level
      ((ambientOriginalEquiv D H leftGramInverse rightGramInverse critical).symm
        (ambientOriginalEquiv D H leftGramInverse rightGramInverse critical quotient))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem original_projection_range (beta : Charge D) (level : ℤ) :
    LinearMap.range (originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level) =
    (LinearMap.range (ambientCohomologyProjection D H leftGramInverse rightGramInverse critical beta level)).map
      (ambientOriginalEquiv D H leftGramInverse rightGramInverse critical).toLinearMap := by
  let equivalence := ambientOriginalEquiv D H leftGramInverse rightGramInverse critical
  rw [originalCohomologyProjection, LinearMap.range_comp]
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top_of_surjective equivalence.symm.toLinearMap equivalence.symm.surjective)]

def ambientOriginalSummandEquiv (beta : Charge D) (level : ℤ) :
    LinearMap.range (ambientCohomologyProjection D H leftGramInverse rightGramInverse critical beta level)
      ≃ₗ[ℂ] LinearMap.range (originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level) :=
  ((ambientOriginalEquiv D H leftGramInverse rightGramInverse critical).submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (original_projection_range D H leftGramInverse rightGramInverse critical beta level).symm)

def sectorOriginalEquiv (beta : Charge D) (level : ℤ) :
    actualSectorCohomology D H leftGramInverse rightGramInverse critical beta level ≃ₗ[ℂ]
      LinearMap.range (originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level) :=
  (sectorAmbientEquiv D H leftGramInverse rightGramInverse critical beta level).trans
    (ambientOriginalSummandEquiv D H leftGramInverse rightGramInverse critical beta level)

theorem original_projection_idempotent (beta : Charge D) (level : ℤ) :
    originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level *
      originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level =
    originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨ambientClass, rfl⟩ :=
    (ambientOriginalEquiv D H leftGramInverse rightGramInverse critical).surjective quotient
  simp only [Module.End.mul_apply, original_projection_transport]
  exact congrArg (ambientOriginalEquiv D H leftGramInverse rightGramInverse critical)
    (LinearMap.congr_fun (ambient_cohomology_projection_idempotent D H leftGramInverse rightGramInverse
      critical beta level) ambientClass)

theorem literal_off_shell_zero (beta : Charge D) (level : ℤ)
    (offShell : chosenH D beta + (level : ℂ) - 1 ≠ 0)
    (quotient : LinearMap.range (originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level)) :
    quotient = 0 := by
  apply (sectorOriginalEquiv D H leftGramInverse rightGramInverse critical beta level).symm.injective
  rw [map_zero]
  exact original_off_shell_sector_zero D H leftGramInverse rightGramInverse critical beta level offShell _

theorem literal_mass_shell_summand (beta : Charge D) (level : ℤ)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (nullDirection : Fin D.rank → ℂ) (xAxis yAxis : Fin D.rank)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    if chosenH D beta + (level : ℂ) - 1 = 0 then
      Nonempty (LinearMap.range (energyProjector D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta xAxis yAxis level) ≃ₗ[ℂ]
        LinearMap.range (originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level))
    else ∀ quotient : LinearMap.range (originalCohomologyProjection D H leftGramInverse rightGramInverse
      critical beta level), quotient = 0 := by
  classical
  by_cases onShell : chosenH D beta + (level : ℂ) - 1 = 0
  · rw [if_pos onShell]
    obtain ⟨reducedSquare, reducedIdentification, ⟨sectorIdentification⟩, ambientIdentification⟩ :=
      original_on_shell_cohomology_equivalences D H leftGramInverse rightGramInverse critical beta level
        frame inverse leftFrameInverse rightFrameInverse nullDirection xAxis yAxis null nonzero distinct
        xRow yRow xDual yDual onShell
    exact ⟨sectorIdentification.trans (sectorOriginalEquiv D H leftGramInverse rightGramInverse critical beta level)⟩
  · rw [if_neg onShell]
    exact literal_off_shell_zero D H leftGramInverse rightGramInverse critical beta level onShell

def originalJ : Module.End ℂ original :=
  let equivalence := (ambientOriginalEquiv D H leftGramInverse rightGramInverse critical).symm.trans
    (ambientAbsoluteEquiv D H leftGramInverse rightGramInverse critical)
  equivalence.symm.toLinearMap.comp
    ((OriginalBrstReassembly.cohomologyJ D H leftGramInverse rightGramInverse critical ⊤
      (OriginalBrstReassembly.top_stable D H) (fun _ _ => Submodule.mem_top)).comp equivalence.toLinearMap)

theorem literal_reduced_quotient_transfer (beta : Charge D) (level : ℤ)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (nullDirection : Fin D.rank → ℂ) (xAxis yAxis : Fin D.rank)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    ∃ reducedSquare : energyReducedDifferential D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level *
      energyReducedDifferential D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level = 0,
      Nonempty (trueCohomology (Source := LinearMap.range
        (energyProjector D H frame inverse leftGramInverse rightGramInverse
          leftFrameInverse rightFrameInverse beta xAxis yAxis level))
        (energyReducedDifferential D H frame inverse leftGramInverse rightGramInverse
          leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level) reducedSquare ≃ₗ[ℂ]
        LinearMap.range (originalCohomologyProjection D H leftGramInverse rightGramInverse critical beta level)) := by
  obtain ⟨reducedSquare, ⟨equivalence⟩⟩ :=
    original_reduced_ambient_quotient_transfer D H leftGramInverse rightGramInverse critical beta level
      frame inverse leftFrameInverse rightFrameInverse nullDirection xAxis yAxis null nonzero distinct
      xRow yRow xDual yDual
  exact ⟨reducedSquare, ⟨equivalence.trans
    (ambientOriginalSummandEquiv D H leftGramInverse rightGramInverse critical beta level)⟩⟩

theorem originalJ_representative (cycle : LatticeBcGhostNeutralCohomology.OriginalCycles D H) :
    originalJ D H leftGramInverse rightGramInverse critical ((LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ cycle) =
      (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
        ⟨OriginalBrstReassembly.nativeJ D cycle.val,
          OriginalBrstReassembly.nativeJ_cycle D H cycle.val cycle.property⟩ := rfl

#print axioms ambientOriginalEquiv
#print axioms literal_mass_shell_summand
#print axioms literal_reduced_quotient_transfer
#print axioms originalJ_representative

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
