import D5.S3.VertexAlgebra.OriginalQAmbientEnergyProjectionTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQFiniteHplCheck OriginalBrstReassembly

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
  (critical : D.rank = 26) (beta : Charge D) (level : ℤ)

local notation "energyQ" => energyOriginalQ D H leftGramInverse rightGramInverse beta level
local notation "ambientSquare" =>
  LatticeBcGhostBrstNilpotence.nilpotent D H leftGramInverse rightGramInverse critical

include critical in
theorem actual_energy_square : energyQ * energyQ = 0 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  exact LinearMap.congr_fun ambientSquare state.val

abbrev actualAmbientCohomology := trueCohomology (Q D H) ambientSquare

abbrev actualSectorCohomology := trueCohomology energyQ
  (actual_energy_square D H leftGramInverse rightGramInverse critical beta level)

local notation "ambient" => actualAmbientCohomology D H leftGramInverse rightGramInverse critical
local notation "sector" => actualSectorCohomology D H leftGramInverse rightGramInverse critical beta level
local notation "sectorSquare" => actual_energy_square D H leftGramInverse rightGramInverse critical beta level
local notation "toSector" => ambientEnergyToSector D H leftGramInverse rightGramInverse beta level

theorem ambient_energy_to_sector_chain :
    (energyQ).comp toSector = (toSector).comp (Q D H) := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  exact (LinearMap.congr_fun
    (ambient_energy_projection_Q D H leftGramInverse rightGramInverse beta level) state).symm

def sectorToAmbient : sector →ₗ[ℂ] ambient :=
  trueCohomologyMap energyQ (Q D H) sectorSquare ambientSquare
    (originalEnergySector D H beta level).subtype rfl

def ambientToSector : ambient →ₗ[ℂ] sector :=
  trueCohomologyMap (Q D H) energyQ ambientSquare sectorSquare toSector
    (ambient_energy_to_sector_chain D H leftGramInverse rightGramInverse beta level)

def ambientCohomologyProjection : Module.End ℂ ambient :=
  trueCohomologyMap (Q D H) (Q D H) ambientSquare ambientSquare
    (ambientEnergyProjection D beta level)
    (ambient_energy_projection_Q D H leftGramInverse rightGramInverse beta level).symm

local notation "includeClass" => sectorToAmbient D H leftGramInverse rightGramInverse critical beta level
local notation "projectClass" => ambientToSector D H leftGramInverse rightGramInverse critical beta level
local notation "ambientP" => ambientCohomologyProjection D H leftGramInverse rightGramInverse critical beta level

theorem sector_ambient_retract (quotient : sector) : projectClass (includeClass quotient) = quotient := by
  refine Submodule.Quotient.induction_on _ quotient ?_
  intro cycle
  change Submodule.Quotient.mk
    (trueCycleMap (Q D H) energyQ toSector
      (ambient_energy_to_sector_chain D H leftGramInverse rightGramInverse beta level)
      (trueCycleMap energyQ (Q D H) (originalEnergySector D H beta level).subtype rfl cycle)) =
    (Submodule.Quotient.mk cycle : sector)
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact ambient_energy_projection_fixed D H leftGramInverse rightGramInverse beta level cycle.val.property

theorem sector_to_ambient_injective : Function.Injective includeClass := by
  intro first second equality
  have recovered := congrArg projectClass equality
  simpa only [sector_ambient_retract] using recovered

theorem ambient_cohomology_projection_factor : ambientP = (includeClass).comp projectClass := by
  apply LinearMap.ext
  intro quotient
  refine Submodule.Quotient.induction_on _ quotient ?_
  intro cycle
  rfl

theorem ambient_cohomology_projection_idempotent : ambientP * ambientP = ambientP := by
  apply LinearMap.ext
  intro quotient
  simp only [Module.End.mul_apply, ambient_cohomology_projection_factor, LinearMap.comp_apply,
    sector_ambient_retract]

theorem sector_ambient_projection_range : LinearMap.range includeClass = LinearMap.range ambientP := by
  ext quotient
  constructor
  · rintro ⟨sectorClass, rfl⟩
    refine ⟨includeClass sectorClass, ?_⟩
    rw [ambient_cohomology_projection_factor, LinearMap.comp_apply, sector_ambient_retract]
  · rintro ⟨ambientClass, rfl⟩
    exact ⟨projectClass ambientClass, (LinearMap.congr_fun
      (ambient_cohomology_projection_factor D H leftGramInverse rightGramInverse critical beta level)
        ambientClass).symm⟩

def sectorAmbientEquiv : sector ≃ₗ[ℂ] LinearMap.range ambientP :=
  (LinearEquiv.ofLeftInverse (sector_ambient_retract D H leftGramInverse rightGramInverse
    critical beta level)).trans
    (LinearEquiv.ofEq _ _ (sector_ambient_projection_range D H leftGramInverse rightGramInverse
      critical beta level))

def ambientAbsoluteCycleEquiv : LinearMap.ker (Q D H) ≃ₗ[ℂ] cycles D H ⊤ where
  toFun cycle := ⟨cycle.val, Submodule.mem_top, cycle.property⟩
  invFun cycle := ⟨cycle.val, cycle.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ambient_absolute_boundaries :
    (trueBoundaries (Q D H) ambientSquare).map (ambientAbsoluteCycleEquiv D H).toLinearMap =
      boundaries D H leftGramInverse rightGramInverse critical ⊤ (top_stable D H) := by
  ext cycle
  constructor
  · rintro ⟨sourceCycle, ⟨witness, boundaryEquality⟩, imageEquality⟩
    refine ⟨⟨witness, Submodule.mem_top⟩, ?_⟩
    apply Subtype.ext
    change Q D H witness = cycle.val
    exact (congrArg Subtype.val boundaryEquality).trans (congrArg Subtype.val imageEquality)
  · rintro ⟨witness, boundaryEquality⟩
    refine ⟨⟨cycle.val, cycle.property.2⟩, ⟨witness.val, ?_⟩, rfl⟩
    apply Subtype.ext
    change Q D H witness.val = cycle.val
    exact congrArg (fun state : cycles D H ⊤ => state.val) boundaryEquality

def ambientAbsoluteEquiv : ambient ≃ₗ[ℂ]
    absoluteCohomology D H leftGramInverse rightGramInverse critical :=
  Submodule.Quotient.equiv (trueBoundaries (Q D H) ambientSquare)
    (boundaries D H leftGramInverse rightGramInverse critical ⊤ (top_stable D H))
    (ambientAbsoluteCycleEquiv D H)
    (ambient_absolute_boundaries D H leftGramInverse rightGramInverse critical)

def absoluteEnergySummand : Submodule ℂ
    (absoluteCohomology D H leftGramInverse rightGramInverse critical) :=
  (LinearMap.range ambientP).map (ambientAbsoluteEquiv D H leftGramInverse rightGramInverse
    critical).toLinearMap

def absoluteCohomologyProjection : Module.End ℂ
    (absoluteCohomology D H leftGramInverse rightGramInverse critical) :=
  homologyMap D H leftGramInverse rightGramInverse critical ⊤ ⊤ (top_stable D H) (top_stable D H)
    (ambientEnergyProjection D beta level) (fun _ _ => Submodule.mem_top)
    (ambient_energy_projection_Q D H leftGramInverse rightGramInverse beta level)

theorem absolute_energy_projection_transport (quotient : ambient) :
    absoluteCohomologyProjection D H leftGramInverse rightGramInverse critical beta level
      (ambientAbsoluteEquiv D H leftGramInverse rightGramInverse critical quotient) =
    ambientAbsoluteEquiv D H leftGramInverse rightGramInverse critical (ambientP quotient) := by
  refine Submodule.Quotient.induction_on _ quotient ?_
  intro cycle
  rfl

theorem absolute_energy_projection_range :
    LinearMap.range (absoluteCohomologyProjection D H leftGramInverse rightGramInverse critical beta level) =
      absoluteEnergySummand D H leftGramInverse rightGramInverse critical beta level := by
  let equivalence := ambientAbsoluteEquiv D H leftGramInverse rightGramInverse critical
  let actualProjection := absoluteCohomologyProjection D H leftGramInverse rightGramInverse critical beta level
  have interchange : actualProjection.comp equivalence.toLinearMap = equivalence.toLinearMap.comp ambientP := by
    apply LinearMap.ext
    exact absolute_energy_projection_transport D H leftGramInverse rightGramInverse critical beta level
  change LinearMap.range actualProjection = (LinearMap.range ambientP).map equivalence.toLinearMap
  calc
    _ = LinearMap.range (actualProjection.comp equivalence.toLinearMap) :=
      (LinearMap.range_comp_of_range_eq_top actualProjection
        (LinearMap.range_eq_top_of_surjective equivalence.toLinearMap equivalence.surjective)).symm
    _ = LinearMap.range (equivalence.toLinearMap.comp ambientP) := congrArg LinearMap.range interchange
    _ = _ := LinearMap.range_comp ambientP equivalence.toLinearMap

def sectorAbsoluteSummandEquiv : sector ≃ₗ[ℂ]
    absoluteEnergySummand D H leftGramInverse rightGramInverse critical beta level :=
  (sectorAmbientEquiv D H leftGramInverse rightGramInverse critical beta level).trans
    ((ambientAbsoluteEquiv D H leftGramInverse rightGramInverse critical).submoduleMap
      (LinearMap.range ambientP))

def sectorAbsoluteProjectionEquiv : sector ≃ₗ[ℂ]
    LinearMap.range (absoluteCohomologyProjection D H leftGramInverse rightGramInverse critical beta level) :=
  (sectorAbsoluteSummandEquiv D H leftGramInverse rightGramInverse critical beta level).trans
    (LinearEquiv.ofEq _ _ (absolute_energy_projection_range D H leftGramInverse rightGramInverse
      critical beta level).symm)

#print axioms sector_to_ambient_injective
#print axioms sectorAmbientEquiv
#print axioms sectorAbsoluteSummandEquiv
#print axioms sectorAbsoluteProjectionEquiv

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
