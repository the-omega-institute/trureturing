import D5.S3.VertexAlgebra.OriginalQAmbientQuotientTransient
import D5.S3.VertexAlgebra.OriginalQTransferredMassShellTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge OriginalQFiniteHplCheck

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
  (critical : D.rank = 26) (beta : Charge D) (level : ℤ)

local notation "energyQ" => energyOriginalQ D H leftGramInverse rightGramInverse beta level
local notation "sectorSquare" => actual_energy_square D H leftGramInverse rightGramInverse critical beta level
local notation "sector" => actualSectorCohomology D H leftGramInverse rightGramInverse critical beta level
local notation "ambientP" => ambientCohomologyProjection D H leftGramInverse rightGramInverse critical beta level

theorem original_off_shell_cycle_boundary
    (offShell : chosenH D beta + (level : ℂ) - 1 ≠ 0) (cycle : LinearMap.ker energyQ) :
    cycle ∈ trueBoundaries energyQ sectorSquare := by
  let coefficient := chosenH D beta + (level : ℂ) - 1
  have cycleLaw : Q D H cycle.val.val = 0 := congrArg Subtype.val cycle.property
  have ward := LinearMap.congr_fun (ward_identity D H 0) cycle.val.val
  change Q D H (B D 0 cycle.val.val) + B D 0 (Q D H cycle.val.val) =
    (M D H 0 + G D 0) cycle.val.val at ward
  rw [cycleLaw, map_zero, add_zero, cycle.val.property.2] at ward
  refine ⟨ambientEnergyToSector D H leftGramInverse rightGramInverse beta level
    (coefficient⁻¹ • B D 0 cycle.val.val), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change Q D H (ambientEnergyProjection D beta level
    (coefficient⁻¹ • B D 0 cycle.val.val)) = cycle.val.val
  have commutes := LinearMap.congr_fun
    (ambient_energy_projection_Q D H leftGramInverse rightGramInverse beta level)
      (coefficient⁻¹ • B D 0 cycle.val.val)
  simp only [LinearMap.comp_apply] at commutes
  rw [← commutes, map_smul, ward, smul_smul, inv_mul_cancel₀ offShell, one_smul]
  exact ambient_energy_projection_fixed D H leftGramInverse rightGramInverse beta level cycle.val.property

theorem original_off_shell_sector_zero
    (offShell : chosenH D beta + (level : ℂ) - 1 ≠ 0) (quotient : sector) : quotient = 0 := by
  refine Submodule.Quotient.induction_on _ quotient ?_
  intro cycle
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact original_off_shell_cycle_boundary D H leftGramInverse rightGramInverse critical beta level offShell cycle

theorem original_off_shell_ambient_summand_zero
    (offShell : chosenH D beta + (level : ℂ) - 1 ≠ 0) (quotient : LinearMap.range ambientP) :
    quotient = 0 := by
  apply (sectorAmbientEquiv D H leftGramInverse rightGramInverse critical beta level).symm.injective
  rw [map_zero]
  exact original_off_shell_sector_zero D H leftGramInverse rightGramInverse critical beta level offShell _

variable (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
  (nullDirection : Fin D.rank → ℂ) (xAxis yAxis : Fin D.rank)

local notation "energyP" => energyProjector D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta xAxis yAxis level
local notation "reducedDifferential" => energyReducedDifferential D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level

theorem original_reduced_ambient_quotient_transfer
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    ∃ reducedSquare : reducedDifferential * reducedDifferential = 0,
      Nonempty (trueCohomology (Source := LinearMap.range energyP) reducedDifferential reducedSquare
        ≃ₗ[ℂ] LinearMap.range ambientP) := by
  obtain ⟨originalSquare, reducedSquare, ⟨transfer⟩⟩ := original_energy_true_quotient_transfer D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
    critical null nonzero distinct xRow yRow xDual yDual
  exact ⟨reducedSquare, ⟨transfer.trans
    (sectorAmbientEquiv D H leftGramInverse rightGramInverse critical beta level)⟩⟩

include critical in
theorem original_off_shell_reduced_zero
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (offShell : chosenH D beta + (level : ℂ) - 1 ≠ 0) :
    ∃ reducedSquare : reducedDifferential * reducedDifferential = 0,
      ∀ quotient : trueCohomology (Source := LinearMap.range energyP) reducedDifferential reducedSquare,
        quotient = 0 := by
  obtain ⟨reducedSquare, ⟨transfer⟩⟩ := original_reduced_ambient_quotient_transfer D H
    leftGramInverse rightGramInverse critical beta level frame inverse leftFrameInverse rightFrameInverse
    nullDirection xAxis yAxis null nonzero distinct xRow yRow xDual yDual
  refine ⟨reducedSquare, fun quotient => transfer.injective ?_⟩
  rw [map_zero]
  exact original_off_shell_ambient_summand_zero D H leftGramInverse rightGramInverse critical beta level
    offShell (transfer quotient)

theorem original_on_shell_reduced_differential_zero
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (onShell : chosenH D beta + (level : ℂ) - 1 = 0) : reducedDifferential = 0 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  apply Subtype.ext
  change (energyTransferredDifferential D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level state.val : State D) = 0
  rw [energyTransferredDifferential_coe,
    original_transferred_differential_mass_shell D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
      xRow yRow xDual yDual level state.val.val state.val.property.1 state.val.property.2,
    onShell, zero_smul]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem original_on_shell_cohomology_equivalences
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (onShell : chosenH D beta + (level : ℂ) - 1 = 0) :
    ∃ reducedSquare : reducedDifferential * reducedDifferential = 0,
      Nonempty (trueCohomology (Source := LinearMap.range energyP) reducedDifferential reducedSquare
        ≃ₗ[ℂ] LinearMap.range energyP) ∧
      Nonempty (LinearMap.range energyP ≃ₗ[ℂ] sector) ∧
      Nonempty (LinearMap.range energyP ≃ₗ[ℂ] LinearMap.range ambientP) := by
  obtain ⟨originalSquare, reducedSquare, ⟨transfer⟩⟩ := original_energy_true_quotient_transfer D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
    critical null nonzero distinct xRow yRow xDual yDual
  have zeroDifferential := original_on_shell_reduced_differential_zero D H leftGramInverse rightGramInverse
    beta level frame inverse leftFrameInverse rightFrameInverse nullDirection xAxis yAxis
    null nonzero distinct xRow yRow xDual yDual onShell
  have zeroQuotient (Carrier : Type) [AddCommGroup Carrier] [Module ℂ Carrier]
      (operator : Module.End ℂ Carrier) (square : operator * operator = 0) (vanishes : operator = 0) :
      trueCohomology (Source := Carrier) operator square ≃ₗ[ℂ] Carrier := by
    have zeroBoundaries : trueBoundaries (Source := Carrier) operator square = ⊥ := by
      apply le_antisymm _ bot_le
      rintro cycle ⟨state, equality⟩
      change cycle = 0
      apply Subtype.ext
      have coefficientEquality := congrArg Subtype.val equality
      change operator state = cycle.val at coefficientEquality
      rw [← coefficientEquality, vanishes, LinearMap.zero_apply]
      rfl
    let cycleEquiv : LinearMap.ker operator ≃ₗ[ℂ] Carrier :=
      { toFun := Subtype.val
        invFun := fun state => ⟨state, by
          change operator state = 0
          rw [vanishes, LinearMap.zero_apply]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact ((trueBoundaries (Source := Carrier) operator square).quotEquivOfEqBot zeroBoundaries).trans cycleEquiv
  let reducedEquiv := zeroQuotient (↥(LinearMap.range energyP)) reducedDifferential reducedSquare zeroDifferential
  let sectorEquiv := reducedEquiv.symm.trans transfer
  exact ⟨reducedSquare, ⟨reducedEquiv⟩, ⟨sectorEquiv⟩,
    ⟨sectorEquiv.trans (sectorAmbientEquiv D H leftGramInverse rightGramInverse critical beta level)⟩⟩

theorem original_mass_shell_absolute_summand
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    if chosenH D beta + (level : ℂ) - 1 = 0 then
      Nonempty (LinearMap.range energyP ≃ₗ[ℂ]
        LinearMap.range (absoluteCohomologyProjection D H leftGramInverse rightGramInverse
          critical beta level))
    else ∀ quotient : LinearMap.range (absoluteCohomologyProjection D H leftGramInverse rightGramInverse
      critical beta level), quotient = 0 := by
  classical
  by_cases onShell : chosenH D beta + (level : ℂ) - 1 = 0
  · rw [if_pos onShell]
    obtain ⟨reducedSquare, reducedIdentification, ⟨sectorIdentification⟩, ambientIdentification⟩ :=
      original_on_shell_cohomology_equivalences D H leftGramInverse rightGramInverse critical beta level
        frame inverse leftFrameInverse rightFrameInverse nullDirection xAxis yAxis null nonzero distinct
        xRow yRow xDual yDual onShell
    exact ⟨sectorIdentification.trans
      (sectorAbsoluteProjectionEquiv D H leftGramInverse rightGramInverse critical beta level)⟩
  · rw [if_neg onShell]
    intro quotient
    apply (sectorAbsoluteProjectionEquiv D H leftGramInverse rightGramInverse critical beta level).symm.injective
    rw [map_zero]
    exact original_off_shell_sector_zero D H leftGramInverse rightGramInverse critical beta level onShell _

#print axioms original_off_shell_cycle_boundary
#print axioms original_off_shell_sector_zero
#print axioms original_reduced_ambient_quotient_transfer
#print axioms original_on_shell_cohomology_equivalences
#print axioms original_mass_shell_absolute_summand

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
