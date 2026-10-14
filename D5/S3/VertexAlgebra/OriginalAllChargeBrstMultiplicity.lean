/- GID: D5/S3/VertexAlgebra/OriginalAllChargeBrstMultiplicity
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal original all-charge integral graded multiplicities and off-shell contraction. -/

import D5.S3.VertexAlgebra.OriginalZeroChargeGradedSectorBridge
import D5.S3.VertexAlgebra.OriginalColoredBrstMultiplicity
import D5.S3.VertexAlgebra.OriginalQAmbientMassShellCohomologyTransient
import D5.S3.VertexAlgebra.OriginalQLiteralQuotientTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.OriginalAllChargeBrstMultiplicity

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQQuartetSource OriginalQFiniteHplCheck OriginalBrstReassembly
  RelativePairing.AbsolutePhysicalNoGhost OriginalColoredBrstMultiplicity LatticeOscillatorFockMetric

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
  (critical : D.rank = 26) (beta : Charge D) (level : ℤ)

local notation "sector" => originalEnergySector D H beta level
local notation "stable" => energyStable D H leftGram rightGram beta level
local notation "energyQ" => energyOriginalQ D H leftGram rightGram beta level
local notation "energySquare" => actual_energy_square D H leftGram rightGram critical beta level
local notation "sectorBoundary" => boundaries D H leftGram rightGram critical sector stable
local notation "sectorCohomology" => Cohomology D H leftGram rightGram critical sector stable
local notation "degreeCohomology" => ghostCohomology D H leftGram rightGram critical sector stable
local notation "degreeInclude" => ghostClassInclude D H leftGram rightGram critical sector stable
local notation "projected" => energyGhostProjected D H leftGram rightGram beta level

def originalCycleEquiv : LinearMap.ker energyQ ≃ₗ[ℂ] cycles D H sector where
  toFun state := ⟨state.val.val, state.val.property, congrArg Subtype.val state.property⟩
  invFun state := ⟨⟨state.val, state.property.1⟩, Subtype.ext state.property.2⟩
  left_inv state := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv state := by apply Subtype.ext; rfl
  map_add' first second := by apply Subtype.ext; rfl
  map_smul' scalar state := by apply Subtype.ext; rfl

private theorem original_boundary_map :
    (trueBoundaries energyQ energySquare).map
      (originalCycleEquiv D H leftGram rightGram beta level).toLinearMap = sectorBoundary := by
  ext state
  rw [boundary_iff]
  constructor
  · rintro ⟨native, ⟨preimage, equation⟩, rfl⟩
    exact ⟨preimage, congrArg (fun cycle : LinearMap.ker energyQ => cycle.val.val) equation⟩
  · rintro ⟨preimage, equation⟩
    refine ⟨(originalCycleEquiv D H leftGram rightGram beta level).symm state,
      ⟨preimage, ?_⟩, (originalCycleEquiv D H leftGram rightGram beta level).apply_symm_apply state⟩
    apply Subtype.ext
    apply Subtype.ext
    exact equation

def originalSectorEquiv : actualSectorCohomology D H leftGram rightGram critical beta level ≃ₗ[ℂ]
    sectorCohomology := by
  let induced := Submodule.Quotient.equiv
    (M := LinearMap.ker energyQ) (N := cycles D H sector)
    (σ₁₂ := RingHom.id ℂ) (σ₂₁ := RingHom.id ℂ)
    (trueBoundaries energyQ energySquare) sectorBoundary
    (originalCycleEquiv D H leftGram rightGram beta level)
    (original_boundary_map D H leftGram rightGram critical beta level)
  exact induced

def literalOriginalSummandEquiv : sectorCohomology ≃ₗ[ℂ]
    LinearMap.range (originalCohomologyProjection D H leftGram rightGram critical beta level) :=
  (originalSectorEquiv D H leftGram rightGram critical beta level).symm.trans
    (sectorOriginalEquiv D H leftGram rightGram critical beta level)

theorem original_ambient_representative (state : cycles D H sector) :
    (literalOriginalSummandEquiv D H leftGram rightGram critical beta level
      (Submodule.Quotient.mk state)).val =
    (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
      ⟨state.val, state.property.2⟩ := rfl

theorem original_off_shell_zero
    (offShell : chosenH D beta + (level : ℂ) - 1 ≠ 0) (state : sectorCohomology) : state = 0 := by
  obtain ⟨cycle, rfl⟩ := (sectorBoundary).mkQ_surjective state
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have originalBoundary := original_off_shell_cycle_boundary D H leftGram rightGram critical
    beta level offShell ((originalCycleEquiv D H leftGram rightGram beta level).symm cycle)
  rw [← original_boundary_map D H leftGram rightGram critical beta level]
  exact ⟨(originalCycleEquiv D H leftGram rightGram beta level).symm cycle,
    originalBoundary, (originalCycleEquiv D H leftGram rightGram beta level).apply_symm_apply cycle⟩

private theorem degree_include_injective (degree : ℤ) :
    Function.Injective (degreeInclude degree) := by
  intro first second equality
  have split := congrArg
    (ghostClassSplit D H leftGram rightGram critical sector stable projected) equality
  rw [ghostSplit_include, ghostSplit_include] at split
  simpa [DirectSum.lof_eq_of, DirectSum.of_apply] using
    congrArg (fun pieces => pieces degree) split

private theorem off_shell_dimensions
    (offShell : chosenH D beta + (level : ℂ) - 1 ≠ 0) (degree : ℤ) :
    Module.finrank ℂ (degreeCohomology degree) = 0 ∧
      Module.finrank ℂ sectorCohomology = 0 := by
  have fullZero : ∀ state : sectorCohomology, state = 0 :=
    original_off_shell_zero D H leftGram rightGram critical beta level offShell
  have degreeZero : ∀ state : degreeCohomology degree, state = 0 := by
    intro state
    apply degree_include_injective D H leftGram rightGram critical beta level degree
    rw [map_zero]
    exact fullZero _
  letI : Subsingleton sectorCohomology := ⟨fun first second => (fullZero first).trans (fullZero second).symm⟩
  letI : Subsingleton (degreeCohomology degree) :=
    ⟨fun first second => (degreeZero first).trans (degreeZero second).symm⟩
  exact ⟨Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton⟩

def exceptionalMultiplicity (degree : ℤ) : ℕ :=
  if degree = 0 then 1 else if degree = 1 then 26 else
    if degree = 2 then 26 else if degree = 3 then 1 else 0

def gradedMultiplicity (beta : Charge D) (level degree : ℤ) : ℕ :=
  if chosenH D beta + (level : ℂ) - 1 = 0 then
    if beta = 0 then exceptionalMultiplicity degree
    else if degree = 1 ∨ degree = 2 then p24 level else 0
  else 0

def totalMultiplicity (beta : Charge D) (level : ℤ) : ℕ :=
  if chosenH D beta + (level : ℂ) - 1 = 0 then
    if beta = 0 then 54 else 2 * p24 level
  else 0

variable (signatureLaw : beta ≠ 0 →
  QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' = (D.rank : ℤ) - 2)

include signatureLaw in
theorem original_all_charge_multiplicities (degree : ℤ) :
    Module.finrank ℂ (degreeCohomology degree) = gradedMultiplicity D beta level degree ∧
      Module.finrank ℂ sectorCohomology = totalMultiplicity D beta level := by
  classical
  by_cases shell : chosenH D beta + (level : ℂ) - 1 = 0
  · by_cases zeroCharge : beta = 0
    · subst beta
      have levelOne : level = 1 := by
        have complexOne : (level : ℂ) = 1 := sub_eq_zero.mp (by
          simpa [chosenH, complexCharge, gramPair] using shell)
        exact_mod_cast complexOne
      subst level
      rw [gradedMultiplicity, totalMultiplicity, if_pos shell, if_pos shell,
        if_pos rfl, if_pos rfl]
      constructor
      · simpa only [exceptionalMultiplicity, critical] using
          OriginalZeroChargeGradedSectorBridge.original_zero_graded_finrank
            D H leftGram rightGram critical degree
      · have inherited := OriginalZeroChargeGradedSectorBridge.original_zero_finrank
          D H leftGram rightGram critical
        simpa only [critical, Nat.reduceMul, Nat.reduceAdd] using inherited
    · have inherited := original_brst_multiplicities D H leftGram rightGram beta level
        critical shell zeroCharge (signatureLaw zeroCharge)
      rw [gradedMultiplicity, totalMultiplicity, if_pos shell, if_pos shell,
        if_neg zeroCharge, if_neg zeroCharge]
      refine ⟨?_, inherited.2.2⟩
      by_cases first : degree = 1
      · subst degree
        simpa using inherited.1
      by_cases second : degree = 2
      · subst degree
        simpa using inherited.2.1
      rw [if_neg (not_or.mpr ⟨first, second⟩)]
      have everyZero := original_other_ghost_cohomology_zero D H leftGram rightGram beta level
        critical zeroCharge (signatureLaw zeroCharge) degree first second
      letI : Subsingleton (degreeCohomology degree) :=
        ⟨fun firstState secondState => (everyZero firstState).trans (everyZero secondState).symm⟩
      exact Module.finrank_zero_of_subsingleton
  · rw [gradedMultiplicity, totalMultiplicity, if_neg shell, if_neg shell]
    exact off_shell_dimensions D H leftGram rightGram critical beta level shell degree

include signatureLaw in
theorem original_negative_level_multiplicities (negative : level < 0) (degree : ℤ) :
    Module.finrank ℂ (degreeCohomology degree) = 0 ∧
      Module.finrank ℂ sectorCohomology = 0 := by
  have classification := original_all_charge_multiplicities D H leftGram rightGram critical
    beta level signatureLaw degree
  have partitionZero : p24 level = 0 := by
    simp [p24, coloredMultiplicity, negative]
  have zeroOffShell : beta = 0 → chosenH D beta + (level : ℂ) - 1 ≠ 0 := by
    rintro rfl shell
    have complexOne : (level : ℂ) = 1 := sub_eq_zero.mp (by
      simpa [chosenH, complexCharge, gramPair] using shell)
    have levelOne : level = 1 := by exact_mod_cast complexOne
    omega
  by_cases shell : chosenH D beta + (level : ℂ) - 1 = 0
  · have nonzero : beta ≠ 0 := fun zeroCharge => zeroOffShell zeroCharge shell
    simpa [gradedMultiplicity, totalMultiplicity, shell, nonzero, partitionZero]
      using classification
  · simpa [gradedMultiplicity, totalMultiplicity, shell] using classification

#print axioms originalSectorEquiv
#print axioms original_off_shell_zero
#print axioms original_all_charge_multiplicities
#print axioms original_negative_level_multiplicities

end
end D5.S3.VertexAlgebra.OriginalAllChargeBrstMultiplicity
