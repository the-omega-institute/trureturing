/- GID: D5/S3/VertexAlgebra/OriginalAbsoluteGradedSector
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual original nonzero-charge on-shell sector has precisely its two transverse ghost branches. -/

import D5.S3.VertexAlgebra.OriginalAbsoluteGhostDoublet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.OriginalAbsoluteGradedSector

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  LatticeBcGhostNeutralCohomology LatticeOscillatorFockMetric OriginalQQuartetSource
  OriginalQEnergyInclusionPairing OriginalBrstReassembly OriginalQPhysicalPairing
  OriginalAbsoluteGhostDoublet RelativePairing.AbsolutePhysicalNoGhost
  RelativePairing.RealPhysicalNoGhost RelativePairing.NativePhysicalRealization
open scoped DirectSum BigOperators

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
variable (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
variable (shell : chosenH D beta + (level : ℂ) - 1 = 0) (chargeNonzero : beta ≠ 0)
variable (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
  (D.rank : ℤ) - 2)

local notation "sector" => originalEnergySector D H beta level
local notation "stable" => energyStable D H leftGram rightGram beta level
local notation "projected" => energyGhostProjected D H leftGram rightGram beta level
local notation "degreeCohomology" => ghostCohomology D H leftGram rightGram critical sector stable
local notation "fullCohomology" => Cohomology D H leftGram rightGram critical sector stable
local notation "split" => ghostClassSplit D H leftGram rightGram critical sector stable projected
local notation "includeClass" => ghostClassInclude D H leftGram rightGram critical sector stable

def choice : AdmissibleFrame D beta :=
  admissibleOfNative D H beta
    (constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian)

local notation "frameChoice" => choice D H leftGram rightGram beta critical chargeNonzero lorentzian
local notation "transverse" => TransverseDownIndex D (AdmissibleFrame.xAxis frameChoice)
  (AdmissibleFrame.yAxis frameChoice) level →₀ ℂ

def downEquiv : transverse ≃ₗ[ℂ] degreeCohomology 1 :=
  (nativePhysicalEquiv D H (frameChoice).frame (frameChoice).inverse leftGram rightGram
    (frameChoice).leftFrame (frameChoice).rightFrame beta (frameChoice).direction
    (frameChoice).xAxis (frameChoice).yAxis level critical (frameChoice).null
    (frameChoice).nonzero (frameChoice).distinct (frameChoice).xRow (frameChoice).yRow
    (frameChoice).xDual (frameChoice).yDual shell).trans
    (absolutePhysicalEquiv D H leftGram rightGram beta level critical shell chargeNonzero
      lorentzian).symm

def upEquiv : transverse ≃ₗ[ℂ] degreeCohomology 2 :=
  nativeUpEquiv D H (frameChoice).frame (frameChoice).inverse leftGram rightGram
    (frameChoice).leftFrame (frameChoice).rightFrame beta (frameChoice).direction
    (frameChoice).xAxis (frameChoice).yAxis level critical (frameChoice).null
    (frameChoice).nonzero (frameChoice).distinct (frameChoice).xRow (frameChoice).yRow
    (frameChoice).xDual (frameChoice).yDual shell

def twoDegreesEquiv : (⨁ degree : ℤ, degreeCohomology degree) ≃ₗ[ℂ]
    degreeCohomology 1 × degreeCohomology 2 where
  toFun pieces := (pieces 1, pieces 2)
  invFun pair := DirectSum.of degreeCohomology 1 pair.1 + DirectSum.of degreeCohomology 2 pair.2
  left_inv := by
    intro pieces
    apply DFinsupp.ext
    intro degree
    by_cases first : degree = 1
    · subst degree
      simp [DirectSum.of_apply]
    · by_cases second : degree = 2
      · subst degree
        simp [DirectSum.of_apply]
      · have zero := original_other_ghost_cohomology_zero D H leftGram rightGram beta level
          critical chargeNonzero lorentzian degree first second (pieces degree)
        simpa [DirectSum.of_apply, first, second, Ne.symm first, Ne.symm second] using zero.symm
  right_inv := by intro pair; ext <;> simp [DirectSum.of_apply]
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar pieces; rfl

def ungradedEquiv : fullCohomology ≃ₗ[ℂ] transverse × transverse :=
  (ghostCohomologyEquiv D H leftGram rightGram critical sector stable projected).trans
    ((twoDegreesEquiv D H leftGram rightGram beta level critical chargeNonzero lorentzian).trans
      ((downEquiv D H leftGram rightGram beta level critical shell chargeNonzero lorentzian).symm.prodCongr
        (upEquiv D H leftGram rightGram beta level critical shell chargeNonzero lorentzian).symm))

local notation "equivalence" => ungradedEquiv D H leftGram rightGram beta level critical shell
  chargeNonzero lorentzian
local notation "downIdentification" => downEquiv D H leftGram rightGram beta level critical shell
  chargeNonzero lorentzian
local notation "upIdentification" => upEquiv D H leftGram rightGram beta level critical shell
  chargeNonzero lorentzian

theorem ungraded_degree_one (quotient : fullCohomology) :
    downIdentification (equivalence quotient).1 = split quotient 1 := by
  change downIdentification ((downIdentification).symm (split quotient 1)) = _
  exact LinearEquiv.apply_symm_apply _ _

theorem ungraded_degree_two (quotient : fullCohomology) :
    upIdentification (equivalence quotient).2 = split quotient 2 := by
  change upIdentification ((upIdentification).symm (split quotient 2)) = _
  exact LinearEquiv.apply_symm_apply _ _

theorem ungraded_ghost_one_projector (quotient : fullCohomology) :
    equivalence (includeClass 1 (split quotient 1)) = ((equivalence quotient).1, 0) := by
  change ((downIdentification).symm (split (includeClass 1 (split quotient 1)) 1),
    (upIdentification).symm (split (includeClass 1 (split quotient 1)) 2)) =
      ((downIdentification).symm (split quotient 1), 0)
  rw [ghostSplit_include]
  simp [DirectSum.lof_eq_of, DirectSum.of_apply]

theorem ungraded_ghost_two_projector (quotient : fullCohomology) :
    equivalence (includeClass 2 (split quotient 2)) = (0, (equivalence quotient).2) := by
  change ((downIdentification).symm (split (includeClass 2 (split quotient 2)) 1),
    (upIdentification).symm (split (includeClass 2 (split quotient 2)) 2)) =
      (0, (upIdentification).symm (split quotient 2))
  rw [ghostSplit_include]
  simp [DirectSum.lof_eq_of, DirectSum.of_apply]

def fullOriginalCycle : cycles D H sector →ₗ[ℂ] OriginalCycles D H :=
  (cycles D H sector).subtype.codRestrict (OriginalCycles D H) (fun state => state.property.2)

def fullOriginalClass : cycles D H sector →ₗ[ℂ] OriginalCohomology D H :=
  (OriginalBoundaries D H).mkQ.comp (fullOriginalCycle D H beta level)

theorem full_unrestricted_boundary_intersection :
    boundaries D H leftGram rightGram critical sector stable =
      (OriginalBoundaries D H).comap (fullOriginalCycle D H beta level) := by
  ext state
  rw [boundary_iff]
  change (∃ preimage : sector, Q D H preimage.val = state.val) ↔
    ∃ preimage : State D, Q D H preimage = state.val
  constructor
  · rintro ⟨preimage, equation⟩
    exact ⟨preimage.val, equation⟩
  · intro ambient
    obtain ⟨preimage, equation⟩ := (ambient_boundary_sector_preimage D H leftGram rightGram
      beta level ⟨state.val, state.property.1⟩).mp ambient
    exact ⟨preimage, congrArg Subtype.val equation⟩

private theorem fullOriginalClass_kernel :
    LinearMap.ker (fullOriginalClass D H beta level) =
      boundaries D H leftGram rightGram critical sector stable := by
  rw [full_unrestricted_boundary_intersection D H leftGram rightGram beta level critical]
  ext state
  exact Submodule.Quotient.mk_eq_zero _

def fullOriginalInclusion : fullCohomology →ₗ[ℂ] OriginalCohomology D H :=
  (boundaries D H leftGram rightGram critical sector stable).liftQ
    (fullOriginalClass D H beta level)
    (by rw [fullOriginalClass_kernel D H leftGram rightGram beta level critical])

private theorem fullOriginalInclusion_injective : Function.Injective
    (fullOriginalInclusion D H leftGram rightGram beta level critical) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _
    (by rw [fullOriginalClass_kernel D H leftGram rightGram beta level critical])

def originalImageEquiv : LinearMap.range
    (fullOriginalInclusion D H leftGram rightGram beta level critical) ≃ₗ[ℂ]
    transverse × transverse :=
  (LinearEquiv.ofInjective (fullOriginalInclusion D H leftGram rightGram beta level critical)
    (fullOriginalInclusion_injective D H leftGram rightGram beta level critical)).symm.trans
    equivalence

#print axioms ungradedEquiv
#print axioms ungraded_ghost_one_projector
#print axioms ungraded_ghost_two_projector
#print axioms full_unrestricted_boundary_intersection
#print axioms originalImageEquiv

end
end D5.S3.VertexAlgebra.OriginalAbsoluteGradedSector
