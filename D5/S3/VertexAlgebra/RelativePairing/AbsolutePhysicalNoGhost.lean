/- GID: D5/S3/VertexAlgebra/RelativePairing/AbsolutePhysicalNoGhost
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute ghost-one classes have the literal physical image and its canonical no-ghost form. -/

import D5.S3.VertexAlgebra.OriginalAbsoluteGhostCompleteness
import D5.S3.VertexAlgebra.RelativePairing.RealPhysicalNoGhost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  LatticeBcGhostNeutralCohomology OriginalQQuartetSource OriginalBrstReassembly
  OriginalQPhysicalPairing OriginalAbsoluteGhostCompleteness RealPhysicalNoGhost
  LatticeOscillatorFockMetric

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
variable (beta : Charge D) (level : ℤ)

def energyStable : ∀ state, state ∈ originalEnergySector D H beta level →
    Q D H state ∈ originalEnergySector D H beta level :=
  fun state member => (energyOriginalQ D H leftGram rightGram beta level ⟨state, member⟩).property

include leftGram rightGram in
theorem energyGhostProjected (degree : ℤ) (state : State D)
    (member : state ∈ originalEnergySector D H beta level) :
    ghostProjection D degree state ∈ originalEnergySector D H beta level := by
  rw [original_energy_sector_partition D H leftGram rightGram] at member ⊢
  rw [mem_part] at member ⊢
  intro label outside
  rw [ghostProjection, projection_coeff, (member label outside)]
  split <;> rfl

def ghostOriginalCycle (degree : ℤ) :
    ghostCycles D H (originalEnergySector D H beta level) degree →ₗ[ℂ] OriginalCycles D H :=
  (ghostCycles D H (originalEnergySector D H beta level) degree).subtype.codRestrict
    (OriginalCycles D H) (fun state => state.property.1.2)

def ghostOriginalClass (degree : ℤ) :
    ghostCycles D H (originalEnergySector D H beta level) degree →ₗ[ℂ] OriginalCohomology D H :=
  (OriginalBoundaries D H).mkQ.comp (ghostOriginalCycle D H beta level degree)

variable (critical : D.rank = 26)

local notation "stable" => energyStable D H leftGram rightGram beta level
local notation "projected" => energyGhostProjected D H leftGram rightGram beta level
local notation "degreeCycles" => ghostCycles D H (originalEnergySector D H beta level)
local notation "degreeBoundaries" => ghostBoundaries D H leftGram rightGram critical
  (originalEnergySector D H beta level) stable
local notation "degreeCohomology" => ghostCohomology D H leftGram rightGram critical
  (originalEnergySector D H beta level) stable

theorem ghostBoundary_unrestricted_intersection (degree : ℤ) :
    degreeBoundaries degree = (OriginalBoundaries D H).comap
      (ghostOriginalCycle D H beta level degree) := by
  rw [ghostBoundary_original_intersection D H leftGram rightGram critical
    (originalEnergySector D H beta level) stable projected degree]
  ext state
  rw [Submodule.mem_comap, boundary_iff]
  change (∃ preimage : originalEnergySector D H beta level, Q D H preimage.val = state.val) ↔
    ∃ preimage : State D, Q D H preimage = state.val
  constructor
  · rintro ⟨preimage, equation⟩
    exact ⟨preimage.val, equation⟩
  · intro ambient
    obtain ⟨preimage, equation⟩ :=
      (ambient_boundary_sector_preimage D H leftGram rightGram beta level
        ⟨state.val, state.property.1.1⟩).mp ambient
    exact ⟨preimage, congrArg Subtype.val equation⟩

theorem ghostOriginalClass_kernel (degree : ℤ) :
    LinearMap.ker (ghostOriginalClass D H beta level degree) = degreeBoundaries degree := by
  rw [ghostBoundary_unrestricted_intersection D H leftGram rightGram beta level critical degree]
  ext state
  change (OriginalBoundaries D H).mkQ (ghostOriginalCycle D H beta level degree state) = 0 ↔
    ghostOriginalCycle D H beta level degree state ∈ OriginalBoundaries D H
  exact Submodule.Quotient.mk_eq_zero _

def ghostOriginalInclusion (degree : ℤ) : degreeCohomology degree →ₗ[ℂ] OriginalCohomology D H :=
  (degreeBoundaries degree).liftQ (ghostOriginalClass D H beta level degree)
    (by rw [ghostOriginalClass_kernel D H leftGram rightGram beta level critical degree])

theorem ghostOriginalInclusion_injective (degree : ℤ) :
    Function.Injective (ghostOriginalInclusion D H leftGram rightGram beta level critical degree) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _
    (by rw [ghostOriginalClass_kernel D H leftGram rightGram beta level critical degree])

variable (shell : chosenH D beta + (level : ℂ) - 1 = 0) (chargeNonzero : beta ≠ 0)
variable (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
  (D.rank : ℤ) - 2)

include leftGram rightGram critical shell chargeNonzero lorentzian in
theorem original_absolute_ghost_one_representative (state : originalEnergySector D H beta level)
    (cycle : Q D H state.val = 0) (homogeneous : state.val ∈ ghostPart D 1) :
    ∃ representative : physicalCycles D H beta level,
      ∃ preimage : originalEnergySector D H beta level, preimage.val ∈ ghostPart D 0 ∧
        state.val - physicalState D H beta level representative = Q D H preimage.val := by
  let native := constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian
  let choice := admissibleOfNative D H beta native
  exact absolute_ghost_one_representative D H choice.frame choice.inverse leftGram rightGram
    choice.leftFrame choice.rightFrame beta choice.direction choice.xAxis choice.yAxis level
    critical choice.null choice.nonzero choice.distinct choice.xRow choice.yRow
    choice.xDual choice.yDual shell state cycle homogeneous

include leftGram rightGram critical shell chargeNonzero lorentzian in
theorem absolute_degree_one_image :
    LinearMap.range (ghostOriginalClass D H beta level 1) = physicalImage D H beta level := by
  rw [physicalImage_eq]
  ext quotient
  constructor
  · rintro ⟨state, rfl⟩
    obtain ⟨representative, preimage, homogeneous, equation⟩ :=
      original_absolute_ghost_one_representative D H leftGram rightGram beta level critical
        shell chargeNonzero lorentzian ⟨state.val, state.property.1.1⟩
        state.property.1.2 state.property.2
    refine ⟨representative.val, representative.property, ?_⟩
    have difference : ghostOriginalCycle D H beta level 1 state - representative.val ∈
        OriginalBoundaries D H := ⟨preimage.val, equation.symm⟩
    have equalClasses := (Submodule.Quotient.eq _).mpr difference
    exact equalClasses.symm
  · rintro ⟨representative, member, rfl⟩
    refine ⟨⟨representative.val, ⟨⟨member.1.1, representative.property⟩, member.2⟩⟩, rfl⟩

include shell chargeNonzero lorentzian in
theorem absolute_degree_one_inclusion_image :
    LinearMap.range (ghostOriginalInclusion D H leftGram rightGram beta level critical 1) =
      physicalImage D H beta level := by
  rw [← absolute_degree_one_image D H leftGram rightGram beta level critical shell
    chargeNonzero lorentzian]
  ext quotient
  constructor
  · rintro ⟨quotient, rfl⟩
    obtain ⟨state, rfl⟩ := (degreeBoundaries 1).mkQ_surjective quotient
    exact ⟨state, rfl⟩
  · rintro ⟨state, rfl⟩
    exact ⟨(degreeBoundaries 1).mkQ state, rfl⟩

def absolutePhysicalEquiv : degreeCohomology 1 ≃ₗ[ℂ] physicalImage D H beta level :=
  (LinearEquiv.ofInjective (ghostOriginalInclusion D H leftGram rightGram beta level critical 1)
    (ghostOriginalInclusion_injective D H leftGram rightGram beta level critical 1)).trans
    (LinearEquiv.ofEq _ _ (absolute_degree_one_inclusion_image D H leftGram rightGram beta
      level critical shell chargeNonzero lorentzian))

local notation "identification" => absolutePhysicalEquiv D H leftGram rightGram beta level
  critical shell chargeNonzero lorentzian

theorem absolutePhysicalEquiv_original_representative (state : degreeCycles 1) :
    (identification ((degreeBoundaries 1).mkQ state)).val =
      (OriginalBoundaries D H).mkQ (ghostOriginalCycle D H beta level 1 state) := rfl

def physicalGhostCycle (state : physicalCycles D H beta level) : degreeCycles 1 :=
  ⟨state.val.val, ⟨⟨state.property.1.1, state.val.property⟩, state.property.2⟩⟩

theorem absolutePhysicalEquiv_inverse_representative (state : physicalCycles D H beta level) :
    (identification).symm (imageRepresentative D H beta level state) =
      (degreeBoundaries 1).mkQ (physicalGhostCycle D H beta level state) := by
  apply (identification).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rfl

theorem absolutePhysicalEquiv_physical_representative (state : physicalCycles D H beta level) :
    identification ((degreeBoundaries 1).mkQ (physicalGhostCycle D H beta level state)) =
      imageRepresentative D H beta level state := by
  apply Subtype.ext
  rfl

def absoluteCanonicalForm : degreeCohomology 1 →ₗ⋆[ℂ] degreeCohomology 1 →ₗ[ℂ] ℂ where
  toFun first := (canonicalForm D H leftGram rightGram beta level critical shell chargeNonzero
    lorentzian (identification first)).comp (identification).toLinearMap
  map_add' := by intro first second; ext other; simp
  map_smul' := by intro scalar first; ext other; simp

local notation "form" => absoluteCanonicalForm D H leftGram rightGram beta level critical
  shell chargeNonzero lorentzian

theorem absoluteCanonicalForm_recovery (first second : physicalCycles D H beta level) :
    form ((degreeBoundaries 1).mkQ (physicalGhostCycle D H beta level first))
      ((degreeBoundaries 1).mkQ (physicalGhostCycle D H beta level second)) =
    LatticeBcGhostHermitianForm.F D (physicalState D H beta level first)
      (C D 0 (physicalState D H beta level second)) := by
  change (canonicalForm D H leftGram rightGram beta level critical shell chargeNonzero lorentzian
    (identification ((degreeBoundaries 1).mkQ (physicalGhostCycle D H beta level first))))
    (identification ((degreeBoundaries 1).mkQ (physicalGhostCycle D H beta level second))) = _
  rw [absolutePhysicalEquiv_physical_representative,
    absolutePhysicalEquiv_physical_representative]
  exact canonicalForm_recovery D H leftGram rightGram beta level critical shell chargeNonzero
    lorentzian first second

theorem absoluteCanonicalForm_noGhost :
    (∀ state : degreeCohomology 1, state ≠ 0 →
      0 < (-form state state).re ∧ (-form state state).im = 0) ∧
    (∀ state : degreeCohomology 1, (∀ other, form state other = 0) ↔ state = 0) ∧
    (∀ state : degreeCohomology 1, (∀ other, form other state = 0) ↔ state = 0) := by
  have physical := canonicalForm_noGhost D H leftGram rightGram beta level critical shell
    chargeNonzero lorentzian
  refine ⟨?_, ?_, ?_⟩
  · intro state nonzero
    exact physical.1 (identification state) (by simpa using nonzero)
  · intro state
    constructor
    · intro radical
      apply (identification).injective
      rw [map_zero]
      apply (physical.2.1 (identification state)).mp
      intro other
      obtain ⟨preimage, rfl⟩ := (identification).surjective other
      exact radical preimage
    · rintro rfl
      intro other
      simp
  · intro state
    constructor
    · intro radical
      apply (identification).injective
      rw [map_zero]
      apply (physical.2.2 (identification state)).mp
      intro other
      obtain ⟨preimage, rfl⟩ := (identification).surjective other
      exact radical preimage
    · rintro rfl
      intro other
      simp

theorem absoluteCanonicalForm_radicals_bot :
    LinearMap.ker form = ⊥ ∧
      (⨅ other : degreeCohomology 1, LinearMap.ker (form other)) = ⊥ := by
  have noGhost := absoluteCanonicalForm_noGhost D H leftGram rightGram beta level critical
    shell chargeNonzero lorentzian
  constructor
  · apply (Submodule.eq_bot_iff _).mpr
    intro state member
    apply (noGhost.2.1 state).mp
    intro other
    exact LinearMap.congr_fun (show form state = 0 from member) other
  · apply (Submodule.eq_bot_iff _).mpr
    intro state member
    apply (noGhost.2.2 state).mp
    intro other
    exact (Submodule.mem_iInf _).mp member other

include leftGram rightGram critical chargeNonzero lorentzian in
theorem original_other_ghost_cycle_boundary (degree : ℤ) (notOne : degree ≠ 1)
    (notTwo : degree ≠ 2) (state : originalEnergySector D H beta level)
    (cycle : Q D H state.val = 0) (homogeneous : state.val ∈ ghostPart D degree) :
    ∃ preimage : originalEnergySector D H beta level,
      preimage.val ∈ ghostPart D (degree - 1) ∧ Q D H preimage.val = state.val := by
  let native := constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian
  let choice := admissibleOfNative D H beta native
  exact other_ghost_cycle_boundary D H choice.frame choice.inverse leftGram rightGram
    choice.leftFrame choice.rightFrame beta choice.direction choice.xAxis choice.yAxis level
    critical choice.null choice.nonzero choice.distinct choice.xRow choice.yRow
    choice.xDual choice.yDual degree notOne notTwo state cycle homogeneous

include chargeNonzero lorentzian in
theorem original_other_ghost_cohomology_zero (degree : ℤ) (notOne : degree ≠ 1)
    (notTwo : degree ≠ 2) (quotient : degreeCohomology degree) : quotient = 0 := by
  obtain ⟨state, rfl⟩ := (degreeBoundaries degree).mkQ_surjective quotient
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  obtain ⟨preimage, homogeneous, equation⟩ := original_other_ghost_cycle_boundary D H
    leftGram rightGram beta level critical chargeNonzero lorentzian degree notOne notTwo
    ⟨state.val, state.property.1.1⟩ state.property.1.2 state.property.2
  exact (ghostBoundary_iff D H leftGram rightGram critical (originalEnergySector D H beta level)
    stable degree state).mpr ⟨⟨preimage.val, preimage.property, homogeneous⟩, equation⟩

#print axioms original_absolute_ghost_one_representative
#print axioms absolute_degree_one_image
#print axioms absolutePhysicalEquiv
#print axioms absoluteCanonicalForm_noGhost
#print axioms absoluteCanonicalForm_radicals_bot
#print axioms original_other_ghost_cohomology_zero

end
end D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost
