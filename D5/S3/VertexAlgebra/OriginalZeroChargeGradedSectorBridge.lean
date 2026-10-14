/- GID: D5/S3/VertexAlgebra/OriginalZeroChargeGradedSectorBridge
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identification of the native exceptional complex with the literal original sector quotient. -/

import D5.S3.VertexAlgebra.OriginalZeroChargeBrstGrading
import D5.S3.VertexAlgebra.OriginalIntegralGhostCompatibilityTransient
import D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.OriginalZeroChargeGradedSectorBridge

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQQuartetSource RelativePairing.AbsolutePhysicalNoGhost
open scoped TensorProduct

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)

local notation "nativeSector" => OriginalZeroChargeEnergyBasis.sector D
local notation "nativeCycles" => OriginalZeroChargeBrstComplex.cycles D
local notation "nativeBoundary" =>
  Submodule.comap (Submodule.subtype (OriginalZeroChargeBrstComplex.cycles D))
    (OriginalZeroChargeBrstComplex.boundaries D)
local notation "originalSector" => originalEnergySector D H 0 1
local notation "stable" => energyStable D H leftGram rightGram 0 1
local notation "originalCycles" => OriginalBrstReassembly.cycles D H originalSector

private theorem native_charge_coeff (state : State D)
    (label : OriginalZeroChargeEnergyBasis.FullIndex D) :
    (OriginalZeroChargeEnergyBasis.fullBasis D).repr (chargeProjection D 0 state) label =
      if label.1.1 = 0 then (OriginalZeroChargeEnergyBasis.fullBasis D).repr state label else 0 := by
  classical
  let coordinate := (Finsupp.lapply label).comp
    (OriginalZeroChargeEnergyBasis.fullBasis D).repr.toLinearMap
  have diagonal : coordinate.comp (chargeProjection D 0) =
      (if label.1.1 = 0 then (1 : ℂ) else 0) • coordinate := by
    apply (OriginalZeroChargeEnergyBasis.fullBasis D).ext
    intro other
    have basisEquality : OriginalZeroChargeEnergyBasis.fullBasis D other =
        OriginalBrstReassembly.fullBasis D ((other.1.1, other.1.2), other.2) := by
      simp [OriginalZeroChargeEnergyBasis.fullBasis_apply,
        OriginalBrstReassembly.fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply]
    have chargeLaw := original_charge_projection_basis D 0
      ((other.1.1, other.1.2), other.2)
    rw [← basisEquality] at chargeLaw
    by_cases same : other = label
    · subst other
      by_cases neutral : label.1.1 = 0 <;> simp [coordinate, chargeLaw, neutral]
    · by_cases sourceZero : other.1.1 = 0 <;> by_cases targetZero : label.1.1 = 0 <;>
        simp [coordinate, chargeLaw, same, sourceZero, targetZero]
  have equality := LinearMap.congr_fun diagonal state
  by_cases neutral : label.1.1 = 0 <;> simpa [coordinate, neutral] using equality

private theorem native_charge_fixed (state : State D) :
    chargeProjection D 0 state = state ↔
      ∀ label : OriginalZeroChargeEnergyBasis.FullIndex D,
        label.1.1 ≠ 0 → (OriginalZeroChargeEnergyBasis.fullBasis D).repr state label = 0 := by
  constructor
  · intro fixed label different
    have equality := native_charge_coeff D state label
    rw [fixed, if_neg different] at equality
    exact equality
  · intro supported
    apply (OriginalZeroChargeEnergyBasis.fullBasis D).repr.injective
    ext label
    rw [native_charge_coeff]
    by_cases same : label.1.1 = 0
    · rw [if_pos same]
    · rw [if_neg same, supported label same]

include leftGram rightGram in
theorem sector_eq_original : nativeSector = originalSector := by
  ext state
  rw [OriginalZeroChargeEnergyBasis.mem_sector_iff D H leftGram rightGram]
  change ((∀ label : OriginalZeroChargeEnergyBasis.FullIndex D,
    label.1.1 ≠ 0 → (OriginalZeroChargeEnergyBasis.fullBasis D).repr state label = 0) ∧
    (M D H 0 + G D 0) state = 0) ↔
    chargeProjection D 0 state = state ∧
      (M D H 0 + G D 0) state = (chosenH D 0 + ((1 : ℤ) : ℂ) - 1) • state
  rw [native_charge_fixed]
  simp [chosenH, complexCharge, gramPair]

def sectorEquiv : nativeSector ≃ₗ[ℂ] originalSector :=
  LinearEquiv.ofEq _ _ (sector_eq_original D H leftGram rightGram)

def cycleEquiv : nativeCycles ≃ₗ[ℂ] originalCycles where
  toFun state := ⟨state.val.val,
    (sector_eq_original D H leftGram rightGram) ▸ state.val.property, by
      change Q D H state.val.val = 0
      rw [← OriginalZeroChargeBrstComplex.differential_native D H leftGram rightGram]
      exact congrArg Subtype.val state.property⟩
  invFun state := ⟨⟨state.val,
    (sector_eq_original D H leftGram rightGram).symm ▸ state.property.1⟩, by
      apply Subtype.ext
      exact (OriginalZeroChargeBrstComplex.differential_native D H leftGram rightGram _).trans
        state.property.2⟩
  left_inv state := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv state := by apply Subtype.ext; rfl
  map_add' first second := by apply Subtype.ext; rfl
  map_smul' scalar state := by apply Subtype.ext; rfl

variable (critical : D.rank = 26)

local notation "originalBoundary" =>
  OriginalBrstReassembly.boundaries D H leftGram rightGram critical originalSector stable
local notation "originalCohomology" =>
  OriginalBrstReassembly.Cohomology D H leftGram rightGram critical originalSector stable

theorem boundary_correspondence (state : nativeCycles) :
    cycleEquiv D H leftGram rightGram state ∈ originalBoundary ↔ state ∈ nativeBoundary := by
  rw [OriginalBrstReassembly.boundary_iff]
  change (∃ preimage : originalSector, Q D H preimage.val = state.val.val) ↔
    ∃ preimage : nativeSector, OriginalZeroChargeBrstComplex.differential D preimage = state.val
  constructor
  · rintro ⟨preimage, equation⟩
    refine ⟨(sectorEquiv D H leftGram rightGram).symm preimage, ?_⟩
    apply Subtype.ext
    exact (OriginalZeroChargeBrstComplex.differential_native D H leftGram rightGram _).trans
      equation
  · rintro ⟨preimage, equation⟩
    refine ⟨sectorEquiv D H leftGram rightGram preimage, ?_⟩
    simpa only [sectorEquiv, LinearEquiv.coe_ofEq_apply] using
      (OriginalZeroChargeBrstComplex.differential_native D H leftGram rightGram preimage).symm.trans
        (congrArg Subtype.val equation)

private theorem boundary_map :
    Submodule.map (cycleEquiv D H leftGram rightGram).toLinearMap nativeBoundary =
      originalBoundary := by
  ext state
  constructor
  · rintro ⟨native, member, rfl⟩
    exact (boundary_correspondence D H leftGram rightGram critical native).mpr member
  · intro member
    refine ⟨(cycleEquiv D H leftGram rightGram).symm state, ?_,
      (cycleEquiv D H leftGram rightGram).apply_symm_apply state⟩
    apply (boundary_correspondence D H leftGram rightGram critical _).mp
    simpa using member

def cohomologyEquiv : OriginalZeroChargeBrstComplex.Cohomology D ≃ₗ[ℂ] originalCohomology :=
  Submodule.Quotient.equiv nativeBoundary originalBoundary
    (cycleEquiv D H leftGram rightGram) (boundary_map D H leftGram rightGram critical)

theorem cohomologyEquiv_representative (state : nativeCycles) :
    cohomologyEquiv D H leftGram rightGram critical (Submodule.Quotient.mk state) =
      Submodule.Quotient.mk (cycleEquiv D H leftGram rightGram state) := rfl

theorem cohomologyEquiv_inverse_representative (state : originalCycles) :
    (cohomologyEquiv D H leftGram rightGram critical).symm (Submodule.Quotient.mk state) =
      Submodule.Quotient.mk ((cycleEquiv D H leftGram rightGram).symm state) := rfl

def numberStable : ∀ state, state ∈ originalSector →
    OriginalBrstReassembly.nativeJ D state ∈ originalSector := by
  intro state member
  have nativeMember : state ∈ nativeSector :=
    (sector_eq_original D H leftGram rightGram).symm ▸ member
  have numberMember :=
    (OriginalZeroChargeBrstGrading.sectorNumber D ⟨state, nativeMember⟩).property
  have transported := (SetLike.ext_iff.mp (sector_eq_original D H leftGram rightGram)
    (OriginalZeroChargeBrstGrading.sectorNumber D ⟨state, nativeMember⟩).val).mp numberMember
  simpa only [OriginalZeroChargeBrstGrading.sectorNumber_native] using transported

theorem cohomologyEquiv_number (state : OriginalZeroChargeBrstComplex.Cohomology D) :
    cohomologyEquiv D H leftGram rightGram critical
      (OriginalZeroChargeBrstGrading.cohomologyNumber D state) =
    OriginalBrstReassembly.cohomologyJ D H leftGram rightGram critical originalSector stable
      (numberStable D H leftGram rightGram)
      (cohomologyEquiv D H leftGram rightGram critical state) := by
  refine Submodule.Quotient.induction_on _ state ?_
  intro representative
  rw [OriginalZeroChargeBrstGrading.cohomologyNumber_native,
    cohomologyEquiv_representative, cohomologyEquiv_representative]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  exact OriginalZeroChargeBrstGrading.sectorNumber_native D representative.val

local notation "degreeCohomology" => OriginalBrstReassembly.ghostCohomology D H
  leftGram rightGram critical originalSector stable
local notation "degreeInclude" => OriginalBrstReassembly.ghostClassInclude D H
  leftGram rightGram critical originalSector stable
local notation "projected" => energyGhostProjected D H leftGram rightGram 0 1

private theorem ghost_include_injective (degree : ℤ) :
    Function.Injective (degreeInclude degree) := by
  intro first second equality
  have split := congrArg
    (OriginalBrstReassembly.ghostClassSplit D H leftGram rightGram critical
      originalSector stable projected) equality
  rw [OriginalBrstReassembly.ghostSplit_include,
    OriginalBrstReassembly.ghostSplit_include] at split
  have component := congrArg (fun pieces => pieces degree) split
  simpa [DirectSum.lof_eq_of, DirectSum.of_apply] using component

def ghostToNative (degree : ℤ) : degreeCohomology degree →ₗ[ℂ]
    OriginalZeroChargeBrstComplex.Cohomology D :=
  (cohomologyEquiv D H leftGram rightGram critical).symm.toLinearMap.comp
    (degreeInclude degree)

private theorem ghostToNative_homogeneous (degree : ℤ) (state : degreeCohomology degree) :
    ghostToNative D H leftGram rightGram critical degree state ∈
      OriginalZeroChargeBrstGrading.gradedCohomology D degree := by
  obtain ⟨representative, rfl⟩ :=
    (OriginalBrstReassembly.ghostBoundaries D H leftGram rightGram critical
      originalSector stable degree).mkQ_surjective state
  apply (OriginalZeroChargeBrstGrading.mem_graded_iff_number D degree _).mpr
  let native := (cycleEquiv D H leftGram rightGram).symm
    (OriginalBrstReassembly.ghostCycleInclude D H originalSector degree representative)
  change OriginalZeroChargeBrstGrading.cohomologyNumber D (Submodule.Quotient.mk native) =
    (degree : ℂ) • Submodule.Quotient.mk native
  rw [OriginalZeroChargeBrstGrading.cohomologyNumber_native]
  change (nativeBoundary).mkQ (OriginalZeroChargeBrstGrading.cycleNumber D native) =
    (degree : ℂ) • (nativeBoundary).mkQ native
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  change (OriginalZeroChargeBrstGrading.sectorNumber D native.val : State D) =
    (degree : ℂ) • native.val.val
  rw [OriginalZeroChargeBrstGrading.sectorNumber_native]
  exact (OriginalBrstReassembly.ghostPart_iff_number D degree representative.val).mp
    representative.property.2

def ghostToGraded (degree : ℤ) : degreeCohomology degree →ₗ[ℂ]
    OriginalZeroChargeBrstGrading.gradedCohomology D degree :=
  (ghostToNative D H leftGram rightGram critical degree).codRestrict _
    (ghostToNative_homogeneous D H leftGram rightGram critical degree)

private theorem ghostToGraded_bijective (degree : ℤ) :
    Function.Bijective (ghostToGraded D H leftGram rightGram critical degree) := by
  constructor
  · intro first second equality
    apply ghost_include_injective D H leftGram rightGram critical degree
    apply (cohomologyEquiv D H leftGram rightGram critical).symm.injective
    exact congrArg Subtype.val equality
  · intro state
    let native := OriginalZeroChargeBrstCohomology.representative D
      (OriginalZeroChargeBrstCohomology.cohomologyCoordinates D state.val)
    have laws := OriginalZeroChargeBrstGrading.homogeneous_representative D degree
      state.val state.property
    let representative : OriginalBrstReassembly.ghostCycles D H originalSector degree :=
      ⟨native.val.val, (cycleEquiv D H leftGram rightGram native).property,
        (OriginalBrstReassembly.ghostPart_iff_number D degree native.val.val).mpr laws.2.1⟩
    refine ⟨Submodule.Quotient.mk representative, ?_⟩
    apply Subtype.ext
    change (cohomologyEquiv D H leftGram rightGram critical).symm
      (Submodule.Quotient.mk (cycleEquiv D H leftGram rightGram native)) = state.val
    rw [← cohomologyEquiv_representative, LinearEquiv.symm_apply_apply]
    exact laws.1

def gradedEquiv (degree : ℤ) : OriginalZeroChargeBrstGrading.gradedCohomology D degree ≃ₗ[ℂ]
    degreeCohomology degree :=
  (LinearEquiv.ofBijective (ghostToGraded D H leftGram rightGram critical degree)
    (ghostToGraded_bijective D H leftGram rightGram critical degree)).symm

theorem gradedEquiv_inclusion (degree : ℤ)
    (state : OriginalZeroChargeBrstGrading.gradedCohomology D degree) :
    degreeInclude degree (gradedEquiv D H leftGram rightGram critical degree state) =
      cohomologyEquiv D H leftGram rightGram critical state.val := by
  have inverse := congrArg Subtype.val
    ((gradedEquiv D H leftGram rightGram critical degree).symm_apply_apply state)
  change (cohomologyEquiv D H leftGram rightGram critical).symm
    (degreeInclude degree (gradedEquiv D H leftGram rightGram critical degree state)) =
      state.val at inverse
  rw [← inverse, LinearEquiv.apply_symm_apply]

include leftGram rightGram critical in
theorem ghost_predecessor_preimage (degree : ℤ) (state : nativeCycles)
    (homogeneous : OriginalBrstReassembly.nativeJ D state.val.val =
      (degree : ℂ) • state.val.val) :
    state ∈ nativeBoundary ↔
      ∃ preimage : OriginalBrstReassembly.subspaceParts D
        (OriginalBrstReassembly.ghostTag D) originalSector (degree - 1),
        Q D H preimage.val = state.val.val := by
  constructor
  · intro member
    obtain ⟨preimage, equation, numberLaw, _⟩ :=
      OriginalZeroChargeBrstGrading.original_boundary_homogeneous_preimage
        D H leftGram rightGram degree state.val member homogeneous
    exact ⟨⟨preimage.val, (sectorEquiv D H leftGram rightGram preimage).property,
      (OriginalBrstReassembly.ghostPart_iff_number D (degree - 1) preimage.val).mpr numberLaw⟩,
        equation⟩
  · rintro ⟨preimage, equation⟩
    apply (boundary_correspondence D H leftGram rightGram critical state).mp
    exact (OriginalBrstReassembly.boundary_iff D H leftGram rightGram critical
      originalSector stable _).mpr ⟨⟨preimage.val, preimage.property.1⟩, equation⟩

theorem original_zero_graded_finrank (degree : ℤ) :
    Module.finrank ℂ (degreeCohomology degree) =
      if degree = 0 then 1 else if degree = 1 then D.rank else
        if degree = 2 then D.rank else if degree = 3 then 1 else 0 := by
  rw [← (gradedEquiv D H leftGram rightGram critical degree).finrank_eq]
  exact OriginalZeroChargeBrstGrading.graded_finrank D degree

theorem original_zero_finrank : Module.finrank ℂ originalCohomology = 2 * D.rank + 2 := by
  classical
  rw [← (cohomologyEquiv D H leftGram rightGram critical).finrank_eq,
    (OriginalZeroChargeBrstCohomology.cohomologyCoordinates D).finrank_eq,
    Module.finrank_finsupp_self,
    ← Fintype.card_congr (OriginalZeroChargeBrstGrading.survivorEquiv D)]
  simp [OriginalZeroChargeBrstGrading.SurvivorIndex, Nat.mul_comm, Nat.add_comm]

#print axioms sector_eq_original
#print axioms cohomologyEquiv
#print axioms gradedEquiv
#print axioms ghost_predecessor_preimage

end
end D5.S3.VertexAlgebra.OriginalZeroChargeGradedSectorBridge
