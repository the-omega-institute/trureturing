/- GID: D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none -/

import D5.S3.VertexAlgebra.RelativePairing.TensorRelativeForm
import D5.S3.VertexAlgebra.OriginalQRelativeAmbientPreimage
import D5.S3.VertexAlgebra.OriginalIntegralGhostCompatibilityTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.OriginalQPhysicalPairing

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  LatticeBcGhostHermitianForm LatticeBcGhostHermitianAdjoint LatticeBcGhostHermitianRelative
  LatticeBcGhostNeutralCohomology OriginalBrstReassembly OriginalQQuartetSource
open scoped TensorProduct

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (beta : Charge D) (level : ℤ)

def physicalCycles : Submodule ℂ (OriginalCycles D H) :=
  ((originalEnergySector D H beta level).comap (OriginalCycles D H).subtype ⊓
    LinearMap.ker ((B D 0).comp (OriginalCycles D H).subtype)) ⊓
      (ghostPart D 1).comap (OriginalCycles D H).subtype

def physicalState : physicalCycles D H beta level →ₗ[ℂ] State D :=
  (OriginalCycles D H).subtype.comp (physicalCycles D H beta level).subtype

def physicalBoundaries : Submodule ℂ (physicalCycles D H beta level) :=
  (OriginalBoundaries D H).comap (physicalCycles D H beta level).subtype

abbrev PhysicalCohomology : Type :=
  (↥(physicalCycles D H beta level)) ⧸ (physicalBoundaries D H beta level)

def physicalClassMap : physicalCycles D H beta level →ₗ[ℂ] OriginalCohomology D H :=
  (OriginalBoundaries D H).mkQ.comp (physicalCycles D H beta level).subtype

private theorem physicalClassMap_kernel :
    LinearMap.ker (physicalClassMap D H beta level) = physicalBoundaries D H beta level := by
  ext state
  change (OriginalBoundaries D H).mkQ state.val = 0 ↔ state.val ∈ OriginalBoundaries D H
  exact Submodule.Quotient.mk_eq_zero (OriginalBoundaries D H)

def inclusion : PhysicalCohomology D H beta level →ₗ[ℂ] OriginalCohomology D H :=
  (physicalBoundaries D H beta level).liftQ (physicalClassMap D H beta level)
    (by rw [physicalClassMap_kernel])

theorem inclusion_injective : Function.Injective (inclusion D H beta level) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (by rw [physicalClassMap_kernel])

theorem inclusion_mk (state : physicalCycles D H beta level) :
    inclusion D H beta level ((physicalBoundaries D H beta level).mkQ state) =
      (OriginalBoundaries D H).mkQ state.val := rfl

def physicalImage : Submodule ℂ (OriginalCohomology D H) :=
  LinearMap.range (inclusion D H beta level)

def imageEquiv : PhysicalCohomology D H beta level ≃ₗ[ℂ] physicalImage D H beta level :=
  LinearEquiv.ofInjective (inclusion D H beta level) (inclusion_injective D H beta level)

theorem physicalImage_eq : physicalImage D H beta level =
    (physicalCycles D H beta level).map (OriginalBoundaries D H).mkQ := by
  ext state
  constructor
  · rintro ⟨quotient, equality⟩
    induction quotient using Submodule.Quotient.induction_on with
    | _ representative =>
      exact ⟨representative.val, representative.property, equality⟩
  · rintro ⟨representative, member, equality⟩
    exact ⟨(physicalBoundaries D H beta level).mkQ ⟨representative, member⟩, equality⟩

def imageRepresentative : physicalCycles D H beta level →ₗ[ℂ] physicalImage D H beta level :=
  (physicalClassMap D H beta level).codRestrict (physicalImage D H beta level) (by
    intro state
    rw [physicalImage_eq]
    exact ⟨state.val, state.property, rfl⟩)

private theorem imageEquiv_mk (state : physicalCycles D H beta level) :
    (imageEquiv D H beta level) ((physicalBoundaries D H beta level).mkQ state) =
      imageRepresentative D H beta level state := by
  apply Subtype.ext
  exact inclusion_mk D H beta level state

def insertedForm : physicalCycles D H beta level →ₗ⋆[ℂ]
    physicalCycles D H beta level →ₗ[ℂ] ℂ where
  toFun left := (tensorForm D (physicalState D H beta level left)).comp
    ((C D 0).comp (physicalState D H beta level))
  map_add' := by
    intro first second
    ext right
    simp [physicalState]
  map_smul' := by
    intro scalar state
    ext right
    simp [physicalState, LinearMap.map_smulₛₗ]

variable (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
  (leftFrame : inverse * frame = 1) (rightFrame : frame * inverse = 1)
  (nullDirection : Fin D.rank → ℂ) (xAxis yAxis : Fin D.rank)
  (critical : D.rank = 26) (null : gramPair D nullDirection nullDirection = 0)
  (nonzero : chosenP D beta nullDirection ≠ 0) (distinct : xAxis ≠ yAxis)
  (xRow : frame xAxis = nullDirection)
  (yRow : frame yAxis = adaptedPartner D beta nullDirection)
  (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
  (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
  (shell : chosenH D beta + (level : ℂ) - 1 = 0)

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
theorem representative_independent
    (first second third fourth : originalEnergySector D H beta level)
    (firstCycle : Q D H first.val = 0) (secondCycle : Q D H second.val = 0)
    (thirdCycle : Q D H third.val = 0) (fourthCycle : Q D H fourth.val = 0)
    (firstRelative : B D 0 first.val = 0) (secondRelative : B D 0 second.val = 0)
    (thirdRelative : B D 0 third.val = 0) (fourthRelative : B D 0 fourth.val = 0)
    (firstDegree : first.val ∈ ghostPart D 1) (secondDegree : second.val ∈ ghostPart D 1)
    (thirdDegree : third.val ∈ ghostPart D 1) (fourthDegree : fourth.val ∈ ghostPart D 1)
    (leftEquality : (OriginalBoundaries D H).mkQ (⟨first.val, firstCycle⟩ : OriginalCycles D H) =
      (OriginalBoundaries D H).mkQ (⟨second.val, secondCycle⟩ : OriginalCycles D H))
    (rightEquality : (OriginalBoundaries D H).mkQ (⟨third.val, thirdCycle⟩ : OriginalCycles D H) =
      (OriginalBoundaries D H).mkQ (⟨fourth.val, fourthCycle⟩ : OriginalCycles D H)) :
    F D first.val (C D 0 third.val) = F D second.val (C D 0 fourth.val) := by
  obtain ⟨leftPreimage, leftRelative, _leftDegree, leftImage⟩ :=
    (literal_physical_equality_iff_relative_preimage D H frame inverse leftGram rightGram
      leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
      xRow yRow xDual yDual shell first second firstCycle secondCycle firstRelative secondRelative
      firstDegree secondDegree).mp leftEquality
  obtain ⟨rightPreimage, rightRelative, _rightDegree, rightImage⟩ :=
    (literal_physical_equality_iff_relative_preimage D H frame inverse leftGram rightGram
      leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
      xRow yRow xDual yDual shell third fourth thirdCycle fourthCycle thirdRelative fourthRelative
      thirdDegree fourthDegree).mp rightEquality
  have leftZero := (boundary_pairing_vanishes D H leftGram rightGram leftPreimage.val third.val
    leftRelative thirdRelative thirdCycle).1
  have rightZero := (boundary_pairing_vanishes D H leftGram rightGram rightPreimage.val second.val
    rightRelative secondRelative secondCycle).2
  have leftDifference : F D first.val (C D 0 third.val) -
      F D second.val (C D 0 third.val) = 0 := by
    simpa only [leftImage, F, map_sub, LinearMap.sub_apply] using leftZero
  have rightDifference : F D second.val (C D 0 third.val) -
      F D second.val (C D 0 fourth.val) = 0 := by
    simpa only [rightImage, map_sub, F] using rightZero
  exact (sub_eq_zero.mp leftDifference).trans (sub_eq_zero.mp rightDifference)

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
theorem physical_boundary_vanishing (boundary cycle : physicalCycles D H beta level)
    (member : boundary ∈ physicalBoundaries D H beta level) :
    insertedForm D H beta level boundary cycle = 0 ∧
      insertedForm D H beta level cycle boundary = 0 := by
  let sectorBoundary : originalEnergySector D H beta level :=
    ⟨physicalState D H beta level boundary, boundary.property.1.1⟩
  have boundaryRelative : B D 0 sectorBoundary.val = 0 := boundary.property.1.2
  have boundaryCycle : Q D H sectorBoundary.val = 0 := boundary.val.property
  have boundaryDegree : sectorBoundary.val ∈ ghostPart D 1 := boundary.property.2
  have ambientBoundary : ∃ ambient : State D, Q D H ambient = sectorBoundary.val := member
  have repaired := relative_ambient_boundary_homotopy_preimage D H frame inverse
    leftGram rightGram leftFrame rightFrame beta nullDirection xAxis yAxis level
    critical null nonzero distinct xRow yRow xDual yDual shell 1 sectorBoundary
    boundaryRelative boundaryCycle boundaryDegree ambientBoundary
  have vanishing := boundary_pairing_vanishes D H leftGram rightGram
    (energyTransferHomotopy D H frame inverse leftGram rightGram leftFrame rightFrame beta
      nullDirection xAxis yAxis level sectorBoundary).val
    (physicalState D H beta level cycle) repaired.1 cycle.property.1.2 cycle.val.property
  change F D (physicalState D H beta level boundary)
      (C D 0 (physicalState D H beta level cycle)) = 0 ∧
    F D (physicalState D H beta level cycle)
      (C D 0 (physicalState D H beta level boundary)) = 0
  simpa only [repaired.2.2] using vanishing

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
def quotientForm : PhysicalCohomology D H beta level →ₗ⋆[ℂ]
    PhysicalCohomology D H beta level →ₗ[ℂ] ℂ :=
  (physicalBoundaries D H beta level).liftQ {
    toFun := fun left => (physicalBoundaries D H beta level).liftQ
      (insertedForm D H beta level left) (by
        intro boundary member
        exact (physical_boundary_vanishing D H beta level frame inverse leftGram rightGram
          leftFrame rightFrame nullDirection xAxis yAxis critical null nonzero distinct
          xRow yRow xDual yDual shell boundary left member).2)
    map_add' := by
      intro first second
      apply LinearMap.ext
      intro quotient
      induction quotient using Submodule.Quotient.induction_on with
      | _ representative => simp [insertedForm]
    map_smul' := by
      intro scalar left
      apply LinearMap.ext
      intro quotient
      induction quotient using Submodule.Quotient.induction_on with
      | _ representative => simp [insertedForm, LinearMap.map_smulₛₗ] }
    (by
      intro boundary member
      apply LinearMap.ext
      intro quotient
      induction quotient using Submodule.Quotient.induction_on with
      | _ representative =>
        exact (physical_boundary_vanishing D H beta level frame inverse leftGram rightGram
          leftFrame rightFrame nullDirection xAxis yAxis critical null nonzero distinct
          xRow yRow xDual yDual shell boundary representative member).1)

local notation "descended" => quotientForm D H beta level frame inverse leftGram rightGram
  leftFrame rightFrame nullDirection xAxis yAxis critical null nonzero distinct
  xRow yRow xDual yDual shell

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
theorem quotientForm_mk (left right : physicalCycles D H beta level) :
    descended ((physicalBoundaries D H beta level).mkQ left)
      ((physicalBoundaries D H beta level).mkQ right) =
    F D (physicalState D H beta level left) (C D 0 (physicalState D H beta level right)) := rfl

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
def imageForm : physicalImage D H beta level →ₗ⋆[ℂ]
    physicalImage D H beta level →ₗ[ℂ] ℂ where
  toFun left := (descended ((imageEquiv D H beta level).symm left)).comp
    (imageEquiv D H beta level).symm.toLinearMap
  map_add' := by intro first second; ext right; simp
  map_smul' := by intro scalar left; ext right; simp [LinearMap.map_smulₛₗ]

local notation "literalForm" => imageForm D H beta level frame inverse leftGram rightGram
  leftFrame rightFrame nullDirection xAxis yAxis critical null nonzero distinct
  xRow yRow xDual yDual shell

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
theorem imageForm_recovery (left right : physicalCycles D H beta level) :
    literalForm (imageRepresentative D H beta level left)
      (imageRepresentative D H beta level right) =
    F D (physicalState D H beta level left) (C D 0 (physicalState D H beta level right)) := by
  rw [← imageEquiv_mk, ← imageEquiv_mk]
  change descended
    ((imageEquiv D H beta level).symm
      ((imageEquiv D H beta level) ((physicalBoundaries D H beta level).mkQ left)))
    ((imageEquiv D H beta level).symm
      ((imageEquiv D H beta level) ((physicalBoundaries D H beta level).mkQ right))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact quotientForm_mk D H beta level frame inverse leftGram rightGram leftFrame rightFrame
    nullDirection xAxis yAxis critical null nonzero distinct xRow yRow xDual yDual shell left right

private theorem Pi_degree_one (state : State D) (member : state ∈ ghostPart D 1) :
    Pi D state = -state := by
  let odd : Module.End ℂ (State D) := TensorProduct.map LinearMap.id
    (BcGhostSuperGenerators.parityPart 1)
  have projection : odd state = state := ghostPart_original_parity D 1 state member
  have operator : (Pi D).comp odd = -odd := by
    apply TensorProduct.ext'
    intro matter ghost
    have ghostParity := BcGhostBpZForm.Pi_homogeneous 1
      (BcGhostSuperGenerators.parityPart 1 ghost)
      (BcGhostSuperGenerators.parityPart_mem 1 ghost)
    simp [odd, Pi, ghostParity, TensorProduct.tmul_neg]
  have applied := LinearMap.congr_fun operator state
  simpa only [LinearMap.comp_apply, LinearMap.neg_apply, projection] using applied

private theorem insertedForm_hermitian (left right : physicalCycles D H beta level) :
    insertedForm D H beta level left right = star (insertedForm D H beta level right left) := by
  have parity := Pi_degree_one D (physicalState D H beta level left) left.property.2
  have adjoint := LatticeBcGhostHermitianAdjoint.F_C D 0
    (physicalState D H beta level left) (physicalState D H beta level right)
  rw [parity, neg_zero] at adjoint
  have identity : F D (C D 0 (physicalState D H beta level left))
      (physicalState D H beta level right) =
      F D (physicalState D H beta level left) (C D 0 (physicalState D H beta level right)) := by
    simpa [F] using adjoint
  change F D (physicalState D H beta level left) (C D 0 (physicalState D H beta level right)) = _
  rw [← identity, F_hermitian]
  rfl

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
theorem quotientForm_hermitian (left right : PhysicalCohomology D H beta level) :
    descended left right = star (descended right left) := by
  induction left using Submodule.Quotient.induction_on with
  | _ first =>
    induction right using Submodule.Quotient.induction_on with
    | _ second => exact insertedForm_hermitian D H beta level first second

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
theorem imageForm_hermitian (left right : physicalImage D H beta level) :
    literalForm left right = star (literalForm right left) :=
  quotientForm_hermitian D H beta level frame inverse leftGram rightGram leftFrame rightFrame
    nullDirection xAxis yAxis critical null nonzero distinct xRow yRow xDual yDual shell
    ((imageEquiv D H beta level).symm left) ((imageEquiv D H beta level).symm right)

#print axioms representative_independent
#print axioms physical_boundary_vanishing
#print axioms inclusion_injective
#print axioms quotientForm_mk
#print axioms imageForm_recovery
#print axioms imageForm_hermitian

end

end D5.S3.VertexAlgebra.OriginalQPhysicalPairing
