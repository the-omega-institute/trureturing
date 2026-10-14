import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostRotatedForm

import Reg.Support.DependentFamily

set_option autoImplicit false

#check _root_.D5.S3.VertexAlgebra.BcGhostRotatedForm.rotation_support
#check _root_.D5.S3.VertexAlgebra.BcGhostRotatedForm.Hplus_degree_selection
#check _root_.D5.S3.VertexAlgebra.BcGhostRotatedForm.Hplus_c0_degree_selection
#check _root_.D5.S3.VertexAlgebra.BcGhostRotatedForm.Hplus_j_k

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostBpZForm
open _root_.D5.S3.VertexAlgebra.BcGhostEnergyRotation
open _root_.D5.S3.VertexAlgebra.BcGhostRotatedForm

namespace Reg.D5.S3.VertexAlgebra.BcGhostRotatedForm

noncomputable section

abbrev signature : Signature where
  Params := _root_.D5.S3.VertexAlgebra.BcGhostBpZForm.GhostFock
  State _ := _root_.D5.S3.VertexAlgebra.BcGhostBpZForm.GhostFock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ left right => BPZ (rotation left) right) (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ left right => BPZ (rotation left) right + 1) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law realization := ∀ left right, realization.readout () left right = BPZ left (rotation right)

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have impossible := law 0 0
  change BPZ (rotation 0) 0 + 1 = BPZ 0 (rotation 0) at impossible
  simp [BPZ] at impossible

def sourceWitness : Registration arena
    (∀ left right, BPZ (rotation left) right = BPZ left (rotation right)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rotation_transpose, rejected, rejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedFails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨basis ∅, basis (chi ∅), 0, ?_⟩
    change BPZ (rotation (basis ∅)) (basis (chi ∅)) ≠ BPZ (rotation (basis ∅)) 0
    rw [show rotation (basis ∅) = basis ∅ by
      simp [basis, rotation_single, phase, _root_.D5.S3.VertexAlgebra.BcGhostLZeroSpectrum.energy]]
    rw [BPZ_kernel, if_pos rfl]
    simpa [BPZ] using eps_nonzero ∅

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.BcGhostRotatedForm.rotation_transpose)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostRotatedForm.rotation_transpose.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostRotatedForm.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ left right => BPZ (rotation left) right) (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostRotatedForm
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.VertexAlgebra.BcGhostRotatedForm
