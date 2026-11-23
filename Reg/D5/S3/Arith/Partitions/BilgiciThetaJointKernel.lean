import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.Partitions.BilgiciThetaJointKernel

/-! The two tests distinguish equivariant classes outside the cubic multiplication range. -/

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Partitions.BilgiciThetaJointKernel

open _root_.D5.S3.Arith.Partitions.BilgiciThetaQuartic (S_Z)
open _root_.D5.S3.Arith.Partitions.BilgiciThetaStructural
open _root_.D5.S3.ConceptDynamics.InformationEscape

private def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => K × K
  Anchor := Empty
  finiteAnchor := inferInstance

private noncomputable def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ x => tests x) (fun e => nomatch e)

private noncomputable def arena : DependentFamily.Arena where
  signature := signature
  Law := fun readout =>
    ∀ {x : A}, x ∈ eigengrade 7 11 →
      ((show K × K from readout.readout () () x) = 0 ↔
        ∃ y ∈ eigengrade 4 9, q S_Z * y = x)

private abbrev sourceScope := type_of% (@joint_kernel_membership)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private noncomputable def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : K × K)) (fun e => nomatch e)

private theorem erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨y, hy, hmul⟩ := (h (x := q u) u_mem).mp rfl
  exact u_not_in_range ⟨⟨y, hy⟩, Subtype.ext hmul⟩

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@joint_kernel_membership), erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    rintro ⟨⟩
    refine ⟨(), q u, (0 : A), ?_⟩
    change tests (q u) ≠ tests 0
    rw [quotient_u_tests, map_zero]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@joint_kernel_membership) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Partitions.BilgiciThetaStructural.joint_kernel_membership.__information_unit
  realizationName := `Reg.D5.S3.Arith.Partitions.BilgiciThetaJointKernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ _ x => tests x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Partitions.BilgiciThetaJointKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Partitions.BilgiciThetaJointKernel
