import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open FourthSegmentStoppedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Control
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := (_ : AcquiredNativeState) × ℕ
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Visible
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (c d : AcquiredNativeState) (ω : Stream) (n : ℕ),
    c.source.finiteFields.control = d.source.finiteFields.control →
    R.readout () ⟨c,n⟩ ω = visible (nativeDrive d ω n)

def actual : Realization signature :=
  realize signature (fun _ p ω => visible (nativeDrive p.1 ω p.2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law initial initial (fun _ => 0) 0 rfl
  simpa [rejected,realize,visible,nativeDrive] using h

def record : Registration arena (type_of% (@drive_control)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨drive_control,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨initial,1⟩,(fun _ => 0),(fun _ => 1),?_⟩
    intro h
    have hletters := congrArg (fun v : Visible => v.map Prod.fst) h
    simpa [actual,realize,visible,nativeDrive,nextNative,nextOperation,initial,
      nativeStep,nativeRead,finiteRead] using hletters

def driveControlRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@drive_control)
    (type_of% (realize signature
      (fun _ p ω => visible (nativeDrive p.1 ω p.2)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.driveControl,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.record,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p ω => visible (nativeDrive p.1 ω p.2)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl,
    definition := none,
    coordinates := #[0,3],
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg","fn","arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl
