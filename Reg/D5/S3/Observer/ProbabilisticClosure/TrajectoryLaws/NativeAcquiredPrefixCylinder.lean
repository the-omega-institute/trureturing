import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open FourthSegmentStoppedLaw (Stream Prefix readPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev cylinderSignature : Signature where
  Params := List Operation
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (List Operation × AcquiredNativeState × ℕ)
  Anchor := Empty
  finiteAnchor := inferInstance

def cylinderArena : Arena where
  signature := cylinderSignature
  Law R := ∀ (h : List Operation) (c : AcquiredNativeState) (ω : Stream) (k : ℕ),
    R.readout () h ω = some (h, c, k) ↔
      run h = some c ∧ Prefix ω (readLetters h) ∧ k = (readLetters h).length

def cylinderActual : Realization cylinderSignature :=
  realize cylinderSignature (fun _ h ω => nativeDrive initial ω h.length) (fun e => nomatch e)

def cylinderRejected : Realization cylinderSignature :=
  realize cylinderSignature (fun _ _ _ => none) (fun e => nomatch e)

private theorem cylinder_rejected_law : ¬ cylinderArena.Law cylinderRejected := by
  intro law
  have h := law [] initial (fun _ => 0) 0
  simpa [cylinderRejected, realize, run, execute, readLetters, Prefix, readPrefix] using h

def cylinderRecord : Registration cylinderArena (cylinderArena.Law cylinderActual) where
  actual := cylinderActual
  bridge := Iff.rfl
  variation := ⟨native_acquired_prefix_cylinder, cylinderRejected, cylinder_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cylinderRejected, ?_, rfl, cylinder_rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨[.read 0], (fun _ => 0), (fun _ => 1), ?_⟩
    cases i
    change nativeDrive initial (fun _ => 0) 1 ≠ nativeDrive initial (fun _ => 1) 1
    decide

def cylinderRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_acquired_prefix_cylinder)
    (type_of% (realize cylinderSignature
      (fun _ h ω => nativeDrive initial ω h.length) (fun e => nomatch e))) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder.cylinder,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder.cylinderRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨cylinderArena⟩,
  objectArena := .source ⟨cylinderArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source cylinderArena ⟨cylinderRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize cylinderSignature
    (fun _ h ω => nativeDrive initial ω h.length) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
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

def resumptionSignature : Signature where
  Params := (c : AcquiredNativeState) × ℕ
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (List Operation × AcquiredNativeState × ℕ)
  Anchor := Empty
  finiteAnchor := inferInstance

def resumptionArena : Arena where
  signature := resumptionSignature
  Law R := ∀ (h : List Operation) (c : AcquiredNativeState) (ω : Stream) (k : ℕ),
    nativeDrive initial ω h.length = some (h, c, k) → ∀ n : ℕ,
      k = (readLetters h).length ∧
      nativeDrive initial ω (h.length + n) =
        (R.readout () ⟨c, n⟩ (rawTail ω k)).map (fun r =>
          (h ++ r.1, r.2.1, k + r.2.2)) ∧
      ∃ nf : PrefixForm, render nf = h ∧ c = reconstruct nf ∧ PrefixFacts nf c

def resumptionActual : Realization resumptionSignature :=
  realize resumptionSignature (fun _ p ω => nativeDrive p.1 ω p.2) (fun e => nomatch e)

def resumptionRejected : Realization resumptionSignature :=
  realize resumptionSignature (fun _ _ _ => none) (fun e => nomatch e)

private theorem resumption_rejected_law : ¬ resumptionArena.Law resumptionRejected := by
  intro law
  have h := (law [] initial (fun _ => 0) 0 rfl 0).2.1
  simpa [resumptionRejected, realize, nativeDrive] using h

def resumptionRecord : Registration resumptionArena (resumptionArena.Law resumptionActual) where
  actual := resumptionActual
  bridge := Iff.rfl
  variation := ⟨native_acquired_prefix_resumption, resumptionRejected, resumption_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨resumptionRejected, ?_, rfl, resumption_rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨initial, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    cases i
    change nativeDrive initial (fun _ => 0) 1 ≠ nativeDrive initial (fun _ => 1) 1
    decide

def resumptionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_acquired_prefix_resumption)
    (type_of% (realize resumptionSignature
      (fun _ p ω => nativeDrive p.1 ω p.2) (fun e => nomatch e))) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder.resumption,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder.resumptionRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨resumptionArena⟩,
  objectArena := .source ⟨resumptionArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source resumptionArena ⟨resumptionRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize resumptionSignature
    (fun _ p ω => nativeDrive p.1 ω p.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder,
    definition := none,
    coordinates := #[1, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder
