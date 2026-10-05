import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Budget.DyadicDeadlineStaircase
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase

open _root_.D5.S3.Observer.Budget.DyadicDeadlineStaircase
open _root_.D5.S3.Observer.Budget.DyadicPrefixDelayRange
open _root_.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev timingSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def timingActual : Realization timingSignature :=
  realize timingSignature (fun _ _ d => earliestTime d (2 ^ d - 1))
    (fun e => nomatch e)

def timingRejected : Realization timingSignature :=
  realize timingSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev timingArena : Arena where
  signature := timingSignature
  Law R := ∀ d : Nat,
    let P := 2 ^ (d + 1)
    let W := sharpWait (d + 1)
    R.readout () () d + P = W + P ∧
    (∀ k : Nat, k < d →
      earliestTime d (2 ^ d - 1 - 2 ^ k) + P = W + 2 ^ (k + 1)) ∧
    (∀ t : Nat, t < 2 ^ d → t.bitIndices.length + 2 ≤ d →
      earliestTime d t + P ≤ W) ∧
    (∀ t : Nat, t < 2 ^ d →
      t.bitIndices.length ≤ d ∧
      (t.bitIndices.length = d → t = 2 ^ d - 1) ∧
      (t.bitIndices.length + 1 = d →
        ∃ k : Nat, k < d ∧ t + 2 ^ k = 2 ^ d - 1))

theorem timingRejected_law : ¬ timingArena.Law timingRejected := by
  intro h
  have hh := (h 0).1
  norm_num [timingRejected, realize, sharpWait] at hh

def timingRegistration : Registration timingArena (timingArena.Law timingActual) where
  actual := timingActual
  bridge := Iff.rfl
  variation := ⟨exceptional_prefix_timing, timingRejected, timingRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨timingRejected, ?_, rfl, timingRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [timingActual, realize, earliestTime, Nat.bitIndices]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Budget.DyadicDeadlineStaircase.exceptional_prefix_timing) (type_of% (realize.{0, 0, 0, 0, 0} timingSignature
    (fun _ _ d => earliestTime d (2 ^ d - 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Budget") "DyadicDeadlineStaircase") "exceptional_prefix_timing") "Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase/Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(timingArena)⟩,
  objectArena := .source ⟨(timingArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (timingArena) ⟨(timingRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} timingSignature
    (fun _ _ d => earliestTime d (2 ^ d - 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Budget.DyadicDeadlineStaircase, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms timingRegistration

end Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase
