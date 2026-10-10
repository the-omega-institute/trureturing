import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap

open _root_.D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace StaticAudit

@[reducible] def signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (min p.2 p.1 + 2)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => staticEncode p.1 p.2 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => ⟨min p.2 p.1 + 1, by omega⟩) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m H : ℕ) (ε : ℝ), 0 ≤ ε → ε < 1 / 2 →
    (StaticCorrect m H ε (R.readout () ⟨m, H⟩) (staticDecode m H) ∧
      IsLeast (staticSizes m H ε) (min H m + 2)) ∧
    (UpdaterCorrect m ε (machineEncode m) (machineUpdate m) (machineReadout m) ∧
      IsLeast (updaterSizes m ε) (m + 2))

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := (law 0 0 0 (by norm_num) (by norm_num)).1.1 0 0 (by omega)
  norm_num [rejected, realize, staticDecode, pulse] at impossible

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨delayed_pulse_memory_gap, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
    intro h
    have := congrArg Fin.val h
    norm_num [actual, realize, staticEncode] at this

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap.delayed_pulse_memory_gap) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p n => staticEncode p.1 p.2 n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "Prediction") "DelayedPulseMemoryGap") "delayed_pulse_memory_gap") "Reg.D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap/Reg.D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap.StaticAudit.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap.StaticAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p n => staticEncode p.1 p.2 n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end StaticAudit

end Reg.D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap
