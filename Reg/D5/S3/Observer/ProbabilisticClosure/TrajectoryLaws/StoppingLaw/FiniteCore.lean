import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := List ℤ
  State _ := ℤ → Bool
  Role := Fin 5
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Execution
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun i _ _ => if i = 4 then ⟨none, [(0, false), (0, false)]⟩ else ⟨none, []⟩)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (ts : List ℤ) (x : ℤ → Bool),
    (R.readout 0 ts x).output = some (.a false) ∧
      (R.readout 1 ts x).paid = ts.length ∨
    (R.readout 2 ts x).output = some (.a true) ∧
      1 ≤ (R.readout 3 ts x).paid ∧ (R.readout 4 ts x).paid ≤ ts.length

private theorem actual_law : arena.Law actual := by
  exact ReadTree.stopComb_outcomes

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h [] (fun _ => false)
  simpa [rejected, realize] using hbad

def evidence : Registration arena (type_of% (@ReadTree.stopComb_outcomes)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      let bad : Realization signature := realize signature
        (fun j ts x => if j = i then rejected.readout j ts x else actual.readout j ts x)
        (fun e => nomatch e)
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro j hj
        funext ts x
        simp [bad, realize, hj]
      · intro h
        fin_cases i
        · have hx := h [0] (fun _ => false)
          simp [bad, actual, rejected, realize, ReadTree.stopComb, ReadTree.run,
            Execution.prepend, Execution.paid] at hx
        · have hx := h [0] (fun _ => false)
          simp [bad, actual, rejected, realize, ReadTree.stopComb, ReadTree.run,
            Execution.prepend, Execution.paid] at hx
        · have hx := h [0] (fun _ => true)
          simp [bad, actual, rejected, realize, ReadTree.stopComb, ReadTree.run,
            Execution.prepend, Execution.paid] at hx
        · have hx := h [0] (fun _ => true)
          simp [bad, actual, rejected, realize, ReadTree.stopComb, ReadTree.run,
            Execution.prepend, Execution.paid] at hx
        · have hx := h [0] (fun _ => true)
          simp [bad, actual, rejected, realize, ReadTree.stopComb, ReadTree.run,
            Execution.prepend, Execution.paid] at hx
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    refine ⟨[0], (fun _ => false), (fun _ => true), ?_⟩
    intro h
    have ho := congrArg Execution.output h
    simp [actual, realize, ReadTree.stopComb, ReadTree.run, Execution.prepend] at ho

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.stopComb_outcomes)
    (type_of% (realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0],
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
        stateBinder := 1, functionOperand := false,
        stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "arg", "fn", "arg", "arg"],
        stateBinder := 1, functionOperand := false,
        stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "arg"],
        stateBinder := 1, functionOperand := false,
        stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "arg", "arg", "fn", "arg", "arg", "arg"],
        stateBinder := 1, functionOperand := false,
        stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "arg", "arg", "arg", "fn", "arg", "arg"],
        stateBinder := 1, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
