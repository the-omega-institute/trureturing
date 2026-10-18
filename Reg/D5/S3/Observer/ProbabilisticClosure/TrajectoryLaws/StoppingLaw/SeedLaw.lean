import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Bool
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j k => (witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : Bool) (k : ℕ), R.readout () j k =
    (List.range k).map (fun i : ℕ => j.toInt + 2 * ((i : ℤ) + 1) + 1)

private theorem actual_law : arena.Law actual := by
  exact witness_read_addresses

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h false 1
  simpa [rejected, realize] using hbad

def evidence : Registration arena (type_of% (@witness_read_addresses)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨false, 0, 1, ?_⟩
    simp [actual, realize, witnessEdges]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@witness_read_addresses)
    (type_of% (realize signature (fun _ j k => (witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ j k => (witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
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
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
