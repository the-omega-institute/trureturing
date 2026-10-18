import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Bool × ℤ
  State _ := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => visible p.1 S (2 * p.2 + p.1.toInt)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (φ : Bool) (S : Spins) (e : ℤ),
    R.readout () (φ, e) S = Bool.xor (S e) (S (e + 1))

private theorem actual_law : arena.Law actual := by
  exact active_visible

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h false (fun _ => false) 0
  simpa [rejected, realize] using hbad

def evidence : Registration arena (type_of% (@active_visible)) where
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
    refine ⟨(false, 0), (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    simp [actual, realize, visible]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@active_visible)
    (type_of% (realize signature (fun _ p S => visible p.1 S (2 * p.2 + p.1.toInt)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p S => visible p.1 S (2 * p.2 + p.1.toInt)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
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

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
