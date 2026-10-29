import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.SixStateResidualSeparation
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.SixStateResidualSeparation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.SixStateResidualSeparation

abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R :=

    (∀ x x', residual kernel 1 x x' ↔ firstClass x = firstClass x') ∧
    (∀ x x', residual kernel 2 x x' ↔ stableClass x = stableClass x') ∧
    (∀ n, residual kernel (n+2) = residual kernel 2) ∧
    (∀ x x', (∀ n, residual kernel n x x') ↔ stableClass x = stableClass x') ∧
    (∀ w, R.readout false () w = profile w ∧ R.readout true () w = profile w) ∧
    (∀ n, StoppingEq kernel n 0 1) ∧
    residual kernel 1 0 1 ∧ ¬ residual kernel 2 0 1 ∧
    ¬ (∀ n, residual kernel n 0 1) ∧ StochasticQuotient ∧
    (∀ update, 1/2 ≤ updateFailure update 0)

abbrev actual : Realization signature :=
  realize signature (fun i _ w => if i then wordProb kernel 1 w else wordProb kernel 0 w)
    (fun e => nomatch e)

abbrev intervention (i : Bool) : Realization signature :=
  realize signature (fun j _ w => if j = i then 0 else actual.readout j () w)
    (fun e => nomatch e)

private theorem intervention_not_law (i : Bool) : ¬ arena.Law (intervention i) := by
  intro law
  have h := law.2.2.2.2.1 []
  cases i
  · have hh := h.1
    norm_num [intervention,realize,profile] at hh
  · have hh := h.2
    norm_num [intervention,realize,profile] at hh

def record : Registration arena (type_of% counterkernel_facts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨counterkernel_facts,intervention false,intervention_not_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_not_law i⟩
      intro j h
      funext M w
      simp [intervention,realize,h]
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), [], [true], ?_⟩
    have hp := counterkernel_facts.2.2.2.2.1
    cases i
    · change wordProb kernel 0 [] ≠ wordProb kernel 0 [true]
      rw [(hp []).1,(hp [true]).1]
      norm_num [profile]
    · change wordProb kernel 1 [] ≠ wordProb kernel 1 [true]
      rw [(hp []).2,(hp [true]).2]
      norm_num [profile]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@counterkernel_facts) (Realization signature) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.SixStateResidualSeparation.facts,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.SixStateResidualSeparation.record,
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
    (fun i _ w => if i then wordProb kernel 1 w else wordProb kernel 0 w)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.SixStateResidualSeparation
