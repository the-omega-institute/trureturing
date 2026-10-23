import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookModel
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace Reg.D5.S1.Digit.Infinite.SixWindowForcing.Algebra
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => (1-x)/2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => t^2+1) (fun e => nomatch e)
def sourceStatement : Prop := g^2+4*g=1 ∧ (4/17:ℝ)<g ∧ g<17/72 ∧ t=(1+g)/2 ∧ t^2=(1-g)/2
abbrev arena : Arena where
  signature := signature
  Law R := g^2+4*g=1 ∧ (4/17:ℝ)<g ∧ g<17/72 ∧ t=(1+g)/2 ∧ t^2=R.readout () () g
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := hh.2.2.2.2
  change t^2=t^2+1 at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.SixWindowForcing.algebra,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.SixWindowForcing.algebra)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => (1-x)/2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.SixWindowForcing.algebra.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.SixWindowForcing.Algebra.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => (1-x)/2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.SixWindowForcing, definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "arg", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.SixWindowForcing.Algebra
