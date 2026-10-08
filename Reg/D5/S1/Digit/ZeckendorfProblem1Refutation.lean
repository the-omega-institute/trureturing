import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.ZeckendorfProblem1Refutation
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.ZeckendorfResidualMachine
open D5.S1.Digit.ZeckendorfProblem1Refutation

namespace Reg.D5.S1.Digit.ZeckendorfProblem1Refutation
noncomputable section
open Classical

abbrev signature : Signature where
  Params := ℝ × ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p a => a * p.2 ≤ minimumStates p.2 ∧ (minimumStates p.2 : ℝ) ≤ p.1 * p.2)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ c0 : ℕ,
    ∀ c : ℕ, c0 ≤ c → R.readout () (b,c) a)

def rejected : Realization signature := realize signature
  (fun _ p a => a * p.2 ≤ p.2 ∧ (p.2 : ℝ) ≤ p.1 * p.2)
  (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  refine ⟨1,1,by norm_num,by norm_num,0,?_⟩
  intro c hc
  simp [rejected,realize]

def registration : Registration arena (¬ Problem1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨problem1_refuted,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨((minimumStates 1 : ℝ),1),0,(minimumStates 1 : ℝ)+1,?_⟩
    intro he
    have htrue : actual.readout i ((minimumStates 1 : ℝ),1) 0 := by
      simp [actual,realize]
    have hbad := Eq.mp he htrue
    simp only [actual,realize,Nat.cast_one,mul_one] at hbad
    linarith [hbad.1]

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S1.Digit.ZeckendorfProblem1Refutation
  definition := some {
    owner := `D5.S1.Digit.ZeckendorfProblem1Refutation
    name := `D5.S1.Digit.ZeckendorfProblem1Refutation.Problem1
    path := #["arg"]}
  coordinates := #[1,3]
  readouts := #[{
    path := #["arg","arg","body","arg","body","arg","arg","arg","body","body","body"]
    stateBinder := 0
    stateOperand := some #["fn","arg","fn","arg","fn","arg"]}] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Digit.ZeckendorfProblem1Refutation.problem1_refuted) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p a => a * p.2 ≤ minimumStates p.2 ∧ (minimumStates p.2 : ℝ) ≤ p.1 * p.2)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfProblem1Refutation") "problem1_refuted") "Reg.D5.S1.Digit.ZeckendorfProblem1Refutation/Reg.D5.S1.Digit.ZeckendorfProblem1Refutation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfProblem1Refutation.registration,
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
    (fun _ p a => a * p.2 ≤ minimumStates p.2 ∧ (minimumStates p.2 : ℝ) ≤ p.1 * p.2)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfProblem1Refutation, definition := some { owner := `D5.S1.Digit.ZeckendorfProblem1Refutation, name := `D5.S1.Digit.ZeckendorfProblem1Refutation.Problem1, path := #["arg"] }, coordinates := #[1, 3], readouts := #[{ path := #["arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "body", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg", "fn", "arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfProblem1Refutation
