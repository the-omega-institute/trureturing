import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook

noncomputable section

abbrev seedSignature : Signature where
  Params := Σ _ : List Return, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def seedActual : Realization seedSignature :=
  realize seedSignature (fun _ p y => execute .high p.1 y) (fun e => nomatch e)

def seedRejected : Realization seedSignature :=
  realize seedSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev seedArena : Arena where
  signature := seedSignature
  Law R := ∀ (xs : List Return) (x y : ℝ),
    R.readout () ⟨xs, x⟩ y - execute .high xs x = g ^ listWeight xs * (y - x)

theorem seed_rejected_law : ¬ seedArena.Law seedRejected := by
  intro h
  have hh := h [] 0 1
  norm_num [seedRejected, realize, execute, listWeight] at hh

def seedRegistration : Registration seedArena
    (∀ (xs : List Return) (x y : ℝ),
      execute .high xs y - execute .high xs x = g ^ listWeight xs * (y - x)) where
  actual := seedActual
  bridge := Iff.rfl
  variation := ⟨execute_seed_difference, seedRejected, seed_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seedRejected, ?_, rfl, seed_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨[], 0⟩, 0, 1, ?_⟩
    norm_num [seedActual, realize, execute]

def execute_seed_difference_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.execute_seed_difference)
      (type_of% (realize.{0,0,0,0,0} seedSignature
        (fun _ p y => execute .high p.1 y) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.execute_seed_difference_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.seedRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨seedArena⟩
  objectArena := .source ⟨seedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source seedArena ⟨seedRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} seedSignature
    (fun _ p y => execute .high p.1 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms seedRegistration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
