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

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal132
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := List Return
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ xs E => execute .high xs E) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => aSide .high) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K N : ℕ) (d B : ℝ) (model : Model) (xs : List Return)
    (weak : GuardTrace K d false .high xs (initial .high model))
    (weight : listWeight xs = N) (above : initial .high model < B)
    (E : ℝ) (raised : B ≤ E),
    GuardTrace K (d + (B-initial .high model)*g^N) false .high xs E ∧
    aSide .high < r.readout () xs E

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h 0 0 0 (initial .high .original + 1) .original []
    trivial rfl (by linarith) (initial .high .original + 1) le_rfl).2
  exact lt_irrefl _ impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.exact_guard_gain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.exact_guard_gain, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨[], 0, 1, ?_⟩
    norm_num [actual, realize, execute]

def exact_guard_gain_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.exact_guard_gain)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ xs E => execute .high xs E) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal132.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal132.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ xs E => execute .high xs E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms exact_guard_gain_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal132

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal134
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : ℤ → List CuLetter, ℤ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p n => (blockWindow p.1 p.2 n).length) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (W : ℤ → List CuLetter) (positive : ∀ j, 0 < (W j).length) (a : ℤ) (n : ℕ),
    (r.readout () ⟨W, a⟩ n : ℤ) = blockCut W (a+n)-blockCut W a ∧
    ∀ j : ℕ, j < n → ∀ k : ℕ, k < (W (a+(j : ℤ))).length →
      (blockWindow W a n)[(blockCut W (a+(j : ℤ))-blockCut W a).toNat+k]?.getD .u =
        (W (a+(j : ℤ)))[k]?.getD .u

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h (fun _ => [.u]) (by intro j; simp) 0 0).1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.block_window_positions) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.block_window_positions, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨(fun _ => [.u]), 0⟩, 0, 1, ?_⟩
    simp [actual, realize, blockWindow]

def block_window_positions_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.block_window_positions)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p n => (blockWindow p.1 p.2 n).length) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal134.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal134.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p n => (blockWindow p.1 p.2 n).length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms block_window_positions_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal134
