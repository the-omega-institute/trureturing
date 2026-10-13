import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.ExactOriginal50
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ)
    (execution : List Return) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))),
    ActualPairSupply model o (r.readout () () b) .closed execution ↔
      GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) (!o 0) .high execution
        (initial .high model)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hqb, hbp⟩ :=
    Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.record_interval_nonempty
  have bad := (h .original (fun _ => false) b [] 2 (by decide) hqb hbp).mpr trivial
  obtain ⟨err, herr, _⟩ := bad .high
  have hb := herr 0
  change |err 0| ≤ (-1 : ℝ) at hb
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.actual_closed_record_supply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.actual_closed_record_supply, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def actual_closed_record_supply_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.actual_closed_record_supply)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.ExactOriginal50.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.ExactOriginal50.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_closed_record_supply_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.ExactOriginal50


open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150
  (observationSignature actual)
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budgetLower budget budget_interval)
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ResetBudgetReadout
  (rejected reset_floor_rejected)

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.ExactOriginal51
noncomputable section

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))),
    ∃ R : Return, R.r = 1 ∧
      let B := hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high)
      max (max (xSide .high) (ySide .high))
          ((lam - r.readout () () b) / g ^ 2 / chi ^ K) < B ∧
      (∀ D : ℝ, aSide .high < D → B < returnMap .high R D) ∧
      (∀ D : ℝ, aSide .high ≤ D → B ≤ returnMap .high R D) ∧
      (∀ (sourceModel targetModel : Model) (xs : List Return),
        GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) false .high xs
          (initial .high sourceModel) →
        ActualPairSupply targetModel o b .strict (R :: xs)) ∧
      (∀ xs : List Return, listWeight (R :: xs) = 20 + 6 * R.m + listWeight xs) ∧
      (∀ (m r : ℕ) (z : ℝ), 1 ≤ m → 1 ≤ r → r ≤ K → aSide .high ≤ z →
        let difference :=
          (hSide .high - rho ^ (m + 1) * (hSide .high - chi ^ r * z)) -
          (hSide .high - rho ^ m * (hSide .high - chi ^ r * hSide .high))
        difference = rho ^ m *
          (aSide .high - chi ^ r * hSide .high + rho * chi ^ r * z) ∧
        0 < difference)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => budgetLower) (fun e => nomatch e)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨R, _, floor, _⟩ :=
    h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2
  exact reset_floor_rejected R floor

def evidence : Registration sourceArena
    (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.actual_reset_first_return) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.actual_reset_first_return,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence

def actual_reset_first_return_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.actual_reset_first_return)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.ExactOriginal51.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.ExactOriginal51.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_reset_first_return_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply.ExactOriginal51
