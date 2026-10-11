import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal123
noncomputable section


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Finset (List Return)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ family => family.card) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ) (contract : Contract) (N : ℕ),
    ∃ family : Finset (List Return),
      (∀ xs, xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N) ∧
      r.readout () () family = Nat.card {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N} ∧
      Finite {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  letI : IsEmpty {xs : List Return // ActualPairSupply .original (fun _ => false) (-1) .closed xs ∧ listWeight xs = 0} := ⟨by
    intro xs
    obtain ⟨err, bound, _⟩ := xs.property.1 .high
    have hb := bound 0
    have hn := abs_nonneg (err 0)
    change |err 0| ≤ -1 at hb
    linarith⟩
  obtain ⟨family, _, eq, _⟩ := h .original (fun _ => false) (-1) .closed 0
  change 1 = Nat.card _ at eq
  simpa using eq

def evidence : Registration sourceArena (type_of% @operation_exact_family) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@operation_exact_family, rejected, rejected_law⟩
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
    refine ⟨(), ∅, {[]}, ?_⟩
    simp [actual, realize]

def operation_exact_family_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.operation_exact_family)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ family => family.card) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal123.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal123.evidence
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
    (fun _ _ family => family.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms operation_exact_family_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal123

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal122
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
    (contract : Contract) (xs : List Return) (supply : ActualPairSupply model o b contract xs)
    (j : Side),
OperationRecord o (r.readout () () b) contract (source j model xs)
      (OperationPairedRecord model o xs j) ∧ OperationFiniteSource (source j model xs)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, _, _, supply⟩ :=
    Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.empty_strict_supply
      (fun _ => false)
  have bad := (h .original (fun _ => false) b .strict [] supply .high).1
  obtain ⟨x, _, err, herr, _⟩ := bad
  have hb := herr 0
  change |err 0| < (-1 : ℝ) at hb
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.operation_pair_membership) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.operation_pair_membership, rejected, rejected_law⟩
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

def operation_pair_membership_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.operation_pair_membership)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal122.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal122.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms operation_pair_membership_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations.ExactOriginal122
