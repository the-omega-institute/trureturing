import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal54
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => List Return
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => [⟨1, 2, by decide, by decide⟩]) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (hK : 1 ≤ K)
    (ω : ℤ → CuLetter) (hω : ω ∈ AuxiliaryLanguage K d)
    (i : ℤ) (xs : List Return)
    (letters : ∀ k : Fin (executionWord xs).length,
      (k.val + 1 < (executionWord xs).length ∨ (executionWord xs)[k.val] = .c) →
      ω (i + (k : ℕ)) = (executionWord xs)[k.val]),
    GuardTrace K d false .high (r.readout () () xs) (pastState ω i)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hω : (fun _ : ℤ => CuLetter.u) ∈ AuxiliaryLanguage 1 0 := by
    constructor
    · intro i hc
      have impossible := hc ⟨0, by decide⟩
      cases impossible
    · intro i hc
      have impossible := hc ⟨0, by decide⟩
      cases impossible
  have bad := h 1 0 (by decide) (fun _ => .u) hω 0 [] (by
    intro k
    exact Fin.elim0 k)
  have impossible := bad.1
  change 2 ≤ 1 at impossible
  omega

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.occurrence_run_guards) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.occurrence_run_guards, rejected, rejected_law⟩
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
    refine ⟨(), [], [⟨1, 1, by decide, by decide⟩], ?_⟩
    simp [actual, realize]

def occurrence_run_guards_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.occurrence_run_guards)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal54.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal54.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms occurrence_run_guards_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal54
