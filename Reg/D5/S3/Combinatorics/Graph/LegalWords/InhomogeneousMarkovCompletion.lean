import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion

open scoped BigOperators
open _root_.D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := (ℕ → ℝ) × ℕ
  State p := Fin (p.2 + 2) → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => completion p.1 p.2 w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : ℕ → ℝ) (n : ℕ) (_hu : Interior u (n + 2)),
    LegalLaw (n + 1) (R.readout () (u, n)) ∧
    Means u (n + 1) (R.readout () (u, n)) ∧
    Markov (n + 1) (R.readout () (u, n)) ∧
    ∀ P : (Fin (n + 2) → Bool) → ℝ,
      LegalLaw (n + 1) P → Means u (n + 1) P → Markov (n + 1) P →
        P = R.readout () (u, n)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hi : Interior (fun _ => (1 / 4 : ℝ)) 2 := by
    constructor <;> intros <;> norm_num
  have hh := (h (fun _ => 1 / 4) 0 hi).1.2.1
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨((fun _ => (1 / 4 : ℝ)), 0), (fun _ => false), (fun i => decide (i = 0)), ?_⟩
  norm_num [actual, realize, completion, Fin.prod_univ_succ, pair]

def family : Registration arena (type_of% (@unique_markov_completion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unique_markov_completion, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@unique_markov_completion) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion
