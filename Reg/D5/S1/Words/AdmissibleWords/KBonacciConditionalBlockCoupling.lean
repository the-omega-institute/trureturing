import D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open D5.S0.Tower.DBonacci.Names
open D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal NNReal Classical
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
namespace CompletionNonempty
abbrev signature : Signature where
  Params := Σ k : ℕ, Σ n : ℕ, Finset (Fin n)
  State p := Fin p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (Fin p.2.1 → Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p exterior => completions p.1 p.2.1 p.2.2 exterior)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n : ℕ} (fixed : Finset (Fin n)) (exterior : Fin n → Bool),
    DBonacciAdmissible k n exterior → (R.readout () ⟨k, n, fixed⟩ exterior).Nonempty

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (k := 2) (n := 1) ∅ (fun _ => false) (by decide)
  simpa only [rejected, realize, Finset.not_nonempty_empty] using he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1, Finset.univ⟩, (fun _ => false), (fun _ => true), ?_⟩
  intro he
  change completions 2 1 Finset.univ (fun _ => false) =
    completions 2 1 Finset.univ (fun _ => true) at he
  have hm : (fun _ : Fin 1 => false) ∈
      completions 2 1 Finset.univ (fun _ => false) := by
    simp [completions, show DBonacciAdmissible 2 1 (fun _ => false) from by decide]
  rw [he] at hm
  have hh := (Finset.mem_filter.mp hm).2.2 (0 : Fin 1) (by simp)
  simp at hh

def proof_record : Registration arena (type_of% @completion_nonempty) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@completion_nonempty, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@completion_nonempty) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling.completion_nonempty.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling.CompletionNonempty.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]
#print axioms proof_record
end CompletionNonempty

end Reg.D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
