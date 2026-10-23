import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.QuotientIntegralBudget
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace Reg.D5.S3.Arith.Robin.QuotientIntegralBudget
open _root_.D5.S3.Arith.Robin.QuotientIntegralBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev prefixSignature : Signature where
  Params := Sigma (fun _ : ℕ => ℝ)
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ p k => arithmeticPrefix k p.2) (fun e => nomatch e)
def prefixRejected : Realization prefixSignature :=
  realize prefixSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev prefixArena : Arena where
  signature := prefixSignature
  Law r := ∀ (k : ℕ → ℝ) {N : ℕ} {y : ℝ}, 0 ≤ y → y ≤ N →
    r.readout () ⟨N, y⟩ k = ∑ i ∈ Finset.range N,
      if ((i + 1 : ℕ) : ℝ) ≤ y then k (i + 1) else 0
private theorem prefix_rejected : ¬ prefixArena.Law prefixRejected := by
  intro h
  have ht := h (fun _ => 0) (N := 0) (y := 0) le_rfl (by norm_num)
  norm_num [prefixRejected, realize] at ht
private theorem prefix_dependence : ObservationalDependence prefixSignature prefixActual := by
  intro i
  refine ⟨⟨1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change arithmeticPrefix (fun _ => 0) 1 ≠ arithmeticPrefix (fun _ => 1) 1
  norm_num [arithmeticPrefix]
def prefixFamily : Registration prefixArena (type_of% prefix_as_finite_sum) where
  actual := prefixActual
  bridge := Iff.rfl
  variation := ⟨prefix_as_finite_sum, prefixRejected, prefix_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨prefixRejected, ?_, rfl, prefix_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := prefix_dependence

def prefixRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    prefix_as_finite_sum (type_of% (realize prefixSignature prefixActual.readout prefixActual.anchor))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.QuotientIntegralBudget.prefix_as_finite_sum.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.QuotientIntegralBudget.prefixFamily
  realizationSource := none
  generated := false
  arena := .source ⟨prefixArena⟩
  objectArena := .source ⟨prefixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prefixArena ⟨prefixFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize prefixSignature prefixActual.readout prefixActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ → ℝ)
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.QuotientIntegralBudget
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev differenceSignature : Signature where
  Params := Sigma (fun _ : ℕ => Sigma (fun _ : ℝ => ℝ))
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def differenceActual : Realization differenceSignature :=
  realize differenceSignature
    (fun _ p k => arithmeticPrefix k p.2.2 - arithmeticPrefix k (p.2.1 * p.2.2))
    (fun e => nomatch e)
def differenceRejected : Realization differenceSignature :=
  realize differenceSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev differenceArena : Arena where
  signature := differenceSignature
  Law r := ∀ (k : ℕ → ℝ) {N : ℕ} {c y : ℝ}, 0 ≤ y → 0 ≤ c * y →
    c * y ≤ y → y ≤ N → r.readout () ⟨N, ⟨c, y⟩⟩ k =
      ∑ i ∈ Finset.range N,
        if c * y < ((i + 1 : ℕ) : ℝ) ∧ ((i + 1 : ℕ) : ℝ) ≤ y then k (i + 1) else 0
private theorem difference_rejected : ¬ differenceArena.Law differenceRejected := by
  intro h
  have ht := h (fun _ => 0) (N := 0) (c := 1) (y := 0)
    le_rfl (by norm_num) (by norm_num) (by norm_num)
  norm_num [differenceRejected, realize] at ht
private theorem difference_dependence : ObservationalDependence differenceSignature differenceActual := by
  intro i
  refine ⟨⟨1, ⟨0, 1⟩⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change arithmeticPrefix (fun _ => 0) 1 - arithmeticPrefix (fun _ => 0) (0 * 1) ≠
    arithmeticPrefix (fun _ => 1) 1 - arithmeticPrefix (fun _ => 1) (0 * 1)
  norm_num [arithmeticPrefix]
def differenceFamily : Registration differenceArena (type_of% prefix_difference_finite) where
  actual := differenceActual
  bridge := Iff.rfl
  variation := ⟨prefix_difference_finite, differenceRejected, difference_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨differenceRejected, ?_, rfl, difference_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := difference_dependence

def differenceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    prefix_difference_finite
    (type_of% (realize differenceSignature differenceActual.readout differenceActual.anchor))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.QuotientIntegralBudget.prefix_difference_finite.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.QuotientIntegralBudget.differenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨differenceArena⟩
  objectArena := .source ⟨differenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source differenceArena ⟨differenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize differenceSignature differenceActual.readout differenceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ → ℝ)
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.QuotientIntegralBudget
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.QuotientIntegralBudget
