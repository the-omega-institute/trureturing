import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations

open scoped BigOperators
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion
open _root_.D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ n : ℕ, Fin (n + 2) → ℝ
  State p := Fin (p.1 + 2) → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.1 + 2) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p b => innovation (meansOf p.2) b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (w : Fin (n + 2) → ℝ) (_hw : ∀ i, 0 < w i),
    (∀ i j : Fin (n + 2), i ≠ j →
      (∑ b, law w b * R.readout () ⟨n, w⟩ b i * R.readout () ⟨n, w⟩ b j) = 0) ∧
    (∑ b, law w b * R.readout () ⟨n, w⟩ b 0 ^ 2) =
      meansOf w 0 * (1 - meansOf w 0) ∧
    (∀ i : Fin (n + 1),
      (∑ b, law w b * R.readout () ⟨n, w⟩ b i.succ ^ 2) =
        meansOf w (i.val + 1) * seam (meansOf w) i.val / (1 - meansOf w i.val))

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := (h 0 (fun _ => 1) (fun _ => zero_lt_one)).2.1
  have hmean : meansOf (fun _ : Fin 2 => (1 : ℝ)) 0 = 1 / 3 := by
    have sum_two (F : (Fin 2 → Bool) → ℝ) :
        (∑ b, F b) = ∑ a : Bool, ∑ b : Bool, F ![a, b] := by
      rw [← (piFinTwoEquiv fun _ : Fin 2 => Bool).symm.sum_comp,
        Fintype.sum_prod_type]
      rfl
    norm_num [meansOf, law, partition, sum_two, weight, monomial,
      Fintype.sum_bool, Adm, Finset.filter_insert, Finset.filter_singleton]
  rw [hmean] at hh
  simp only [rejected, realize, pow_two, mul_zero, Finset.sum_const_zero] at hh
  norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨0, fun _ => (1 : ℝ)⟩, (fun _ => false), (fun _ => true), ?_⟩
  intro h
  have he := congrFun h 0
  change (0 : ℝ) - meansOf (fun _ : Fin 2 => (1 : ℝ)) 0 =
    1 - meansOf (fun _ : Fin 2 => (1 : ℝ)) 0 at he
  linarith


def family : Registration arena (type_of% (@orthogonal_innovations)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨orthogonal_innovations, rejected, rejected_law⟩
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
    (@orthogonal_innovations) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations.family
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
    owner := `D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "arg", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg",
        "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "arg", "body", "fn", "arg",
        "arg", "body", "arg", "fn", "arg", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations
