import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.TwoLargeOrdering
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.TwoLargeOrdering

open _root_.D5.S3.Combinatorics.Circle.TwoLargeOrdering
open _root_.D5.S3.Combinatorics.Circle.SourceWidth

/-- Observe the original weight function at every physical label. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Fin n → ℤ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (f : Fin n → ℤ) (labels : List (Fin n)) (B : ℤ),
    labels.Nodup → 0 ≤ B → (labels.map f).sum = 0 →
    (∀ x ∈ labels, |f x| ≤ B) →
    (∀ x ∈ labels, ∀ y ∈ labels, B < 2 * f x → B < 2 * f y → x = y) →
    (∀ x ∈ labels, ∀ y ∈ labels, B < -2 * f x → B < -2 * f y → x = y) →
    ∃ word : List (Fin n), word.Perm labels ∧ InStrip (R.readout () ⟨n, f⟩) B 0 word

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨word, hp, hfalse⟩ := h (n := 1) (fun _ => 0) [0] 0
    (by simp) (by omega) (by simp) (by simp) (by simp) (by simp)
  have he : word = [0] := hp.eq_singleton
  subst word
  norm_num [rejected, realize, InStrip] at hfalse

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, (fun x => (x.val : ℤ))⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% (@exists_order)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_order, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.TwoLargeOrdering.exists_order)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.TwoLargeOrdering.exists_order.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.TwoLargeOrdering.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.TwoLargeOrdering
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.TwoLargeOrdering
