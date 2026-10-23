import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.TwoRunSource
import Reg.Support.DependentFamily

/-! # Source-bound registration for the complete actual two-run construction -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.TwoRunSource

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.TwoRunSource

/-- The original natural parameter and all physical values are retained. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ), 0 < k → ∀ (t : ℕ), TwoRun k t →
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      InStrip (R.readout () k t) (amplitude k t) 0 word ∧
      0 ≤ amplitude k t ∧ amplitude k t ≤ ((2 : ℤ) ^ k - 2) / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨word, hp, hs, _⟩ := h 1 (by omega) 0
    (Or.inl (by norm_num [orbit, centered, modulus]))
  rw [show List.finRange 1 = [0] by decide] at hp
  have he : word = [0] := hp.eq_singleton
  subst word
  norm_num [rejected, realize, InStrip, amplitude, actualSource, centered, modulus] at hs

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 3)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def source_registration : Registration arena (type_of% (@exists_order)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_order, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.Circle.TwoRunSource.exists_order)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.TwoRunSource.exists_order.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.TwoRunSource.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.TwoRunSource
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "fn", "arg",
        "fn", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end Reg.D5.S3.Combinatorics.Circle.TwoRunSource
