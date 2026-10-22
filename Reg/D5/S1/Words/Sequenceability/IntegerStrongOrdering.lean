import D5.S1.Words.Sequenceability.IntegerStrongOrdering
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound interval-sum audit of the complete integer ordering theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.Sequenceability.IntegerStrongOrdering

open _root_.D5.S1.Words.Sequenceability.IntegerStrongOrdering
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _i : ℕ, ℕ
  State _ := List ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q w => ((w.drop q.1).take (q.2 - q.1)).sum)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Finset ℤ), 0 ∉ A →
    ∃ w : List ℤ, w.Perm A.toList ∧
      ∀ i j : ℕ, i < j → j ≤ w.length → (i ≠ 0 ∨ j ≠ w.length) →
        R.readout () ⟨i, j⟩ w ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, hw, hh⟩ := h {1, 2} (by decide)
  have hlen : w.length = 2 := by simpa using hw.length_eq
  exact hh 0 1 (by omega) (by omega) (Or.inr (by omega)) rfl

def family : Registration arena (type_of% (@exists_integer_strong_ordering)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_integer_strong_ordering, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨0, 1⟩, [1], [2], ?_⟩
    cases i
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_integer_strong_ordering) (Realization signature) Unit Unit where
  unitName :=
    `D5.S1.Words.Sequenceability.IntegerStrongOrdering.exists_integer_strong_ordering.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.IntegerStrongOrdering.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.IntegerStrongOrdering
    definition := none
    coordinates := #[3, 4]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body",
        "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.IntegerStrongOrdering
