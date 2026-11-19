import D5.S3.Arith.SumInConcatenation.DecimalMultiples
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Arith.SumInConcatenation.DecimalMultiples

open _root_.D5.S3.Arith.SumInConcatenation
open _root_.D5.S3.Arith.SumInConcatenation.DecimalMultiples
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
attribute [local instance] Classical.propDecidable

/- The source-bound family contract derives the escape origin from the complete
original theorem through sourceSelection. Its literal open-residual route
requires escapeFrom = none; a finite-route type operand would reject before
source reconstruction. The full family proofs and source selectors below
remain the mathematical and binding obligations. -/

namespace LegalTens

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m x => decide (Legal x (10 * m))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x m : ℕ), 0 < x → 0 < m ∧ m < 10 →
    (R.readout () m x = true ↔ x = m)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 1 1 (by decide) (by decide)).mpr rfl
  exact Bool.false_ne_true he

def family : Registration arena (type_of% @legal_multiple_ten_iff) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
    using legal_multiple_ten_iff, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    change decide (Legal 1 10) ≠ decide (Legal 2 10)
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@legal_multiple_ten_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.SumInConcatenation.DecimalMultiples.LegalTens.informationUnit
  realizationName := `Reg.D5.S3.Arith.SumInConcatenation.DecimalMultiples.LegalTens.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m x => decide (Legal x (10 * m)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.SumInConcatenation.DecimalMultiples
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LegalTens

namespace Exclusion

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => seq n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 20) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n m : ℕ), 2 ≤ m ∧ m < 10 → R.readout () m n ≠ 10 * m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 2 (by decide) rfl

def family : Registration arena (type_of% @sequence_ne_multiple_ten) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sequence_ne_multiple_ten, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨0, 0, 2, ?_⟩
    change seq 0 ≠ seq 2
    rw [sequence_multiple_ten_classification.1]
    norm_num [seq, state]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sequence_ne_multiple_ten) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.SumInConcatenation.DecimalMultiples.Exclusion.informationUnit
  realizationName := `Reg.D5.S3.Arith.SumInConcatenation.DecimalMultiples.Exclusion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => seq n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.SumInConcatenation.DecimalMultiples
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Exclusion

namespace Occurrence

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => seq n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 20) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := seq 2 = 10 ∧ ∀ m : ℕ, 0 < m ∧ m < 10 →
    ((∃ n, 1 ≤ n ∧ R.readout () () n = 10 * m) ↔ m = 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h.2 2 (by decide)).mp ⟨1, by decide, rfl⟩
  omega

def family : Registration arena (type_of% sequence_multiple_ten_classification) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sequence_multiple_ten_classification, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change seq 0 ≠ seq 2
    rw [sequence_multiple_ten_classification.1]
    norm_num [seq, state]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sequence_multiple_ten_classification) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.SumInConcatenation.DecimalMultiples.Occurrence.informationUnit
  realizationName := `Reg.D5.S3.Arith.SumInConcatenation.DecimalMultiples.Occurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => seq n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.SumInConcatenation.DecimalMultiples
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Occurrence

#print axioms LegalTens.family
#print axioms LegalTens.audit
#print axioms Exclusion.family
#print axioms Exclusion.audit
#print axioms Occurrence.family
#print axioms Occurrence.audit

end
end Reg.D5.S3.Arith.SumInConcatenation.DecimalMultiples
