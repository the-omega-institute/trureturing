import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation
import Reg.Support.DependentFamily

/-! The common duplication ideal as a varying ideal-valued family. -/

namespace Reg.D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation

open _root_.D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Order
  State := fun _ => Order
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Ideal Order
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a b => commonIdeal a b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (⊥ : Ideal Order)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : Order) (_hab : Ideal.span {a, b} = ⊤),
    ¬ R.readout () a b ≤ (Ideal.span {root}) ^ 7 ∧
    ¬ R.readout () a b ≤ (Ideal.span {delta}) ^ 5 ∧
    ∀ q : Ideal Order, q.IsPrime → R.readout () a b ≤ q →
      q = Ideal.span {root} ∨ q = Ideal.span {delta}

private theorem rejected_negative : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0 (by simp)
  exact hh.1 bot_le

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  change ∃ (a b c : Order), commonIdeal a b ≠ commonIdeal a c
  refine ⟨0, 0, 1, ?_⟩
  intro heq
  have hf : numerator 0 1 ∈ commonIdeal 0 1 := Ideal.subset_span (by simp)
  rw [← heq] at hf
  have hz : numerator 0 1 = 0 := by
    simpa [commonIdeal, numerator, denominator] using hf
  have hr := congrArg Zsqrtd.re hz
  norm_num [numerator, delta, root, pow_succ] at hr

def realization : Registration arena (type_of% (@primitive_duplication_local)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨primitive_duplication_local, rejected, rejected_negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_negative⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def primitive_duplication_local_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@primitive_duplication_local)
      (type_of% (realize signature (fun _ a b => commonIdeal a b) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation.primitive_duplication_local.__information_unit
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => commonIdeal a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

#print axioms realization
#print axioms primitive_duplication_local_registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation
