import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Descartes.SplitPrimeSphereRadii
import Reg.Support.DependentFamily

/-! A source-bound audit of the complete shared-divisibility endpoint. -/

namespace Reg.D5.S3.Arith.Descartes.SplitPrimeSphereRadii

open _root_.D5.S3.Arith.Descartes.PrimitiveSphereRadii
open _root_.D5.S3.Arith.Descartes.SplitPrimeSphereRadii
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section
set_option autoImplicit false

abbrev signature : Signature where
  Params := ℕ × ℕ × Fin 4
  State _ := Fin 4 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q r =>
    (univ.filter fun j => j ≠ q.2.2 ∧ q.1 ^ q.2.1 ∣ r j).card)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : Fin 4 → ℕ) (_ : ∀ i, 0 < r i)
    (_ : gcd4 r = 1) (_ : sphereDescartes r)
    (p : ℕ) (_ : p.Prime) (_ : p % 3 = 1)
    (k : ℕ) (_ : 0 < k) (i : Fin 4) (_ : p ^ k ∣ r i),
    R.readout () (p, k, i) r = 1 ∨ R.readout () (p, k, i) r = 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hpos : ∀ i, 0 < (![28, 21, 12, 84] : Fin 4 → ℕ) i := by
    intro i
    fin_cases i <;> norm_num
  have hgcd : gcd4 ![28, 21, 12, 84] = 1 := by decide
  have hdesc : sphereDescartes ![28, 21, 12, 84] := by
    norm_num [sphereDescartes, Fin.sum_univ_succ]
  have he := h ![28, 21, 12, 84] hpos hgcd hdesc 7 (by decide) (by decide)
    1 (by decide) 0 (by norm_num)
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(7, 1, 0), (fun _ => 1), (fun _ => 7), ?_⟩
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Descartes.SplitPrimeSphereRadii.result.audit
  realizationName := `Reg.D5.S3.Arith.Descartes.SplitPrimeSphereRadii.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q r =>
    (univ.filter fun j => j ≠ q.2.2 ∧ q.1 ^ q.2.1 ∣ r j).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Descartes.SplitPrimeSphereRadii
    definition := none
    coordinates := #[4, 7, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end
end Reg.D5.S3.Arith.Descartes.SplitPrimeSphereRadii
