import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.ErdosNicolas.Classification
import D5.S3.Arith.Divisors.ErdosNicolas.Main
import Reg.Support.DependentFamily

/-! Source-bound audit of the full six-certificate strong-induction theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.ErdosNicolas.Classification

open _root_.D5.S3.Arith.ErdosNicolas
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => @decide (Good n) (by unfold Good; infer_instance))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (_ : BaseOK) (_ : SmallLiftsOK) (_ : LargeLiftsOK)
    (_ : ResidueTreeOK) (_ : MainBoxOK) (_ : ExtraOK),
    ∀ n : ℕ, 0 < n → R.readout () () n = true

private theorem actual_law : arena.Law actual := by
  simpa only [arena, actual, realize, decide_eq_true_eq] using @good_of_finite_certificates

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h Data.Base.base_ok (Data.SmallLifts.small_ok Data.Base.base_ok)
    Data.LargeLifts.large_ok Data.ResidueTrees.residue_tree_ok
    (Data.MainBox.main_box_ok Data.Base.base_ok) Data.Extra.extra_ok 1 (by decide)
  exact Bool.noConfusion he

def evidence : Registration arena (type_of% @good_of_finite_certificates) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    have hzero : ¬Good 0 := by norm_num [Good, exceptions, hHat, pairSum]
    have hone : Good 1 := by norm_num [Good, exceptions, hHat, pairSum]
    simp only [actual, realize, hzero, hone, decide_false, decide_true]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@good_of_finite_certificates) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ErdosNicolas.good_of_finite_certificates.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.ErdosNicolas.Classification.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => @decide (Good n) (by unfold Good; infer_instance)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.ErdosNicolas.Classification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms audit

end
end Reg.D5.S3.Arith.Divisors.ErdosNicolas.Classification
