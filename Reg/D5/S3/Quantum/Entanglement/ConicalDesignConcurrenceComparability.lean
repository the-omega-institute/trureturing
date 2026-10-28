import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
open _root_.D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.checkUnivs false
noncomputable section
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
universe u_3

namespace Scaling

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c x => c * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u_3} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (c : ℝ) (_hc : 0 ≤ c),
    traceNorm ((c : ℂ) • X) = R.readout () c (traceNorm X)

theorem rejected_law : ¬ arena.{u_3}.Law rejected := by
  intro h
  have he := h (n := ULift.{u_3} Unit) 1 1 (by norm_num)
  norm_num [rejected, realize, traceNorm] at he

def source_registration : Registration arena.{u_3} (type_of% @_root_.D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg.{u_3}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.{u_3}.Law actual from (@_root_.D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg.{u_3}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg.{u_3}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.Scaling.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.Scaling.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_3}⟩
  objectArena := .source ⟨arena.{u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_3} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c x => c * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Scaling

end
end Reg.D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
