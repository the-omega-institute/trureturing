import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open _root_.D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.checkUnivs false
noncomputable section
open _root_.D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
universe u_1

namespace Centering

abbrev signature : Signature where
  Params := Σ d : Type u_1, Matrix d d ℂ
  State p := Matrix p.1 p.1 ℂ → Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature.{u_1} (fun _ p center => center p.2) (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature.{u_1} (fun _ _ _ => fun _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {d : Type u_1} [Fintype d] [Nonempty d] [DecidableEq d]
    (effect : Matrix d d ℂ) (_hEffect : effect.IsHermitian),
    R.readout () ⟨d, effect⟩ centeredEffect ∈ HermitianTraceZero (d := d)

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  have he := (h (d := ULift.{u_1} Unit) 0 (by simp)).2
  norm_num [rejected, realize, Matrix.trace, Matrix.diag] at he

def source_registration : Registration arena.{u_1} (type_of% @_root_.D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.centered_effect_mem.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.{u_1}.Law actual from (@_root_.D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.centered_effect_mem.{u_1}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u_1} Unit, 0⟩, (fun _ => 0), (fun _ => fun _ _ => 1), ?_⟩
    intro h
    have he := congrArg (fun M => M ⟨()⟩ ⟨()⟩) h
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.centered_effect_mem.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.Centering.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.Centering.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1} (fun _ p center => center p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Centering

end
end Reg.D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
