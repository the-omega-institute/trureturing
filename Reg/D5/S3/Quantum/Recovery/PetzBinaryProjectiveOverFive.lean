import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the positive loss in the binary projective Petz family. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive
  (Physical commutatorNorm errorSq family_bounds input loss reference)

namespace Reg.D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (hx : 0 < x) (hsmall : x ≤ 1 / 100),
    R.readout () () (x ^ 2 / 5) (loss (input x hx hsmall) (reference x hx hsmall)) ∧
    loss (input x hx hsmall) (reference x hx hsmall) < (12141 / 10000) * x ^ 2 ∧
    (152 / 25) * x ^ 2 < errorSq (input x hx hsmall) (reference x hx hsmall) ∧
    commutatorNorm (reference x hx hsmall) ≤ x ^ 3 ∧
    Physical (input x hx hsmall) (reference x hx hsmall)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (1 / 100) (by norm_num) le_rfl).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @family_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@family_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@family_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive.family_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive
