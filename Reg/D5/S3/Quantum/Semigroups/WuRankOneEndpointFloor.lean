import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuRankOneEndpointFloor

/-! Source-bound readouts for the signed endpoint entries. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuRankOneEndpointFloor

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (Eq.mp (congrFun h 0) rfl)

namespace Entries

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode) (i j k l : Bit),
    R.readout () () (A₁ X (i, k) (j, l))
      (if i = j then
        if k = l then
          (25 / 36 : ℂ) * X (i, k) (j, l) +
          (5 / 36 : ℂ) * X (i, k.rev) (j, l.rev) +
          (5 / 36 : ℂ) * X (i.rev, k) (j.rev, l) +
          (1 / 36 : ℂ) * X (i.rev, k.rev) (j.rev, l.rev)
        else (lambda : ℂ) * ((5 / 6 : ℂ) * X (i, k) (j, l) +
          (1 / 6 : ℂ) * X (i.rev, k) (j.rev, l))
      else if k = l then (lambda : ℂ) * ((5 / 6 : ℂ) * X (i, k) (j, l) -
          (1 / 6 : ℂ) * X (i, k.rev) (j, l.rev))
        else (2 / 3 : ℂ) * X (i, k) (j, l))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0 0 0

def family : Registration arena (type_of% @A₁_apply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_apply, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_apply) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuRankOneEndpointFloor.A₁_apply.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuRankOneEndpointFloor.Entries.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuRankOneEndpointFloor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Entries

end Reg.D5.S3.Quantum.Semigroups.WuRankOneEndpointFloor
