import D5.S3.Geometry.Hyperideal.SignedPortalGap
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Geometry.Hyperideal.SignedPortalGap
open _root_.D5.S3.Geometry.Hyperideal.SignedPortalGap
open _root_.D5.S3.Geometry.Hyperideal.SignedPortalGap.Family
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Nat) (fun _ => Nat)

def actual : Realization signature :=
  realize signature (fun _ _ L => 2*L+1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ L => 2*L+2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L : Nat) (hL : 0 < L),
    let zero : Fin (L+1) := ⟨0,by omega⟩
    CountedWalk insideFin portalFin 3 3 (origin,zero) (target,zero) ∧
    (∀ n k, CountedWalk insideFin portalFin n k (origin,zero) (target,zero) → 3 ≤ n) ∧
    (∃ n ≤ 2*L+1, CountedWalk insideFin portalFin n 1 (origin,zero) (target,zero)) ∧
    (∀ n, CountedWalk insideFin portalFin n 1 (origin,zero) (target,zero) →
      R.readout () () L ≤ n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := finite_signed_shift_unbounded_gap 1 (by decide)
  obtain ⟨n,hn,hw⟩ := ha.2.2.1
  have hb := (h 1 (by decide)).2.2.2 n hw
  change 2*(1 : Nat)+2 ≤ n at hb
  omega

private theorem actual_dependence : actual.readout () () 1 ≠ actual.readout () () 2 := by
  decide

def family : Registration arena (type_of% @finite_signed_shift_unbounded_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_signed_shift_unbounded_gap,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(),1,2,actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@finite_signed_shift_unbounded_gap) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Geometry.Hyperideal.SignedPortalGap.Family.finite_signed_shift_unbounded_gap.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.SignedPortalGap.family
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
    owner := `D5.S3.Geometry.Hyperideal.SignedPortalGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Geometry.Hyperideal.SignedPortalGap
