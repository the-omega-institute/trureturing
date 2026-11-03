import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualMomentOrderArithmetic
import Reg.Support.SingleDependentReadout

/-! Typed owner attempts for the scalar endpoint; source selection remains open under issue #25822. -/

noncomputable section
universe u
open Filter Topology Real
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualMomentOrderArithmetic

namespace ScalarBounds

abbrev claim : Prop := type_of% @ActualKScalarSource.q_scalar_bounds

abbrev signature : Signature :=
  { Params := Unit
    State := fun _ => Bool
    Role := Unit
    finiteRole := inferInstance
    nonemptyRole := inferInstance
    Output := fun _ _ => Prop × Bool
    Anchor := Empty
    finiteAnchor := inferInstance }

def actual : Realization signature :=
  realize signature (fun _ _ state => (if state then True else claim, state))
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ state => (False, state)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := (R.readout () () false).1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), false, true, ?_⟩
  intro h
  have hs := congrArg Prod.snd h
  cases hs

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ActualKScalarSource.q_scalar_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ActualKScalarSource.q_scalar_bounds) (Realization signature) Unit Unit where
  unitName := `ActualKScalarSource.q_scalar_bounds.audit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualMomentOrderArithmetic.ScalarBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end ScalarBounds



end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualMomentOrderArithmetic
