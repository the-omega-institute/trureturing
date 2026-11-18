import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.FermiMellin
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.FermiMellin

namespace Reg.D5.S3.Weil.ZetaBridge.FermiMellin

namespace Bounds
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, R.readout () () 0 (fermi t) ∧ fermi t < 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0).1
def family : Registration arena (type_of% @fermi_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fermi_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he (1 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    exact lt_irrefl _ hh
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fermi_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaBridge.FermiMellin.fermi_bounds.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.FermiMellin.Bounds.family
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
    owner := `D5.S3.Weil.ZetaBridge.FermiMellin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Bounds

namespace Envelope
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, R.readout () () (fermi t) (exp (-t))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0
def family : Registration arena (type_of% @fermi_le_exp_neg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fermi_le_exp_neg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fermi_le_exp_neg) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaBridge.FermiMellin.fermi_le_exp_neg.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.FermiMellin.Envelope.family
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
    owner := `D5.S3.Weil.ZetaBridge.FermiMellin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Envelope

namespace Continuity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ f => Continuous f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () fermi
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h
def family : Registration arena (type_of% @continuous_fermi) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuous_fermi, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), Real.log, ?_⟩
    intro he
    have hc : Continuous Real.log := Eq.mp he continuous_const
    exact (Real.continuousAt_log_iff.mp (hc.continuousAt (x := (0 : ℝ)))) rfl
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_fermi) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaBridge.FermiMellin.continuous_fermi.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.FermiMellin.Continuity.family
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
    owner := `D5.S3.Weil.ZetaBridge.FermiMellin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Continuity

end Reg.D5.S3.Weil.ZetaBridge.FermiMellin
