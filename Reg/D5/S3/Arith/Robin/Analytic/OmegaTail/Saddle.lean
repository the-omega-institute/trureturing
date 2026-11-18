import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-! Exact source families for the entropy saddle and its minimum rate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle

namespace Characterization

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Set ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Set.Ioo (1 : ℝ) x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (∅ : Set ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (saddle ∈ R.readout () () 2) ∧ m saddle = 0 ∧
    (∀ s : ℝ, 1 < s → m s = 0 → s = saddle) ∧
    IsMinOn (_root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.rate 0) (Set.Ioi 1) saddle ∧
    C0 = _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.rate 0 saddle ∧ C0 = H saddle

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h.1

def family : Registration arena (type_of% @saddle_characterization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@saddle_characterization, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 2, ?_⟩
    intro he
    have hh : (3 / 2 : ℝ) ∈ Set.Ioo (1 : ℝ) 0 :=
      Eq.mpr (congrArg (fun S : Set ℝ => (3 / 2 : ℝ) ∈ S) he) (by
        constructor <;> norm_num)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@saddle_characterization) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.saddle_characterization.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle.Characterization.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Characterization

namespace PositiveConstant

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Set ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Set.Ioi x) (fun e => Empty.elim e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (∅ : Set ℝ)) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature
  Law R := C0 ∈ R.readout () () 1

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @constant_gt_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@constant_gt_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 2, ?_⟩
    intro he
    have hh : (2 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@constant_gt_one) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.constant_gt_one.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle.PositiveConstant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Set.Ioi x) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveConstant

namespace NegativeMoment

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, saddle < s → R.readout () () (m s) 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := saddle + 1) (by linarith)

def family : Registration arena (type_of% @m_neg_of_saddle_lt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@m_neg_of_saddle_lt, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 2, ?_⟩
    intro he
    have hh : (2 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@m_neg_of_saddle_lt) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.m_neg_of_saddle_lt.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle.NegativeMoment.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NegativeMoment

namespace EntropyContinuity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f s => ContinuousAt f s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 1 < s → R.readout () () H s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 2) (by norm_num)

def family : Registration arena (type_of% @H_continuousAt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@H_continuousAt, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun x : ℝ => (log x)⁻¹), ?_⟩
    intro he
    have hc : ContinuousAt (fun x : ℝ => (log x)⁻¹) 1 :=
      Eq.mp (congrFun he 1) continuousAt_const
    exact not_continuousAt_inv_log_one hc

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@H_continuousAt) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.H_continuousAt.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle.EntropyContinuity.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EntropyContinuity

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle
