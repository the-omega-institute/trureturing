import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.IncompleteBetaShape.Kernel
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-! Dependent-family registrations for the affine beta kernel. -/

open _root_.D5.S3.Analytic.IncompleteBetaShape.Kernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory
open scoped Real

noncomputable section
namespace Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel

private theorem kernel_dependence :
    ObservationalDependence
      (_root_.Reg.Support.SingleDependentReadout.signature
        (Σ _ : ℝ, Σ _ : ℕ, ℝ) (fun _ => ℝ) (fun _ => ℝ))
      (realize _ (fun _ q v => H q.1 q.2.1 q.2.2 v) (fun e => nomatch e)) := by
  intro i
  refine ⟨⟨1,⟨0,2⟩⟩, 1/4, 1/2, ?_⟩
  exact ne_of_lt (H_strictMonoOn_of_one_lt (by norm_num : (0:ℝ)<1)
    (by norm_num : (1:ℝ)<2) 0 (by norm_num) (by norm_num) (by norm_num))

namespace Reflection
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℕ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => H q.1 q.2.1 q.2.2 v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => v) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ c : ℝ, ∀ n : ℕ, ∀ b v : ℝ, R.readout () ⟨c,⟨n,b⟩⟩ (1-v) = R.readout () ⟨c,⟨n,b⟩⟩ v
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0 2 0
  norm_num [rejected, realize] at hh
def family : Registration arena (type_of% @H_symm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@H_symm, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := kernel_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@H_symm) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Reflection.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Reflection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => H q.1 q.2.1 q.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reflection

namespace Continuity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => H q.1 q.2.2 q.2.1 v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => (Real.log (v+1/2))⁻¹) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {c b : ℝ}, 0 < c → 0 < b → ∀ n : ℕ, ContinuousOn (R.readout () ⟨c,⟨b,n⟩⟩) (Icc 0 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (c := 1) (b := 2) (by norm_num) (by norm_num) 0
  have ha : ContinuousAt (fun v : ℝ => (Real.log (v+1/2))⁻¹) (1/2) :=
    hh.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have he := ha.comp_of_eq (x := (1:ℝ)) (continuousAt_id.sub_const (1/2)) (by norm_num)
  have hn : ContinuousAt (fun v : ℝ => (Real.log v)⁻¹) 1 := by
    simpa only [Function.comp_def, id_eq, sub_add_cancel] using he
  exact Real.not_continuousAt_inv_log_one hn
def family : Registration arena (type_of% @H_continuousOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@H_continuousOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1,⟨2,0⟩⟩, 1/4, 1/2, ?_⟩
    exact ne_of_lt (H_strictMonoOn_of_one_lt (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ)<2) 0 (by norm_num) (by norm_num) (by norm_num))
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@H_continuousOn) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Continuity.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Continuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => H q.1 q.2.2 q.2.1 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Continuity

namespace Boundedness
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => H q.1 q.2.2 q.2.1 v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => v⁻¹) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {c b : ℝ}, 0 < c → 0 < b → ∀ n : ℕ, ∃ C : ℝ, ∀ v ∈ Icc 0 1, ‖R.readout () ⟨c,⟨b,n⟩⟩ v‖ ≤ C
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C,hC⟩ := h (c := 1) (b := 2) (by norm_num) (by norm_num) 0
  have hp : 0 < |C|+1 := by positivity
  have hv : (|C|+1)⁻¹ ∈ Icc (0:ℝ) 1 :=
    ⟨(inv_pos.mpr hp).le, (inv_le_one₀ hp).mpr (by linarith [abs_nonneg C])⟩
  have hh := hC _ hv
  change ‖((|C|+1)⁻¹)⁻¹‖ ≤ C at hh
  rw [inv_inv, Real.norm_of_nonneg hp.le] at hh
  linarith [le_abs_self C]
def family : Registration arena (type_of% @H_bounded) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@H_bounded, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1,⟨2,0⟩⟩, 1/4, 1/2, ?_⟩
    exact ne_of_lt (H_strictMonoOn_of_one_lt (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ)<2) 0 (by norm_num) (by norm_num) (by norm_num))
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@H_bounded) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Boundedness.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Boundedness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => H q.1 q.2.2 q.2.1 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Boundedness

namespace Increase
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => H q.1 q.2.2 q.2.1 v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {c b : ℝ}, 0 < c → 1 < b → ∀ n : ℕ, StrictMonoOn (R.readout () ⟨c,⟨b,n⟩⟩) (Ioc 0 (1/2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (c := 1) (b := 2) (by norm_num) (by norm_num) 0
    (show (1/4:ℝ) ∈ Ioc 0 (1/2) by norm_num)
    (show (1/2:ℝ) ∈ Ioc 0 (1/2) by norm_num) (by norm_num : (1/4:ℝ)<1/2)
  exact (lt_irrefl (0:ℝ)) hh
def family : Registration arena (type_of% @H_strictMonoOn_of_one_lt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@H_strictMonoOn_of_one_lt, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1,⟨2,0⟩⟩, 1/4, 1/2, ?_⟩
    exact ne_of_lt (H_strictMonoOn_of_one_lt (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ)<2) 0 (by norm_num) (by norm_num) (by norm_num))
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@H_strictMonoOn_of_one_lt) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Increase.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Increase.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => H q.1 q.2.2 q.2.1 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Increase

namespace Decrease
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => H q.1 q.2.2 q.2.1 v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {c b : ℝ}, 0 < c → 0 < b → b < 1 → ∀ n : ℕ, StrictAntiOn (R.readout () ⟨c,⟨b,n⟩⟩) (Ioc 0 (1/2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (c := 1) (b := 1/2) (by norm_num) (by norm_num) (by norm_num) 0
    (show (1/4:ℝ) ∈ Ioc 0 (1/2) by norm_num)
    (show (1/2:ℝ) ∈ Ioc 0 (1/2) by norm_num) (by norm_num : (1/4:ℝ)<1/2)
  exact (lt_irrefl (0:ℝ)) hh
def family : Registration arena (type_of% @H_strictAntiOn_of_lt_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@H_strictAntiOn_of_lt_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1,⟨2,0⟩⟩, 1/4, 1/2, ?_⟩
    exact ne_of_lt (H_strictMonoOn_of_one_lt (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ)<2) 0 (by norm_num) (by norm_num) (by norm_num))
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@H_strictAntiOn_of_lt_one) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Decrease.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.Decrease.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => H q.1 q.2.2 q.2.1 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Decrease

namespace InnerIntegrability
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => v^(q.1-1)*(1-v)^((q.2.2.2:ℝ)+1)*F q.2.1 v q.2.2.1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => v⁻¹) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {c b v : ℝ}, 0 < c → 0 < b → ∀ n : ℕ, v ∈ Icc 0 1 → IntervalIntegrable (fun s => R.readout () ⟨c,⟨b,⟨v,n⟩⟩⟩ s) volume 0 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (c := 1) (b := 1) (v := 0) (by norm_num) (by norm_num) 0 (by norm_num)
  change IntervalIntegrable (fun s : ℝ => s⁻¹) volume 0 1 at hh
  norm_num [intervalIntegrable_inv_iff] at hh
def family : Registration arena (type_of% @H_integrand_intervalIntegrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@H_integrand_intervalIntegrable, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1,⟨1,⟨0,0⟩⟩⟩, 0, 1, ?_⟩
    norm_num [actual, realize, F, w]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@H_integrand_intervalIntegrable) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.InnerIntegrability.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.InnerIntegrability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => v^(q.1-1)*(1-v)^((q.2.2.2:ℝ)+1)*F q.2.1 v q.2.2.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end InnerIntegrability

namespace AffineReflection
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => F q.1 q.2 v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => v) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ b s v : ℝ, R.readout () ⟨b,s⟩ (1-v) = R.readout () ⟨b,s⟩ v
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 1 0
  norm_num [rejected, realize] at hh
def family : Registration arena (type_of% @F_symm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@F_symm, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨2,1⟩, 0, 1/2, ?_⟩
    norm_num [actual, realize, F, w]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@F_symm) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.AffineReflection.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.AffineReflection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => F q.1 q.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AffineReflection

namespace AffineContinuity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => F q.1 q.2 v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => (Real.log (v+1/2))⁻¹) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {b s : ℝ}, 0 < b → s ∈ Ico 0 1 → ContinuousOn (R.readout () ⟨b,s⟩) (Icc 0 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (b := 2) (s := 0) (by norm_num) (by norm_num)
  have ha : ContinuousAt (fun v : ℝ => (Real.log (v+1/2))⁻¹) (1/2) :=
    hh.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have he := ha.comp_of_eq (x := (1:ℝ)) (continuousAt_id.sub_const (1/2)) (by norm_num)
  have hn : ContinuousAt (fun v : ℝ => (Real.log v)⁻¹) 1 := by
    simpa only [Function.comp_def, id_eq, sub_add_cancel] using he
  exact Real.not_continuousAt_inv_log_one hn
def family : Registration arena (type_of% @F_continuousOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@F_continuousOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨2,1⟩, 0, 1/2, ?_⟩
    norm_num [actual, realize, F, w]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@F_continuousOn) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.AffineContinuity.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.AffineContinuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => F q.1 q.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AffineContinuity

namespace AffineBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q v => F q.1 q.2 v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q v => (Real.Gamma q.1 * Real.Gamma q.1 / Real.Gamma (2*q.1))/(1-q.2)+1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {b s v : ℝ}, 0 < b → s ∈ Ico 0 1 → v ∈ Icc 0 1 → |R.readout () ⟨b,s⟩ v| ≤ (Real.Gamma b * Real.Gamma b / Real.Gamma (2*b))/(1-s)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (b := 1) (s := 0) (v := 0) (by norm_num) (by norm_num) (by norm_num)
  have hg : Real.Gamma 2 = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  norm_num [rejected, realize, Real.Gamma_one, hg] at hh
def family : Registration arena (type_of% @F_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@F_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨2,1⟩, 0, 1/2, ?_⟩
    norm_num [actual, realize, F, w]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@F_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.AffineBound.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel.AffineBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => F q.1 q.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Kernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AffineBound

end Reg.D5.S3.Analytic.IncompleteBetaShape.Kernel
