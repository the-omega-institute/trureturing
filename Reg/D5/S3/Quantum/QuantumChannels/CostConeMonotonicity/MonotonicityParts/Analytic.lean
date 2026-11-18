import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
import Reg.Support.SingleDependentReadout
import Mathlib.MeasureTheory.Measure.Count

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Set MeasureTheory Real

namespace Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Analytic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

namespace SinePositive
def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℝ} (hp : 0 < p) (hpq : p < q), R.readout () () 0 (sineMoment p q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (p := 1) (q := 2) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), 1, ?_⟩
  intro he
  have h : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
  exact lt_irrefl _ h

def source_registration : Registration arena (type_of% @sineMoment_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sineMoment_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@sineMoment_pos) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.sineMoment_pos.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Analytic.SinePositive.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end SinePositive

namespace PhasePositive
def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℝ} (hq : 0 < q), R.readout () () 0 (phaseMoment q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (q := 1) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), 1, ?_⟩
  intro he
  have h : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
  exact lt_irrefl _ h

def source_registration : Registration arena (type_of% @phaseMoment_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@phaseMoment_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@phaseMoment_pos) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.phaseMoment_pos.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Analytic.PhasePositive.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
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
  options := #[] }

#print axioms source_registration
#print axioms registration
end PhasePositive

namespace Integral
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℝ} (hp : 0 < p) (hpq : p < q) (x y : ℝ),
    R.readout () () (∫ a, sineDistanceIntegrand p q x y a ∂sineParameterMeasure)
      ((2 ^ q * phaseMoment q * sineMoment p q / 2 ^ p) * |x-y|^p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (p := 1) (q := 2) (by norm_num) (by norm_num) 0 1

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), 1, ?_⟩
  intro he
  have h : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

def source_registration : Registration arena (type_of% @integral_sineDistance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_sineDistance, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@integral_sineDistance) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.integral_sineDistance.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Analytic.Integral.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Integral

namespace Integrability
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => (ℝ × ℝ) → ℝ) (fun _ => Measure (ℝ × ℝ) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f μ => Integrable f μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℝ} (hp : 0 < p) (hpq : p < q) (x y : ℝ),
    R.readout () () (sineDistanceIntegrand p q x y) sineParameterMeasure

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (p := 1) (q := 2) (by norm_num) (by norm_num) 0 1

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hi : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) Measure.count :=
    Eq.mp (congrFun he Measure.count) (integrable_zero (ℝ × ℝ) ℝ Measure.count)
  have hfinite := (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp hi
  have hinfinite : ¬ IsFiniteMeasure (Measure.count : Measure (ℝ × ℝ)) := by
    rw [not_isFiniteMeasure_iff, Measure.count_univ]
    simp
  exact hinfinite hfinite

def source_registration : Registration arena (type_of% @integrable_sineDistance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integrable_sineDistance, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@integrable_sineDistance) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.integrable_sineDistance.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Analytic.Integrability.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f μ => Integrable f μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Integrability

end Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Analytic
