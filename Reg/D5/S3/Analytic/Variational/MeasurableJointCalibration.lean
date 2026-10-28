import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Variational.MeasurableJointCalibration
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Reg.Support.SingleDependentReadout

/-! Source-bound measurable integral and calibration readouts. -/
open Set MeasureTheory
open scoped ContDiff
open _root_.D5.S3.Analytic.Variational.MeasurableJointCalibration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.Variational.MeasurableJointCalibration

abbrev functionSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def functionActual : Realization functionSignature :=
  realize functionSignature (fun _ u x => u x) (fun e => nomatch e)
def functionBad : Realization functionSignature :=
  realize functionSignature (fun _ _ x => (x - 1)⁻¹) (fun e => nomatch e)

def integrabilityArena : Arena where
  signature := functionSignature
  Law R := ∀ {u : ℝ → ℝ},
    AEMeasurable u (volume.restrict (Icc (1 : ℝ) 2)) →
    (∃ c B : ℝ, 0 < c ∧
      ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2), c ≤ u x ∧ u x ≤ B) →
    IntervalIntegrable (R.readout () u) volume 1 2 ∧
    IntervalIntegrable (fun x => x / u x) volume 1 2 ∧
    IntervalIntegrable (fun x => (∫ s in (1 : ℝ)..x, u s) / u x ^ 2) volume 1 2

private theorem integrability_bad : ¬ integrabilityArena.Law functionBad := by
  intro h
  have hi := (h (u := fun _ => 1) aemeasurable_const
    ⟨1, 1, by norm_num, Filter.Eventually.of_forall (fun _ => ⟨le_rfl, le_rfl⟩)⟩).1
  change IntervalIntegrable (fun x : ℝ => (x - 1)⁻¹) volume 1 2 at hi
  simpa using hi

private theorem function_dependence : ObservationalDependence functionSignature functionActual := by
  intro i
  exact ⟨id, 0, 1, by norm_num [functionActual, realize]⟩

def integrabilityFamily : Registration integrabilityArena (type_of% @bounded_positive_integrability) where
  actual := functionActual
  bridge := Iff.rfl
  variation := ⟨@bounded_positive_integrability, functionBad, integrability_bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrabilityArena.Law functionActual functionBad integrability_bad
  dependence := function_dependence

def primitiveActual : Realization functionSignature :=
  realize functionSignature (fun _ u x => ∫ t in (1 : ℝ)..x, u t) (fun e => nomatch e)
def primitiveBad : Realization functionSignature :=
  realize functionSignature (fun _ u x => (∫ t in (1 : ℝ)..x, u t) + 1) (fun e => nomatch e)

def congruenceArena : Arena where
  signature := functionSignature
  Law R := ∀ {u v : ℝ → ℝ}, u =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] v →
    ∀ {x : ℝ}, x ∈ Icc (1 : ℝ) 2 → R.readout () u x = ∫ t in (1 : ℝ)..x, v t

private theorem congruence_bad : ¬ congruenceArena.Law primitiveBad := by
  intro h
  have he := h (u := fun _ => 1) Filter.EventuallyEq.rfl (x := 1) (by norm_num)
  norm_num [primitiveBad, realize] at he

private theorem primitive_dependence : ObservationalDependence functionSignature primitiveActual := by
  intro i
  exact ⟨fun _ => 1, 1, 2, by norm_num [primitiveActual, realize]⟩

def congruenceFamily : Registration congruenceArena (type_of% @primitive_congr) where
  actual := primitiveActual
  bridge := Iff.rfl
  variation := ⟨@primitive_congr, primitiveBad, congruence_bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    congruenceArena.Law primitiveActual primitiveBad congruence_bad
  dependence := primitive_dependence

abbrev energySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def energyActual : Realization energySignature :=
  realize energySignature (fun _ b e => b * e) (fun e => nomatch e)
def energyBad : Realization energySignature :=
  realize energySignature (fun _ b e => b * e + 1) (fun e => nomatch e)

def remainderArena : Arena where
  signature := energySignature
  Law R := ∀ {b : ℝ} {Z Q M N u U : ℝ → ℝ},
    Calibration b Z Q M N →
    AEMeasurable u (volume.restrict (Icc (1 : ℝ) 2)) →
    (∃ c B : ℝ, 0 < c ∧
      ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2), c ≤ u x ∧ u x ≤ B) →
    AbsolutelyContinuousOnInterval U 1 2 →
    MapsTo U (Icc (1 : ℝ) 2) (Icc (0 : ℝ) 1) →
    (∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2), HasDerivAt U (u x) x) →
    IntervalIntegrable (fun x => b * (x / u x) + U x / u x ^ 2) volume 1 2 →
    U 1 = 0 → Z 0 = 1 →
    IntervalIntegrable (defect u U Q) volume 1 2 ∧
    0 ≤ ∫ x in (1 : ℝ)..2, defect u U Q x ∧
    potential U Z M 2 - potential U Z M 1 +
        R.readout () b (∫ x in (1 : ℝ)..2, defect u U Q x) ≤
      ∫ x in (1 : ℝ)..2, b * (x / u x) + U x / u x ^ 2 ∧
    ((∫ x in (1 : ℝ)..2, defect u U Q x) = 0 →
      (∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2),
        Real.sqrt x / u x = (2 / 3 : ℝ) * Q (U x)) ∧
      ∀ x ∈ Icc (1 : ℝ) 2, Z (U x) = x * Real.sqrt x)

private def Z (r : ℝ) := (r + 1) * Real.sqrt (r + 1)
private def Q (r : ℝ) := 3 * Real.sqrt (r + 1) / 2
private def M (r : ℝ) := -4 * Real.sqrt (r + 1) + 2 * r / Real.sqrt (r + 1)
private def N (r : ℝ) := -r / ((r + 1) * Real.sqrt (r + 1))

private theorem calibration_witness : Calibration (-3) Z Q M N := by
  have hp (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : 0 < r + 1 := by linarith [hr.1]
  have hZ (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : HasDerivAt Z (Q r) r := by
    have hs := (Real.hasDerivAt_sqrt (ne_of_gt (hp r hr))).comp r ((hasDerivAt_id r).add_const 1)
    convert (((hasDerivAt_id r).add_const 1).mul hs) using 1
    · rfl
    · dsimp only [Q, Pi.mul_apply, Pi.add_apply, Function.comp_apply, id_eq]
      field_simp [ne_of_gt (Real.sqrt_pos.2 (hp r hr))]
      nlinarith [Real.sq_sqrt (hp r hr).le]
  refine ⟨?_, ?_, ?_, hZ, ?_, ?_⟩
  · intro r hr
    exact ((contDiffAt_id.add contDiffAt_const).mul
      ((Real.contDiffAt_sqrt (ne_of_gt (hp r hr))).comp r
        (contDiffAt_id.add contDiffAt_const)))
  · intro r hr
    have hs := (Real.contDiffAt_sqrt (n := ∞) (ne_of_gt (hp r hr))).comp r
      (contDiffAt_id.add contDiffAt_const)
    exact (contDiffAt_const.mul hs).add
      ((contDiffAt_const.mul contDiffAt_id).div hs (ne_of_gt (Real.sqrt_pos.2 (hp r hr))))
  · intro r hr
    exact (((Real.continuous_sqrt.continuousAt.comp
        (continuousAt_id.add continuousAt_const)).const_mul 3).div_const 2).continuousWithinAt
  · intro r hr
    have hs := (Real.hasDerivAt_sqrt (ne_of_gt (hp r hr))).comp r ((hasDerivAt_id r).add_const 1)
    have hd := (hs.const_mul (-4)).add
      (((hasDerivAt_id r).const_mul 2).div hs (ne_of_gt (Real.sqrt_pos.2 (hp r hr))))
    convert hd using 1
    · rfl
    · dsimp only [N, Pi.mul_apply, Pi.add_apply, Pi.div_apply, Function.comp_apply, id_eq]
      field_simp [ne_of_gt (hp r hr), ne_of_gt (Real.sqrt_pos.2 (hp r hr))]
      nlinarith [Real.sq_sqrt (hp r hr).le]
  · intro r hr
    have hroot := Real.sqrt_pos.2 (hp r hr)
    refine ⟨mul_pos (hp r hr) hroot, by dsimp [Q]; positivity, ?_, ?_⟩
    all_goals
      dsimp only [M, N, Z, Q]
      field_simp [ne_of_gt (hp r hr), ne_of_gt hroot]
      have hs := Real.sq_sqrt (hp r hr).le
      generalize Real.sqrt (r + 1) = t at *
      have hr : r = t ^ 2 - 1 := by linarith
      rw [hr]
      ring

private theorem remainder_bad : ¬ remainderArena.Law energyBad := by
  intro h
  have hU : AbsolutelyContinuousOnInterval (fun x : ℝ => x - 1) 1 2 :=
    (contDiff_id.sub contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  have hm : MapsTo (fun x : ℝ => x - 1) (Icc 1 2) (Icc 0 1) := by
    intro x hx; constructor <;> linarith [hx.1, hx.2]
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 1 2 :=
    continuous_id.intervalIntegrable _ _
  have hL : IntervalIntegrable (fun x : ℝ => -3 * (x / 1) + (x - 1) / 1 ^ 2) volume 1 2 := by
    simpa using (hi.const_mul (-3)).add (hi.sub intervalIntegrable_const)
  have he := (h calibration_witness aemeasurable_const
    ⟨1, 1, by norm_num, Filter.Eventually.of_forall (fun _ => ⟨le_rfl, le_rfl⟩)⟩ hU hm
    (Filter.Eventually.of_forall (fun x => by simpa using (hasDerivAt_id x).sub_const 1))
    hL (by norm_num) (by norm_num [Z])).2.2.1
  have hE : (∫ x in (1 : ℝ)..2, defect (fun _ => 1) (fun x => x - 1) Q x) = 0 := by
    have hd : defect (fun _ => 1) (fun x => x - 1) Q = fun _ => (0 : ℝ) := by
      funext x; dsimp [defect, Q]; rw [sub_add_cancel]; ring
    rw [hd, intervalIntegral.integral_zero]
  change potential (fun x => x - 1) Z M 2 - potential (fun x => x - 1) Z M 1 +
    (-3 * (∫ x in (1 : ℝ)..2, defect (fun _ => 1) (fun x => x - 1) Q x) + 1) ≤ _ at he
  rw [hE] at he
  have hV : potential (fun x => x - 1) Z M 2 - potential (fun x => x - 1) Z M 1 = -4 := by
    norm_num [potential, Z, M]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp [ne_of_gt (Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num))]
    nlinarith
  have hI : (∫ x in (1 : ℝ)..2, -3 * (x / 1) + (x - 1) / 1 ^ 2) = -4 := by
    simp only [div_one, one_pow]
    rw [intervalIntegral.integral_add (hi.const_mul (-3))
      (hi.sub intervalIntegrable_const),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hi intervalIntegrable_const]
    norm_num [integral_id]
  rw [hV, hI] at he
  norm_num at he

private theorem energy_dependence : ObservationalDependence energySignature energyActual := by
  intro i
  exact ⟨1, 0, 1, by norm_num [energyActual, realize]⟩

def remainderFamily : Registration remainderArena (type_of% @remainder) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨@remainder, energyBad, remainder_bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    remainderArena.Law energyActual energyBad remainder_bad
  dependence := energy_dependence


def integrabilityAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_positive_integrability) (Realization functionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Variational.MeasurableJointCalibration.integrabilityUnit
  realizationName := `Reg.D5.S3.Analytic.Variational.MeasurableJointCalibration.integrabilityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrabilityArena⟩
  objectArena := .source ⟨integrabilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrabilityArena ⟨integrabilityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize functionSignature (fun _ u x => u x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Variational.MeasurableJointCalibration
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def congruenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@primitive_congr) (Realization functionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Variational.MeasurableJointCalibration.congruenceUnit
  realizationName := `Reg.D5.S3.Analytic.Variational.MeasurableJointCalibration.congruenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨congruenceArena⟩
  objectArena := .source ⟨congruenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source congruenceArena ⟨congruenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize functionSignature (fun _ u x => ∫ t in (1 : ℝ)..x, u t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Variational.MeasurableJointCalibration
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def remainderAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@remainder) (Realization energySignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Variational.MeasurableJointCalibration.remainderUnit
  realizationName := `Reg.D5.S3.Analytic.Variational.MeasurableJointCalibration.remainderFamily
  realizationSource := none
  generated := false
  arena := .source ⟨remainderArena⟩
  objectArena := .source ⟨remainderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source remainderArena ⟨remainderFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize energySignature (fun _ b e => b * e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Variational.MeasurableJointCalibration
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Variational.MeasurableJointCalibration
