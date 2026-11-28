import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich
import Mathlib.Tactic.NormNum
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the sum of upper plane integrals. -/

namespace Reg.D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich

open _root_.D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped ContDiff

open Set
open Omega.Analysis.PeriodicSublevelSandwich (Plane closedCell openCell latticeVector)

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin n → Plane → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n upper => ∑ i : Fin n, ∫ u, upper i u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ {n : ℕ}
    (q : Plane) {F : Plane → Plane} (_hF : Continuous F)
    (_hperiod : ∀ (a : Fin 2 → ℤ) (x : Plane), F (latticeVector a + x) = F x)
    (z : Fin n → Plane) (_hz : Function.Injective z)
    (_hcell : ∀ i, z i ∈ openCell q)
    (_hzero : ∀ x ∈ closedCell q, F x = 0 ↔ ∃ i, x = z i)
    (A : Fin n → Plane ≃L[ℝ] Plane) (_hA : ∀ i, HasFDerivAt F (A i : Plane →L[ℝ] Plane) (z i))
    {η ρ σ : ℝ} (_hη : 0 < η) (_hη1 : η < 1)
    (_hρ : 0 < ρ) (_hρ' : ρ < (1 + η)⁻¹) (_hσ : (1 - η)⁻¹ < σ),
    let D := ∑ i, |LinearMap.det ((A i).toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹
    ∃ (lower upper : Fin n → Plane → ℝ) (δ : ℝ),
      0 < δ ∧
      (∀ i, ContDiff ℝ ∞ (lower i) ∧ ContDiff ℝ ∞ (upper i) ∧
        HasCompactSupport (lower i) ∧ HasCompactSupport (upper i)) ∧
      Real.pi * ρ ^ 2 * D ≤ ∑ i, ∫ u, lower i u ∧
      R.readout () n upper ≤ Real.pi * σ ^ 2 * D ∧
      ∀ ε ∈ Ioo 0 δ, ∀ x,
        (∑ i, ∑' a : Fin 2 → ℤ, lower i (ε⁻¹ • (latticeVector a + x - z i))) ≤
          (if ‖F x‖ < ε then 1 else 0) ∧
        (if ‖F x‖ < ε then 1 else 0) ≤
          (∑ i, ∑' a : Fin 2 → ℤ, upper i (ε⁻¹ • (latticeVector a + x - z i)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let v : Plane := WithLp.toLp 2 fun _ => 1
  have hv : v ≠ 0 := by
    intro he
    have hcoord := congrArg (fun x : Plane => x (0 : Fin 2)) he
    exact one_ne_zero (show (1 : ℝ) = 0 from hcoord)
  let z : Fin 0 → Plane := Fin.elim0
  let A : Fin 0 → Plane ≃L[ℝ] Plane := Fin.elim0
  have hzero : ∀ x ∈ closedCell 0, (fun _ : Plane => v) x = 0 ↔ ∃ i, x = z i := by
    intro x _
    constructor
    · exact fun he => (hv he).elim
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  obtain ⟨lower, upper, δ, _, _, _, hbound, _⟩ :=
    h (n := 0) 0 (F := fun _ => v) continuous_const (fun _ _ => rfl)
      z (fun {i} => Fin.elim0 i) (fun i => Fin.elim0 i) hzero A (fun i => Fin.elim0 i)
      (η := 1 / 2) (ρ := 1 / 2) (σ := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa [rejected, realize] using hbound
  exact (not_le_of_gt zero_lt_one) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let s := Metric.ball (0 : Plane) 1
  refine ⟨1, 0, fun _ => s.indicator 1, ?_⟩
  change (∑ i : Fin 1, ∫ u : Plane, (0 : Fin 1 → Plane → ℝ) i u) ≠
    ∑ i : Fin 1, ∫ u : Plane, s.indicator 1 u
  rw [Fin.sum_univ_one, Fin.sum_univ_one, integral_indicator_one Metric.isOpen_ball.measurableSet]
  have hvol : volume.real s = Real.pi := by
    simp [s, Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hvol]
  simpa only [Pi.zero_apply, integral_zero] using (ne_of_gt Real.pi_pos).symm

def source_registration : Registration arena (type_of% @periodic_test_sandwich) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨periodic_test_sandwich, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@periodic_test_sandwich) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n upper => ∑ i : Fin n, ∫ u, upper i u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg",
        "body", "arg", "body", "arg", "body", "arg", "arg",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 21
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich
