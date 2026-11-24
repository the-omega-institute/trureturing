import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow
open scoped Topology

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => primeTriangleSum x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ {b : ℝ}, 1 < b → (RiemannHypothesis ↔ ∃ A : ℝ, 0 ≤ A ∧
    ∃ᶠ X : ℝ in atTop, ∀ x ∈ Icc X (X ^ b),
      2 * x * Real.log 2 - A * Real.sqrt x ≤ V.readout () () x)

private def changed : Realization signature := by
  classical
  exact realize signature
    (fun _ _ x => if RiemannHypothesis then 0 else 2 * x * Real.log 2)
    (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change primeTriangleSum 0 ≠ primeTriangleSum 1
  have h₀ : primeTriangleSum 0 = 0 := by simp [primeTriangleSum]
  have h₁ : 0 < primeTriangleSum 1 := by
    unfold primeTriangleSum
    have hprimes : (Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊4 * (1 : ℝ)⌋₊).filter Nat.Prime = {2, 3} := by
      norm_num
      decide
    rw [hprimes]
    norm_num [triangleWeight, Finset.sum_insert, Finset.sum_singleton]
    positivity
  exact ne_of_lt (by simpa [h₀] using h₁)

private theorem left_endpoint {Y : ℝ} (hY : 2 ≤ Y) : Y ∈ Icc Y (Y ^ (2 : ℝ)) := by
  rw [Real.rpow_two]
  exact ⟨le_rfl, by nlinarith⟩

private theorem changed_fails : ¬ arena.Law changed := by
  classical
  intro H
  have h := H (b := 2) (by norm_num)
  by_cases hRH : RiemannHypothesis
  · obtain ⟨A, hA, hlate⟩ := h.mp hRH
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    obtain ⟨X, hwin, hX, hsmall⟩ :=
      (hlate.and_eventually ((eventually_ge_atTop (2:ℝ)).and
        (Real.tendsto_sqrt_atTop.eventually_ge_atTop (A / Real.log 2 + 1)))).exists
    have hk := hwin X (left_endpoint hX)
    change 2 * X * Real.log 2 - A * Real.sqrt X ≤
      (if RiemannHypothesis then 0 else 2 * X * Real.log 2) at hk
    rw [if_pos hRH] at hk
    let t := Real.sqrt X
    have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have hsq : t ^ 2 = X := Real.sq_sqrt (by linarith)
    have hcoef : A < 2 * t * Real.log 2 := by
      have hbig : A / Real.log 2 < 2 * t := by
        change A / Real.log 2 + 1 ≤ t at hsmall
        linarith
      exact (div_lt_iff₀ hlog).mp hbig
    have hmul := mul_lt_mul_of_pos_right hcoef ht
    change 2 * X * Real.log 2 - A * t ≤ 0 at hk
    rw [← hsq] at hk
    nlinarith only [hk, hmul]
  · apply hRH
    apply h.mpr
    refine ⟨0, le_rfl, (Filter.Eventually.of_forall fun X x _ => ?_).frequently⟩
    change 2 * x * Real.log 2 - 0 * Real.sqrt x ≤
      (if RiemannHypothesis then 0 else 2 * x * Real.log 2)
    rw [if_neg hRH, zero_mul, sub_zero]

def evidence : Registration arena (type_of% @rh_iff_frequently_prime_triangle_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rh_iff_frequently_prime_triangle_lower, changed, changed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_frequently_prime_triangle_lower) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow.rh_iff_frequently_prime_triangle_lower
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => primeTriangleSum x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg", "fn", "arg", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow
