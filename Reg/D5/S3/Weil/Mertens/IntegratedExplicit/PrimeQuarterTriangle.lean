import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle
open scoped Topology

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ k => primeTriangleSum ((k : ℝ) / 4)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := RiemannHypothesis ↔ ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k : ℕ in atTop,
    2 * ((k : ℝ) / 4) * Real.log 2 - A * Real.sqrt ((k : ℝ) / 4) ≤
      V.readout () () k

private def changed : Realization signature := by
  classical
  exact realize signature
    (fun _ _ k => if RiemannHypothesis then 0 else 2 * ((k : ℝ) / 4) * Real.log 2)
    (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 4, ?_⟩
  change primeTriangleSum ((0 : ℕ) / 4) ≠ primeTriangleSum ((4 : ℕ) / 4)
  have h₀ : primeTriangleSum 0 = 0 := by simp [primeTriangleSum]
  have h₁ : 0 < primeTriangleSum 1 := by
    unfold primeTriangleSum
    have hprimes : (Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊4 * (1 : ℝ)⌋₊).filter Nat.Prime = {2, 3} := by
      norm_num
      decide
    rw [hprimes]
    norm_num [triangleWeight, Finset.sum_insert, Finset.sum_singleton]
    positivity
  norm_num at *
  exact ne_of_lt (by simpa [h₀] using h₁)

private theorem changed_fails : ¬ arena.Law changed := by
  classical
  intro h
  by_cases hRH : RiemannHypothesis
  · obtain ⟨A, hA, hlate⟩ := h.mp hRH
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hscale : Tendsto (fun k : ℕ => (k : ℝ) / 4) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop
    have hroot := Real.tendsto_sqrt_atTop.comp hscale
    obtain ⟨k, hk, hsmall⟩ := (hlate.and
      (hroot.eventually_ge_atTop (A / Real.log 2 + 1))).exists
    change 2 * ((k : ℝ) / 4) * Real.log 2 - A * Real.sqrt ((k : ℝ) / 4) ≤
      (if RiemannHypothesis then 0 else 2 * ((k : ℝ) / 4) * Real.log 2) at hk
    rw [if_pos hRH] at hk
    let t := Real.sqrt ((k : ℝ) / 4)
    have ht : 0 < t := by
      change A / Real.log 2 + 1 ≤ t at hsmall
      linarith [div_nonneg hA hlog.le]
    have hsq : t ^ 2 = (k : ℝ) / 4 := Real.sq_sqrt (by positivity)
    have hcoef : A < 2 * t * Real.log 2 := by
      have hbig : A / Real.log 2 < 2 * t := by
        change A / Real.log 2 + 1 ≤ t at hsmall
        linarith
      exact (div_lt_iff₀ hlog).mp hbig
    have hmul := mul_lt_mul_of_pos_right hcoef ht
    change 2 * ((k : ℝ) / 4) * Real.log 2 - A * t ≤ 0 at hk
    rw [← hsq] at hk
    nlinarith only [hk, hmul]
  · apply hRH
    apply h.mpr
    refine ⟨0, le_rfl, Filter.Eventually.of_forall fun k => ?_⟩
    change 2 * ((k : ℝ) / 4) * Real.log 2 - 0 * Real.sqrt ((k : ℝ) / 4) ≤
      (if RiemannHypothesis then 0 else 2 * ((k : ℝ) / 4) * Real.log 2)
    rw [if_neg hRH, zero_mul, sub_zero]

def evidence : Registration arena (type_of% @rh_iff_eventual_prime_triangle_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rh_iff_eventual_prime_triangle_lower, changed, changed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_eventual_prime_triangle_lower) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle.rh_iff_eventual_prime_triangle_lower
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => primeTriangleSum ((k : ℝ) / 4))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle
