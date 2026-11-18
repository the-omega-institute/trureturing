import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! The complete strip-conditional source law and its audit obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (B)

namespace Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => B x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 / 2 →
    (∀ rho : ℂ, _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero rho → rho.re ≤ 1 - alpha) →
    ∃ C T : ℝ, 0 ≤ C ∧ Real.exp 1 ≤ T ∧ ∀ x : ℝ, T ≤ x →
      |V.readout () () x| ≤ C / (Real.rpow x alpha * Real.log x)

private theorem actual_law : arena.Law actual := @actual_B_critical_strip_envelope

private theorem source_bridge :
    (type_of% (@actual_B_critical_strip_envelope)) ↔ arena.Law actual := Iff.rfl

private abbrev PositiveUniformStrip : Prop :=
  ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ 1 / 2 ∧
    ∀ rho : ℂ, _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero rho → rho.re ≤ 1 - alpha

private theorem law_of_no_positive_strip (h : ¬ PositiveUniformStrip)
    (V : Realization signature) : arena.Law V := by
  intro alpha ha hhalf hstrip
  exact (h ⟨alpha, ha, hhalf, hstrip⟩).elim

private theorem rejected_family_requires_positive_strip {V : Realization signature}
    (h : ¬ arena.Law V) : PositiveUniformStrip := by
  by_contra hn
  exact h (law_of_no_positive_strip hn V)

/- The full source law and its equivalence bridge do not complete a four-slot
   audit. Variation requires a rejected whole family. The preceding proof shows
   that any such rejection implies the existence of a positive uniform strip:
   there is alpha in (0,1/2] bounding every actual nontrivial zero by 1-alpha.
   This existence statement is not identified with RH. Sensitivity and actual
   observational dependence also remain obligations; no Contract.Registration
   or validated audit is asserted here. -/

namespace Quadratic

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ _ x => 8 * ((Chebyshev.theta x - x) / x) ^ 2 / Real.log x)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ}, Real.exp 2 ≤ x → x / 2 ≤ Chebyshev.theta x →
    |_root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.N x| ≤ V.readout () () x

private theorem source_bridge :
    (type_of% (@nonlinear_quadratic)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := _root_.D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2.eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨x, hxexp, hx0, htheta⟩ :=
    (eventually_ge_atTop (Real.exp 2) |>.and
      ((eventually_gt_atTop (0 : ℝ)).and hp)).exists
  have ht : x / 2 ≤ Chebyshev.theta x := by
    have := (lt_div_iff₀ hx0).mp htheta
    linarith only [this]
  have hb := h hxexp ht
  change |_root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.N x| ≤ -1 at hb
  linarith only [hb, abs_nonneg (_root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.N x)]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  have ht : Chebyshev.theta 2 = Real.log 2 := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    norm_num [Nat.primesLE, Nat.primesBelow, Finset.sum_filter, Finset.sum_range_succ]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : Real.log 2 - 2 ≠ 0 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [this]
  change 8 * ((Chebyshev.theta 0 - 0) / 0) ^ 2 / Real.log 0 ≠
    8 * ((Chebyshev.theta 2 - 2) / 2) ^ 2 / Real.log 2
  simp only [div_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.log_zero, ht]
  exact ne_of_lt (div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero
    (div_ne_zero hn (by norm_num)))) hl)

def family : Registration arena (type_of% (@nonlinear_quadratic)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨@nonlinear_quadratic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nonlinear_quadratic) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope.nonlinear_quadratic.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope.Quadratic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => 8 * ((Chebyshev.theta x - x) / x) ^ 2 / Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Quadratic

namespace ThetaPower

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Chebyshev.theta x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x ^ (3 : ℕ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {β C X : ℝ}, (1 / 2 : ℝ) < β →
    (∀ x : ℝ, X ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ β) →
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ x : ℝ, R ≤ x →
      |V.readout () () x - x| ≤ K * x ^ β

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hpsi : ∀ x : ℝ, (2 : ℝ) ≤ x →
      |Chebyshev.psi x - x| ≤ (Real.log 4 + 5) * x ^ (1 : ℝ) := by
    intro x hx
    rw [Real.rpow_one]
    apply abs_le.mpr
    have hp := Chebyshev.psi_le_const_mul_self (show 0 ≤ x by linarith)
    have hn := Chebyshev.psi_nonneg x
    have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    constructor <;> nlinarith
  obtain ⟨K, R, hK, hR, hb⟩ := h (by norm_num : (1 / 2 : ℝ) < 1) hpsi
  let x : ℝ := max R (max K 4) + 1
  have hxR : R ≤ x := by dsimp [x]; linarith [le_max_left R (max K 4)]
  have hx4 : 4 ≤ x := by
    dsimp [x]
    linarith [le_max_right R (max K 4), le_max_right K 4]
  have hxK : K < x := by
    dsimp [x]
    linarith [(le_max_left K 4).trans (le_max_right R (max K 4))]
  have hh := hb x hxR
  change |x ^ (3 : ℕ) - x| ≤ K * x ^ (1 : ℝ) at hh
  rw [Real.rpow_one] at hh
  have hlinear := (le_abs_self (x ^ (3 : ℕ) - x)).trans hh
  have hmul : K * x < x * x := mul_lt_mul_of_pos_right hxK (by linarith)
  have hcube : x * x + x < x ^ (3 : ℕ) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ x - 4)]
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  change Chebyshev.theta 0 ≠ Chebyshev.theta 2
  simp only [Chebyshev.theta_zero]
  exact Ne.symm (Chebyshev.theta_eq_zero_iff.not.mpr (by norm_num))

def family : Registration arena (type_of% (@theta_power_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@theta_power_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@theta_power_bound) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope.theta_power_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope.ThetaPower.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms theta_power_bound
#print axioms family

end ThetaPower

end Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
