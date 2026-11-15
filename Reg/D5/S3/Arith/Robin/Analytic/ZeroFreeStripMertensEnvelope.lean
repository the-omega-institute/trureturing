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

end Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
