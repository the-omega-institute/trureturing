/- Mirrored audits for the two actual-H6 theta laws.
All original telescopes and clauses remain; each law changes one data occurrence.
-/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
import Reg.Support.DependentFamily
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess

open MeasureTheory Set Filter
open scoped ENNReal Topology
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private theorem zero_h6 : originalPhysicalH6 (fun _ : ℝ => (0 : ℂ)) := by
  exact ⟨MemLp.zero', by simp⟩

/- This interval is contained in x>pi and lies strictly below 4*pi. Its
H6 membership and finite excess are proved before its integral is observed.
The interval witness proof is reused from the weighted-physical registration
source. -/
private def indicatorInput : ℝ → ℂ :=
  (Ioc (2 * Real.pi) (3 * Real.pi)).indicator (fun _ => (1 : ℂ))

private theorem indicator_weight_mul (w : ℝ → ℝ) :
    (fun x : ℝ => w x * ‖indicatorInput x‖ ^ 2) =
      (Ioc (2 * Real.pi) (3 * Real.pi)).indicator w := by
  funext x
  by_cases hx : x ∈ Ioc (2 * Real.pi) (3 * Real.pi) <;>
    simp [indicatorInput, hx]

private theorem indicator_h6 : originalPhysicalH6 indicatorInput := by
  have hlp : MemLp indicatorInput 2 volume := by
    change MemLp ((Ioc (2 * Real.pi) (3 * Real.pi)).indicator
      (fun _ : ℝ => (1 : ℂ))) 2 volume
    apply memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet (1 : ℂ)
    exact Or.inr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hc : Continuous (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ)) := by fun_prop
  have hi : IntegrableOn (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ))
      (Ioc (2 * Real.pi) (3 * Real.pi)) := hc.integrableOn_Ioc
  have hid : Integrable
      (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) * ‖indicatorInput x‖ ^ 2) volume := by
    rw [indicator_weight_mul]
    exact hi.integrable_indicator measurableSet_Ioc
  exact ⟨hlp.restrict (Ioi Real.pi), hid.restrict⟩

private theorem indicator_excess_integrable :
    IntegrableOn
      (fun x : ℝ => ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2)
      (Ioi Real.pi) := by
  have hU := indicator_h6
  have hs := (memLp_two_iff_integrable_sq_norm hU.1.aestronglyMeasurable).1 hU.1
  refine (hU.2.sub hs).congr (Eventually.of_forall fun x => ?_)
  change (x / Real.pi) ^ (6 : ℕ) * ‖indicatorInput x‖ ^ 2 - ‖indicatorInput x‖ ^ 2 =
    ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2
  ring

private theorem excess_weight_pos {x : ℝ} (hx : Real.pi < x) :
    0 < (x / Real.pi) ^ (6 : ℕ) - 1 := by
  have hr : 1 < x / Real.pi :=
    (lt_div_iff₀ Real.pi_pos).2 (by simpa using hx)
  exact sub_pos.mpr (one_lt_pow₀ hr (by decide : (6 : ℕ) ≠ 0))

private theorem indicator_excess_pos :
    0 < ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi Real.pi)]
      (fun x : ℝ => ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (excess_weight_pos hx).le (sq_nonneg _)
  have hsupp :
      Function.support
          (fun x : ℝ => ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2) ∩
        Ioi Real.pi = Ioc (2 * Real.pi) (3 * Real.pi) := by
    ext x
    constructor
    · intro hx
      by_contra hnot
      have hz : indicatorInput x = 0 := by simp [indicatorInput, hnot]
      exact hx.1 (by simp [hz])
    · intro hx
      have hxpi : Real.pi < x := by
        have hxlo := hx.1
        linarith [Real.pi_pos]
      refine ⟨?_, hxpi⟩
      change ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2 ≠ 0
      simpa [indicatorInput, hx] using (excess_weight_pos hxpi).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg indicator_excess_integrable,
    hsupp, Real.volume_Ioc]
  exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])

private theorem indicator_midpoint_mem :
    5 * Real.pi / 2 ∈ Ioc (2 * Real.pi) (3 * Real.pi) := by
  constructor <;> linarith [Real.pi_pos]

private theorem not_ae_false :
    ¬ (∀ᵐ x : ℝ ∂volume.restrict (Ioi Real.pi), False) := by
  intro h
  have hz : (volume.restrict (Ioi Real.pi)) Set.univ = 0 := by
    simpa using (ae_iff.mp h)
  rw [Measure.restrict_apply_univ, Real.volume_Ioi] at hz
  exact ENNReal.top_ne_zero hz

namespace Excess

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature
    (fun _ _ F => ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/- The first two clauses and the left excess integral remain literal.
Only the source excess integral on the final RHS is observed. -/
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℂ) (hF : originalPhysicalH6 F),
    originalPhysicalH6 (fullTheta F) ∧
    Integrable
      (fun x : ℝ => ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) ∧
    (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2) ≤
      (∑' j : ℕ, ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹) ^ 2 *
        R.readout () () F

private theorem source_reconstruction :
    (type_of% (@actual_h6_fullTheta_excess_bound)) ↔ arena.Law actual := Iff.rfl

private theorem cubic_sum_pos :
    0 < ∑' j : ℕ, ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹ := by
  have hs0 : Summable (fun n : ℕ => ((n : ℝ) ^ (3 : ℕ))⁻¹) :=
    (Real.summable_nat_pow_inv (p := 3)).2 (by norm_num)
  have hs : Summable (fun j : ℕ => ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹) :=
    (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (3 : ℕ))⁻¹) 1).2 hs0
  exact hs.tsum_pos (fun j => by positivity) 0 (by norm_num)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad : (0 : ℝ) ≤
      (∑' j : ℕ, ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹) ^ 2 * (-1 : ℝ) := by
    simpa [rejected, realize, fullTheta, physicalTerm] using
      (hall (fun _ : ℝ => (0 : ℂ)) zero_h6).2.2
  have hpos := sq_pos_of_pos cubic_sum_pos
  nlinarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), indicatorInput, ?_⟩
  change (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖(0 : ℂ)‖ ^ 2) ≠
    ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2
  simpa using (ne_of_lt indicator_excess_pos)

private def familyRegistration : Registration arena
    (type_of% (@actual_h6_fullTheta_excess_bound)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_h6_fullTheta_excess_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Selector: F=0,hF=1. Two And-right edges,
then the inequality RHS and the multiplication RHS. No integral binder
is entered. All original parameters are still universally quantified. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_h6_fullTheta_excess_bound) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.actual_h6_fullTheta_excess_bound.__information_unit
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ F => ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Excess

namespace Summability

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ F => physicalTerm F) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

/- The complete original H6-to-almost-everywhere summability law. The
selected operand is the partial application physicalTerm F inside the
original mode lambda; neither the AE filter nor Summable is replaced. -/
private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℂ) (hF : originalPhysicalH6 F),
    ∀ᵐ x : ℝ ∂volume.restrict (Ioi Real.pi),
      Summable (fun j : ℕ => R.readout () () F j x)

private theorem source_reconstruction :
    (type_of% (@actual_h6_physicalTerm_summable_ae)) ↔ arena.Law actual := Iff.rfl

private theorem constant_modes_not_summable :
    ¬ Summable (fun _ : ℕ => (1 : ℂ)) := by
  intro hs
  have hz : (1 : ℂ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  exact one_ne_zero hz

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  apply not_ae_false
  filter_upwards [hall (fun _ : ℝ => (0 : ℂ)) zero_h6] with x hx
  apply constant_modes_not_summable
  simpa only [rejected, realize] using hx

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), indicatorInput, ?_⟩
  change physicalTerm (fun _ : ℝ => (0 : ℂ)) ≠ physicalTerm indicatorInput
  intro heq
  have hpoint := congrFun (congrFun heq 0) (5 * Real.pi / 2)
  have hmid : indicatorInput (5 * Real.pi / 2) = 1 :=
    Set.indicator_of_mem indicator_midpoint_mem _
  norm_num only [physicalTerm, Nat.zero_add, Nat.cast_one, one_pow, one_mul,
    mul_zero, hmid] at hpoint

private def familyRegistration : Registration arena
    (type_of% (@actual_h6_physicalTerm_summable_ae)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_h6_physicalTerm_summable_ae, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Selector: F=0,hF=1,AE x=2,mode j=3.
Filter.Eventually's predicate is fn/arg; enter its x body, then fn/arg
selects Summable's function before its explicit default summation filter.
Enter its j body. Two fn edges select exactly physicalTerm F,
whose output is a whole mode family and has no x or j dependency.
Thus coordinates are empty. This is lexical-state mode, not the separate
single-data-argument functionOperand mode. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_h6_physicalTerm_summable_ae) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.actual_h6_physicalTerm_summable_ae.__information_unit
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ F => physicalTerm F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Summability


end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
