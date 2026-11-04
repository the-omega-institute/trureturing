/- The complete original H6 law retains both product domains and both bounds.
Only the excess integral on the first bound's right-hand side is selected. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiWeightedPhysicalMoments
import Reg.Support.DependentFamily
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiWeightedPhysicalMoments

open MeasureTheory Set Filter
open scoped ENNReal Topology
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open _root_.D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
    (fun _ _ U =>
      ∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖U x‖ ^ 2)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : ℝ → ℂ) (hU : originalPhysicalH6 U),
    IntegrableOn (fun x : ℝ =>
      ((x ^ (5 / 4 : ℝ) - Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) * U x) (Ioi Real.pi) ∧
      IntegrableOn (fun x : ℝ => (Real.log (x / Real.pi) : ℂ) * U x) (Ioi Real.pi) ∧
      ‖∫ x : ℝ in Ioi Real.pi,
        ((x ^ (5 / 4 : ℝ) - Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) * U x‖ ^ 2 ≤
        (3 / 40 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * R.readout () () U ∧
      ‖∫ x : ℝ in Ioi Real.pi, (Real.log (x / Real.pi) : ℂ) * U x‖ ^ 2 ≤
        (3 / 160 : ℝ) * Real.pi *
          (∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖U x‖ ^ 2)

private theorem source_reconstruction :
    (type_of% (@actual_h6_weighted_physical_moments)) ↔ arena.Law actual := Iff.rfl

private theorem zero_h6 : originalPhysicalH6 (fun _ : ℝ => (0 : ℂ)) := by
  exact ⟨MemLp.zero', by simp⟩

private theorem actual_law : arena.Law actual :=
  @actual_h6_weighted_physical_moments

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad : (0 : ℝ) ≤ (3 / 40 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * (-1 : ℝ) := by
    simpa [rejected, realize] using
      (hall (fun _ : ℝ => (0 : ℂ)) zero_h6).2.2.1
  have hpos : 0 < (3 / 40 : ℝ) * Real.pi ^ (7 / 2 : ℝ) := by positivity
  nlinarith

/- A genuine compactly supported physical state. Its H6 and excess
integrability are proved below before positivity of its actual integral.
No value of a divergent totalized integral is used as a witness. -/
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
  have hd := hU.2.sub hs
  change Integrable
    (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) * ‖indicatorInput x‖ ^ 2 -
      ‖indicatorInput x‖ ^ 2) (volume.restrict (Ioi Real.pi)) at hd
  simpa only [IntegrableOn, sub_mul, one_mul] using hd

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

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), indicatorInput, ?_⟩
  change (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖(0 : ℂ)‖ ^ 2) ≠
    ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2
  simpa using (ne_of_lt indicator_excess_pos)

private def familyRegistration : Registration arena
    (type_of% (@actual_h6_weighted_physical_moments)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The complete telescope is U=0, hU=1, both explicit, with no parameters.
Two And-right edges skip the L1 clauses; fn/arg selects the first estimate.
The final two arg edges select its RHS and final multiplication operand.
The second excess occurrence remains outside the intervention. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_h6_weighted_physical_moments) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma.actual_h6_weighted_physical_moments.__information_unit
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
    (fun _ _ U =>
      ∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖U x‖ ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiWeightedPhysicalMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiWeightedPhysicalMoments
