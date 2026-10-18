/- SOURCE_ONLY_UNCOMPILED. Three live owner accessor attempts; no accepted audit evidence. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Reg.Support.SingleDependentReadout
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.OwnerAccessors
open _root_.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

private theorem density_two_lt_one : archimedeanJumpDensity 2 < archimedeanJumpDensity 1 := by
  have hD1 : 0 < 1 - Real.exp (-2 : ℝ) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hD12 : 1 - Real.exp (-2 : ℝ) ≤ 1 - Real.exp (-4 : ℝ) := by
    have h := Real.exp_le_exp.mpr (by norm_num : (-4 : ℝ) ≤ -2)
    linarith
  have hD2 : 0 < 1 - Real.exp (-4 : ℝ) := hD1.trans_le hD12
  have hN : Real.exp (-1 : ℝ) < Real.exp (-1 / 2 : ℝ) :=
    Real.exp_lt_exp.mpr (by norm_num)
  have h := (div_lt_div_of_pos_right hN hD2).trans_le
    (div_le_div_of_nonneg_left (Real.exp_pos (-1 / 2 : ℝ)).le hD1 hD12)
  simpa [archimedeanJumpDensity] using h

namespace Nonnegative
abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ}, 0 < x → 0 ≤ R.readout () () x
def actual : Realization signature :=
  realize signature (fun _ _ x => archimedeanJumpDensity x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h (x := 1) (by norm_num)
  change (0 : ℝ) ≤ -1 at h1
  norm_num at h1
def registration : Registration arena (∀ {x : ℝ}, 0 < x → 0 ≤ archimedeanJumpDensity x) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@archimedeanJumpDensity_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change archimedeanJumpDensity 1 ≠ archimedeanJumpDensity 2
    exact ne_of_gt density_two_lt_one

-- The selected raw nonnegative inequality has binders x=0 and hx=1.
-- Its last argument is exactly archimedeanJumpDensity x; no normalized statement is selected.
def sourceRegistration : Contract.Registration
    (@_root_.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity_nonneg)
    (type_of% (realize signature (fun _ _ x => archimedeanJumpDensity x) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.OwnerAccessors.Nonnegative.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.OwnerAccessors.Nonnegative.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => archimedeanJumpDensity x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Nonnegative

namespace LevyIntegral
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def increment (t : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
    (Complex.digamma (1 / 4)).re
def actual : Realization signature :=
  realize signature (fun _ t x => 2 * archimedeanJumpDensity x * (1 - Real.cos (t * x)))
    (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, (∫ x : ℝ in Ioi 0, R.readout () t x) = increment t
def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.exp (-x)) (fun e => nomatch e)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  have hi : (∫ x : ℝ in Ioi 0, Real.exp (-x)) = 1 := by
    simpa using (integral_exp_neg_mul_cos (c := 1) (t := 0) (by norm_num))
  change (∫ x : ℝ in Ioi 0, Real.exp (-x)) = increment 0 at h0
  rw [hi] at h0
  norm_num [increment] at h0
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, Real.pi, 2 * Real.pi, ?_⟩
  have hp : 0 < archimedeanJumpDensity Real.pi := by
    unfold archimedeanJumpDensity
    exact div_pos (Real.exp_pos _)
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])))
  change 2 * archimedeanJumpDensity Real.pi * (1 - Real.cos (1 * Real.pi)) ≠
    2 * archimedeanJumpDensity (2 * Real.pi) * (1 - Real.cos (1 * (2 * Real.pi)))
  simp only [one_mul, Real.cos_pi, Real.cos_two_pi]
  nlinarith
def registration : Registration arena
    (∀ t : ℝ, (∫ x : ℝ in Ioi 0,
      2 * archimedeanJumpDensity x * (1 - Real.cos (t * x))) = increment t) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨levy_integral_eq_digamma, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence
-- No Contract record is asserted: the exact raw integral-lambda binding and
-- occurrence reconstruction still need compiler evidence against the owner accessor.
end LevyIntegral

namespace LevyIntegrability
abbrev signature := LevyIntegral.signature
def actual : Realization signature := LevyIntegral.actual
def arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, IntegrableOn (fun x => R.readout () t x) (Ioi 0)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioi (0 : ℝ))) := h 0
  have hf : IsFiniteMeasure (volume.restrict (Ioi (0 : ℝ))) :=
    (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp h0
  letI := hf
  have hfinite := measure_lt_top (volume.restrict (Ioi (0 : ℝ))) Set.univ
  simpa using hfinite
def registration : Registration arena
    (∀ t : ℝ, IntegrableOn
      (fun x : ℝ => 2 * archimedeanJumpDensity x * (1 - Real.cos (t * x))) (Ioi 0)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨levy_integrableOn, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := LevyIntegral.actual_dependence
-- No Contract record is asserted: IntegrableOn's actual implicit measure and
-- function-lambda source coordinates have not been obtained from compiled binding evidence.
end LevyIntegrability
end Reg.D5.S3.Weil.ZetaGamma.FormCore.OwnerAccessors
