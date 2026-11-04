import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore
import Reg.Support.SingleDependentReadout

/-! Faithful dependent-family audit of the weighted coefficient core. -/

open RHGaussianDilationCore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℝ (fun _ => ℝ → GaussianCoeffSpace) (fun _ => Submodule ℝ GaussianCoeffSpace)

def actual : Realization signature :=
  realize signature (fun _ r f => positiveCurveSpan f r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (z c : ℕ → ℝ) (hz0 : z 0 = 1) (hz : ∀ n, |z n| ≤ 1)
    (hc0 : ∀ n, c n ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C * (9 / 2 : ℝ) ^ n)
    (d : ℝ → ℕ → ℝ) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 36)
    (hcharge : ∀ t, 0 < t → t < r → HasSum (fun n => z n * d t n) 0)
    (htail : ∀ t, 0 < t → t < r → ∀ n : ℕ, n ≠ 0 → d t n = c n * t ^ n),
    ∃ f : ℝ → GaussianCoeffSpace,
      (∀ t, 0 < t → t < r → ∀ n, f t n = coeffWeight n * d t n) ∧
      R.readout () r f = (coeffCharge (gaussianChargeVector z hz)).ker

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let z : ℕ → ℝ := fun n => if n = 0 then 1 else 0
  let c : ℕ → ℝ := fun _ => 1
  let d : ℝ → ℕ → ℝ := fun t n => if n = 0 then 0 else t ^ n
  have hz : ∀ n, |z n| ≤ 1 := by intro n; dsimp [z]; split_ifs <;> norm_num
  have hc : ∀ n, |c n| ≤ (1 : ℝ) * (9 / 2 : ℝ) ^ n := by
    intro n
    simpa only [c, abs_one, one_mul] using
      one_le_pow₀ (n := n) (by norm_num : (1 : ℝ) ≤ 9 / 2)
  have hd : ∀ t : ℝ, HasSum (fun n => z n * d t n) 0 := by
    intro t
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
    funext n
    by_cases hn : n = 0 <;> simp [z, d, hn]
  obtain ⟨f, _, hker⟩ := h z c (by simp [z]) hz (by intro n; norm_num [c])
    (C := 1) (by norm_num) hc d (r := 1 / 36) (by norm_num) le_rfl
    (fun t _ _ => hd t) (by intro t _ _ n hn; simp [d, c, hn])
  have hmem : coeffBasis 1 ∈ (coeffCharge (gaussianChargeVector z hz)).ker := by
    change coeffCharge (gaussianChargeVector z hz) (coeffBasis 1) = 0
    simp [coeffCharge, coeffBasis, innerSL_apply_apply, lp.inner_single_right,
      gaussianChargeVector, z]
  change (⊥ : Submodule ℝ GaussianCoeffSpace) =
    (coeffCharge (gaussianChargeVector z hz)).ker at hker
  rw [← hker] at hmem
  have hzero : coeffBasis 1 = 0 := by simpa using hmem
  have hc0 := congrArg (fun w : GaussianCoeffSpace => w 1) hzero
  norm_num [coeffBasis] at hc0

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1 / 36, (fun _ => 0), (fun _ => coeffBasis 0), ?_⟩
  change positiveCurveSpan (fun _ => 0) (1 / 36) ≠
    positiveCurveSpan (fun _ => coeffBasis 0) (1 / 36)
  intro heq
  have hmem : coeffBasis 0 ∈ positiveCurveSpan (fun _ => coeffBasis 0) (1 / 36) :=
    (Submodule.span ℝ ((fun _ : ℝ => coeffBasis 0) '' Set.Ioo 0 (1 / 36))).le_topologicalClosure
      (Submodule.subset_span ⟨1 / 72, by norm_num, rfl⟩)
  rw [← heq] at hmem
  have hbot : positiveCurveSpan (fun _ => 0) (1 / 36) ≤
      (⊥ : Submodule ℝ GaussianCoeffSpace) := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨t, _, rfl⟩
      exact Submodule.zero_mem _
    · exact isClosed_singleton
  have hzero : coeffBasis 0 = 0 := by simpa using hbot hmem
  have hc0 := congrArg (fun w : GaussianCoeffSpace => w 0) hzero
  norm_num [coeffBasis] at hc0

def family : Registration arena (type_of% weighted_charge_kernel_core_of_scalar_curve) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_charge_kernel_core_of_scalar_curve, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    weighted_charge_kernel_core_of_scalar_curve (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore.core_unit
  realizationName := `Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore.family
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
    (fun _ r f => positiveCurveSpan f r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore
    definition := none
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore
