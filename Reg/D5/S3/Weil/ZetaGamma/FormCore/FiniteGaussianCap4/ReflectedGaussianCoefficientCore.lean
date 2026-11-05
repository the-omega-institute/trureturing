import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianCoefficientCore
import Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore

/-! Faithful dependent-family audit of the actual reflected coefficient core. -/

open RHGaussianDilationCore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open FiniteGaussianCap4.LaguerreSevenHalf

noncomputable section
namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianCoefficientCore

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ → GaussianCoeffSpace) (fun _ => Submodule ℝ GaussianCoeffSpace)

def actual : Realization signature :=
  realize signature (fun _ _ f => positiveCurveSpan f (1 / 36)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∃ f : ℝ → GaussianCoeffSpace,
    (∀ t : ℝ, 0 < t → t < 1 / 36 → ∀ n : ℕ,
      f t n = coeffWeight n * actualReflectedCurveCoefficient t n) ∧
    R.readout () () f = (coeffCharge actualCentralChargeVector).ker

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨f, _, hker⟩
  let a := actualCentralChargeVector
  have ha0 : a 0 = 1 := by
    have h0 : normalizedCentralMellin 0 ≠ 0 := by
      simpa only [Nat.mul_zero] using (normalizedCentralMellin_even_pos 0).ne'
    simp [a, actualCentralChargeVector, gaussianChargeVector, actualCentralZ,
      coeffWeight, h0]
  let v : GaussianCoeffSpace := coeffBasis 1 - a 1 • coeffBasis 0
  have hcharge : coeffCharge a v = 0 := by
    simp only [v, map_sub, map_smul]
    simp [coeffCharge, coeffBasis, innerSL_apply_apply, lp.inner_single_right, ha0]
  have hmem : v ∈ (coeffCharge actualCentralChargeVector).ker := hcharge
  change (⊥ : Submodule ℝ GaussianCoeffSpace) =
    (coeffCharge actualCentralChargeVector).ker at hker
  rw [← hker] at hmem
  have hvzero : v = 0 := by simpa using hmem
  have hcoord := congrArg (fun w : GaussianCoeffSpace => w 1) hvzero
  change coeffBasis 1 1 - a 1 * coeffBasis 0 1 = 0 at hcoord
  norm_num [coeffBasis] at hcoord

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => coeffBasis 0), ?_⟩
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

def family : Registration arena (type_of% actual_reflected_gaussian_coefficient_core) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_reflected_gaussian_coefficient_core, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_reflected_gaussian_coefficient_core (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianCoefficientCore.core_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianCoefficientCore.family
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
    (fun _ _ f => positiveCurveSpan f (1 / 36)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianCoefficientCore
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianCoefficientCore
