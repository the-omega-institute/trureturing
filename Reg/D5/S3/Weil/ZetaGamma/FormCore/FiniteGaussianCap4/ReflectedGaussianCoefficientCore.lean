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

abbrev signature := Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore.signature
abbrev actual := Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore.actual
abbrev rejected := Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore.rejected

def arena : Arena where
  signature := signature
  Law R := ∃ f : ℝ → GaussianCoeffSpace,
    (∀ t : ℝ, 0 < t → t < 1 / 36 → ∀ n : ℕ,
      f t n = coeffWeight n * actualReflectedCurveCoefficient t n) ∧
    R.readout () (1 / 36) f = (coeffCharge actualCentralChargeVector).ker

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

def family : Registration arena (type_of% actual_reflected_gaussian_coefficient_core) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_reflected_gaussian_coefficient_core, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := Reg.D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore.family.dependence

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
    (fun _ r f => positiveCurveSpan f r) (fun e => nomatch e))
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
