import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GaussianZeroKernel
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.GaussianZeroKernel

open MeasureTheory Complex LeanInformationAudit
open _root_.D5.S3.Arith.Robin.GaussianZeroKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℝ, ℝ) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p w => transform p.1 p.2 w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m M γ : ℝ), 0 < m →
    (∀ w : ℂ,
      Integrable (fun y : ℝ => Complex.exp (w * y) * density m M y) ∧
      Integrable (fun y : ℝ => (coordinate m M y : ℂ) * Complex.exp (w * y) *
        density m M y) ∧
      Integrable (fun y : ℝ => (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) *
        density m M y) ∧
      (∫ y : ℝ, Complex.exp (w * y) * density m M y) = R.readout () ⟨m, M⟩ w ∧
      (∫ y : ℝ, (coordinate m M y : ℂ) * Complex.exp (w * y) * density m M y) =
        w * transform m M w ∧
      (∫ y : ℝ, (coordinate m M y : ℂ) ^ 2 * Complex.exp (w * y) * density m M y) =
        (w ^ 2 + 1 / (2 * (m : ℂ))) * transform m M w) ∧
    (∀ ρ : ℂ, ρ ≠ 0 → ρ ≠ 1 →
      let a := (ρ * (1 - ρ))⁻¹
      Integrable (fun y : ℝ => a * Complex.exp (ρ * y) *
        (Complex.exp (-Complex.I * γ * y) * polynomial m M γ y) * density m M y) ∧
      Integrable (fun y : ℝ => a * Complex.exp (ρ * y) * envelope m M γ y) ∧
      (∫ y : ℝ, a * Complex.exp (ρ * y) *
        (Complex.exp (-Complex.I * γ * y) * polynomial m M γ y) * density m M y) =
        -transform m M (ρ - Complex.I * γ) ∧
      (∫ y : ℝ, a * Complex.exp (ρ * y) * envelope m M γ y) =
        2 * a * (ρ ^ 2 + γ ^ 2 + 1 + 1 / (2 * (m : ℂ))) * transform m M ρ) ∧
    (∀ y : ℝ, 0 ≤ envelope m M γ y) ∧
    (1 ≤ m → ∀ y : ℝ, |kernel m M γ y| ≤ envelope m M γ y ∧
      ‖Complex.exp (-Complex.I * γ * y) * polynomial m M γ y‖ * density m M y ≤
        envelope m M γ y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 0 0 (by norm_num)).1 0 |>.2.2.2.1
  have hgood := (gaussian_zero_kernel 1 0 0 (by norm_num)).1 0 |>.2.2.2.1
  have he : transform 1 0 0 = (0 : ℂ) := hgood.symm.trans hbad
  norm_num [transform] at he

def family : Registration arena (type_of% (@gaussian_zero_kernel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gaussian_zero_kernel, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
    change transform 1 0 0 ≠ transform 1 0 1
    simp only [transform, ofReal_one, ofReal_zero, zero_pow (by decide : 2 ≠ 0),
      one_pow, mul_zero, zero_mul, add_zero, one_mul, Complex.exp_zero]
    rw [show Complex.exp (1 : ℂ) = ((Real.exp 1 : ℝ) : ℂ) from
      (Complex.ofReal_exp 1).symm]
    exact_mod_cast (ne_of_lt (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)))

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_zero_kernel) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.GaussianZeroKernel.gaussian_zero_kernel.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.GaussianZeroKernel.family
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
    owner := `D5.S3.Arith.Robin.GaussianZeroKernel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body",
        "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.GaussianZeroKernel
