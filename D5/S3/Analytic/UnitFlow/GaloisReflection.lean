/- GID: D5/S3/Analytic/UnitFlow/GaloisReflection
   generality: I
   mirror-B: D5/B/S3/Analytic/UnitFlow/GaloisReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Galois conjugation gives reflection and faithful infinite-dihedral
     symmetry of the Golden unit-flow principal zeta. -/

import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace D5.S3.Analytic.UnitFlow.GaloisReflection

open NumberField

noncomputable section

/-- The squared absolute value of a real embedding on an algebraic integer. -/
def embeddingSquare {K : Type*} [Field K] (sigma : K →+* ℝ)
    (α : NumberField.RingOfIntegers K) : ℝ :=
  |sigma (α : K)| ^ 2

/-- The anisotropic quadratic form transported by the unit-flow parameter. -/
def anisotropicForm {K : Type*} [Field K] (sigmaPlus sigmaMinus : K →+* ℝ)
    (eta : ℝ) (α : NumberField.RingOfIntegers K) : ℝ :=
  Real.exp eta * embeddingSquare sigmaPlus α +
    Real.exp (-eta) * embeddingSquare sigmaMinus α

/-- The Golden unit-flow principal zeta, indexed by the actual nonzero
algebraic integers of the number field. -/
def principalZeta {K : Type*} [Field K] (sigmaPlus sigmaMinus : K →+* ℝ)
    (s : ℂ) (eta : ℝ) : ℂ :=
  ∑' α : {α : NumberField.RingOfIntegers K // α ≠ 0},
    ((anisotropicForm sigmaPlus sigmaMinus eta α : ℝ) : ℂ) ^ (-s)

/-- Twice the logarithmic Golden regulator, the period from theorem 44.1. -/
def regulatorPeriod : ℝ :=
  2 * Real.log Real.goldenRatio

/-- Restriction of a number-field automorphism to the actual ring of integers. -/
def integerConjugation {K : Type*} [Field K] [NumberField K]
    (tau : K ≃ₐ[ℚ] K) :
      NumberField.RingOfIntegers K ≃ NumberField.RingOfIntegers K :=
  (RingOfIntegers.mapAlgEquiv tau).toEquiv

/-- Restriction of Galois conjugation to nonzero algebraic integers. -/
def nonzeroIntegerConjugation {K : Type*} [Field K] [NumberField K]
    (tau : K ≃ₐ[ℚ] K) :
      {α : NumberField.RingOfIntegers K // α ≠ 0} ≃
        {α : NumberField.RingOfIntegers K // α ≠ 0} :=
  (integerConjugation tau).subtypeEquiv fun α => by
    exact (RingOfIntegers.mapAlgEquiv tau).map_ne_zero_iff.symm

/-- Translation by an integer multiple of a real period. -/
def periodTranslation (period : ℝ) (k : ZMod 0) : Equiv.Perm ℝ where
  toFun eta := eta + (ZMod.cast k : ℝ) * period
  invFun eta := eta - (ZMod.cast k : ℝ) * period
  left_inv eta := by ring
  right_inv eta := by ring

/-- Reflection followed by an integer period shift. -/
def periodReflection (period : ℝ) (k : ZMod 0) : Equiv.Perm ℝ where
  toFun eta := -eta - (ZMod.cast k : ℝ) * period
  invFun eta := -eta - (ZMod.cast k : ℝ) * period
  left_inv eta := by ring
  right_inv eta := by ring

/-- The standard affine action of Mathlib's infinite dihedral group on the
unit-flow parameter line. Rotations translate by integer periods; reflected
elements negate and then shift. -/
def unitFlowAction (period : ℝ) : DihedralGroup 0 →* Equiv.Perm ℝ where
  toFun
    | .r k => periodTranslation period k
    | .sr k => periodReflection period k
  map_one' := by
    change periodTranslation period 0 = 1
    ext eta
    simp [periodTranslation]
  map_mul' g h := by
    cases g with
    | r i =>
        cases h with
        | r j =>
            ext eta
            simp [periodTranslation]
            ring
        | sr j =>
            ext eta
            simp [periodTranslation, periodReflection]
            ring
    | sr i =>
        cases h with
        | r j =>
            ext eta
            simp [periodTranslation, periodReflection]
            ring
        | sr j =>
            ext eta
            simp [periodTranslation, periodReflection]
            ring

@[simp]
theorem unitFlowAction_r_apply (period : ℝ) (k : ZMod 0) (eta : ℝ) :
    unitFlowAction period (.r k) eta = eta + (ZMod.cast k : ℝ) * period :=
  rfl

@[simp]
theorem unitFlowAction_sr_apply (period : ℝ) (k : ZMod 0) (eta : ℝ) :
    unitFlowAction period (.sr k) eta = -eta - (ZMod.cast k : ℝ) * period :=
  rfl

/-- A nonzero period makes the affine infinite-dihedral action faithful. -/
theorem unitFlowAction_injective {period : ℝ} (hperiod : period ≠ 0) :
    Function.Injective (unitFlowAction period) := by
  intro g h hgh
  cases g with
  | r i =>
      cases h with
      | r j =>
          apply congrArg (fun k : ZMod 0 => DihedralGroup.r k)
          apply ZMod.castHom_injective ℝ
          have hzero := Equiv.congr_fun hgh 0
          simp only [unitFlowAction_r_apply, zero_add] at hzero
          exact mul_right_cancel₀ hperiod hzero
      | sr j =>
          have hzero := Equiv.congr_fun hgh 0
          have hone := Equiv.congr_fun hgh 1
          simp only [unitFlowAction_r_apply, unitFlowAction_sr_apply, zero_add, neg_zero,
            zero_sub] at hzero hone
          linarith
  | sr i =>
      cases h with
      | r j =>
          have hzero := Equiv.congr_fun hgh 0
          have hone := Equiv.congr_fun hgh 1
          simp only [unitFlowAction_r_apply, unitFlowAction_sr_apply, zero_add, neg_zero,
            zero_sub] at hzero hone
          linarith
      | sr j =>
          apply congrArg (fun k : ZMod 0 => DihedralGroup.sr k)
          apply ZMod.castHom_injective ℝ
          have hzero := Equiv.congr_fun hgh 0
          simp only [unitFlowAction_sr_apply, neg_zero, zero_sub, neg_inj] at hzero
          exact mul_right_cancel₀ hperiod hzero

private theorem anisotropicForm_conjugation
    {K : Type*} [Field K] [NumberField K]
    (sigmaPlus sigmaMinus : K →+* ℝ) (tau : K ≃ₐ[ℚ] K)
    (hswap : ∀ α : NumberField.RingOfIntegers K,
      embeddingSquare sigmaPlus (integerConjugation tau α) =
          embeddingSquare sigmaMinus α ∧
        embeddingSquare sigmaMinus (integerConjugation tau α) =
          embeddingSquare sigmaPlus α)
    (eta : ℝ) (α : {α : NumberField.RingOfIntegers K // α ≠ 0}) :
    anisotropicForm sigmaPlus sigmaMinus eta (nonzeroIntegerConjugation tau α) =
      anisotropicForm sigmaPlus sigmaMinus (-eta) α := by
  have hplus :
      embeddingSquare sigmaPlus (nonzeroIntegerConjugation tau α) =
        embeddingSquare sigmaMinus α := by
    exact (hswap α).1
  have hminus :
      embeddingSquare sigmaMinus (nonzeroIntegerConjugation tau α) =
        embeddingSquare sigmaPlus α := by
    exact (hswap α).2
  simp only [anisotropicForm, hplus, hminus, neg_neg]
  ring

/-- Galois reflection for the Golden unit-flow principal zeta, together with
the faithful infinite-dihedral symmetry generated by the preceding regulator
period and this reflection. -/
theorem galois_reflection
    {K : Type*} [Field K] [NumberField K]
    (sigmaPlus sigmaMinus : K →+* ℝ) (tau : K ≃ₐ[ℚ] K)
    (hswap : ∀ α : NumberField.RingOfIntegers K,
      embeddingSquare sigmaPlus (integerConjugation tau α) =
          embeddingSquare sigmaMinus α ∧
        embeddingSquare sigmaMinus (integerConjugation tau α) =
          embeddingSquare sigmaPlus α)
    (s : ℂ) (_hs : 1 < s.re)
    (hregulator : Function.Periodic
      (principalZeta sigmaPlus sigmaMinus s) regulatorPeriod) :
    (∀ eta : ℝ,
        principalZeta sigmaPlus sigmaMinus s eta =
          principalZeta sigmaPlus sigmaMinus s (-eta)) ∧
      Function.Injective (unitFlowAction regulatorPeriod) ∧
      ∀ (g : DihedralGroup 0) (eta : ℝ),
        principalZeta sigmaPlus sigmaMinus s (unitFlowAction regulatorPeriod g eta) =
          principalZeta sigmaPlus sigmaMinus s eta := by
  have hreflection : ∀ eta : ℝ,
      principalZeta sigmaPlus sigmaMinus s eta =
        principalZeta sigmaPlus sigmaMinus s (-eta) := by
    intro eta
    unfold principalZeta
    calc
      ∑' α : {α : NumberField.RingOfIntegers K // α ≠ 0},
          ((anisotropicForm sigmaPlus sigmaMinus eta α : ℝ) : ℂ) ^ (-s) =
          ∑' α : {α : NumberField.RingOfIntegers K // α ≠ 0},
            ((anisotropicForm sigmaPlus sigmaMinus eta
              (nonzeroIntegerConjugation tau α) : ℝ) : ℂ) ^ (-s) :=
        ((nonzeroIntegerConjugation tau).tsum_eq _).symm
      _ = ∑' α : {α : NumberField.RingOfIntegers K // α ≠ 0},
          ((anisotropicForm sigmaPlus sigmaMinus (-eta) α : ℝ) : ℂ) ^ (-s) := by
        apply tsum_congr
        intro α
        rw [anisotropicForm_conjugation sigmaPlus sigmaMinus tau hswap]
  have hperiodNonzero : regulatorPeriod ≠ 0 := by
    have hlog : 0 < Real.log Real.goldenRatio :=
      Real.log_pos Real.one_lt_goldenRatio
    unfold regulatorPeriod
    positivity
  refine ⟨hreflection, unitFlowAction_injective hperiodNonzero, ?_⟩
  intro g eta
  cases g with
  | r k =>
      simpa only [unitFlowAction_r_apply, ZMod.intCast_cast] using
        (hregulator.int_mul (ZMod.cast k : ℤ) eta)
  | sr k =>
      have hshift := hregulator.sub_int_mul_eq (x := -eta) (ZMod.cast k : ℤ)
      simpa only [unitFlowAction_sr_apply, ZMod.intCast_cast] using
        hshift.trans (hreflection eta).symm

/-- Reverse probe: the public theorem exposes reflection away from the fixed
point and invariance under both canonical dihedral generators. -/
example
    {K : Type*} [Field K] [NumberField K]
    (sigmaPlus sigmaMinus : K →+* ℝ) (tau : K ≃ₐ[ℚ] K)
    (hswap : ∀ α : NumberField.RingOfIntegers K,
      embeddingSquare sigmaPlus (integerConjugation tau α) =
          embeddingSquare sigmaMinus α ∧
        embeddingSquare sigmaMinus (integerConjugation tau α) =
          embeddingSquare sigmaPlus α)
    (s : ℂ) (hs : 1 < s.re)
    (hregulator : Function.Periodic
      (principalZeta sigmaPlus sigmaMinus s) regulatorPeriod) :
    principalZeta sigmaPlus sigmaMinus s 1 =
        principalZeta sigmaPlus sigmaMinus s (-1) ∧
      principalZeta sigmaPlus sigmaMinus s
          (unitFlowAction regulatorPeriod (.r 1) 1) =
        principalZeta sigmaPlus sigmaMinus s 1 ∧
      principalZeta sigmaPlus sigmaMinus s
          (unitFlowAction regulatorPeriod (.sr 0) 1) =
        principalZeta sigmaPlus sigmaMinus s 1 := by
  rcases galois_reflection sigmaPlus sigmaMinus tau hswap s hs hregulator with
    ⟨hreflection, _, hinvariant⟩
  exact ⟨hreflection 1, hinvariant (.r 1) 1, hinvariant (.sr 0) 1⟩

/-- Collapse probe: the Golden translation generator is not the identity in
the public affine action. -/
example : unitFlowAction regulatorPeriod (.r 0) ≠ unitFlowAction regulatorPeriod (.r 1) := by
  intro h
  have hinjective : Function.Injective (unitFlowAction regulatorPeriod) := by
    apply unitFlowAction_injective
    have hlog : 0 < Real.log Real.goldenRatio :=
      Real.log_pos Real.one_lt_goldenRatio
    unfold regulatorPeriod
    positivity
  have : (DihedralGroup.r 0 : DihedralGroup 0) = DihedralGroup.r 1 := hinjective h
  injection this with hzeroone
  norm_num at hzeroone

end

end D5.S3.Analytic.UnitFlow.GaloisReflection
