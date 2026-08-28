/- GID: D5/S3/Analytic/UnitFlow/GaloisReflection
   generality: I
   mirror-B: D5/B/S3/Analytic/UnitFlow/GaloisReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Galois conjugation reflects the Golden unit-flow principal zeta -/

import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace D5.S3.Analytic.UnitFlow.GaloisReflection

open NumberField
open scoped QuadraticAlgebra

noncomputable section

/-- No rational number satisfies the Golden minimal equation `x^2 = x + 1`. -/
theorem goldenPolynomial_no_rational_root (r : ℚ) : r ^ 2 ≠ 1 + r := by
  intro hr
  have hrReal : (r : ℝ) ^ 2 = 1 + (r : ℝ) := by exact_mod_cast hr
  have hsquare : (2 * (r : ℝ) - 1) ^ 2 = 5 := by nlinarith
  have habs : |2 * (r : ℝ) - 1| = √5 := by
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
  apply (show Irrational (√5 : ℝ) from Nat.Prime.irrational_sqrt (by norm_num))
  exact ⟨|2 * r - 1|, by simpa using habs⟩

instance goldenField_no_rational_root :
    Fact (∀ r : ℚ, r ^ 2 ≠ (1 : ℚ) + 1 * r) :=
  ⟨fun r => by simpa using goldenPolynomial_no_rational_root r⟩

/-- The concrete quadratic field `ℚ(φ) = ℚ[X]/(X^2-X-1)`. -/
abbrev GoldenField := QuadraticAlgebra ℚ 1 1

instance goldenField_numberField : NumberField GoldenField where
  to_charZero := inferInstance
  to_finiteDimensional := by infer_instance

private def goldenEmbedding (root : ℝ) (hroot : root ^ 2 = root + 1) :
    GoldenField →ₐ[ℚ] ℝ where
  toFun x := (x.re : ℝ) + (x.im : ℝ) * root
  map_one' := by simp
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    linear_combination (-((x.im : ℝ) * (y.im : ℝ))) * hroot
  map_zero' := by simp
  map_add' x y := by simp; ring
  commutes' r := by simp

/-- The real embedding sending the Golden generator to `φ`. -/
def goldenEmbeddingPlus : GoldenField →ₐ[ℚ] ℝ :=
  goldenEmbedding Real.goldenRatio Real.goldenRatio_sq

/-- The other real embedding, sending the Golden generator to its conjugate. -/
def goldenEmbeddingMinus : GoldenField →ₐ[ℚ] ℝ :=
  goldenEmbedding Real.goldenConj Real.goldenConj_sq

/-- The nontrivial `ℚ`-automorphism of the concrete Golden field. -/
def goldenConjugation : GoldenField ≃ₐ[ℚ] GoldenField where
  toFun x := star x
  invFun x := star x
  left_inv x := star_star x
  right_inv x := star_star x
  map_mul' x y := by rw [star_mul, mul_comm]
  map_add' x y := star_add x y
  commutes' r := by
    apply QuadraticAlgebra.ext <;> simp

@[simp]
theorem goldenConjugation_re (x : GoldenField) :
    (goldenConjugation x).re = x.re + x.im := by
  change (star x).re = x.re + x.im
  simp

@[simp]
theorem goldenConjugation_im (x : GoldenField) :
    (goldenConjugation x).im = -x.im := by
  change (star x).im = -x.im
  simp

@[simp]
theorem goldenEmbeddingPlus_apply (x : GoldenField) :
    goldenEmbeddingPlus x = (x.re : ℝ) + (x.im : ℝ) * Real.goldenRatio :=
  rfl

@[simp]
theorem goldenEmbeddingMinus_apply (x : GoldenField) :
    goldenEmbeddingMinus x = (x.re : ℝ) + (x.im : ℝ) * Real.goldenConj :=
  rfl

@[simp]
theorem goldenEmbeddingPlus_omega :
    goldenEmbeddingPlus (QuadraticAlgebra.omega : GoldenField) = Real.goldenRatio := by
  rw [goldenEmbeddingPlus_apply]
  norm_num

@[simp]
theorem goldenEmbeddingMinus_omega :
    goldenEmbeddingMinus (QuadraticAlgebra.omega : GoldenField) = Real.goldenConj := by
  rw [goldenEmbeddingMinus_apply]
  norm_num

@[simp]
theorem goldenConjugation_omega :
    goldenConjugation (QuadraticAlgebra.omega : GoldenField) =
      (⟨1, -1⟩ : GoldenField) := by
  apply QuadraticAlgebra.ext <;> norm_num [goldenConjugation]

/-- The two real embeddings of `ℚ(φ)` are genuinely distinct. -/
theorem golden_embeddings_ne : goldenEmbeddingPlus ≠ goldenEmbeddingMinus := by
  intro h
  have homega := DFunLike.congr_fun h
    (QuadraticAlgebra.omega : GoldenField)
  have homega' : Real.goldenRatio = Real.goldenConj := by
    simpa only [goldenEmbeddingPlus_omega, goldenEmbeddingMinus_omega] using homega
  linarith [Real.goldenRatio_pos, Real.goldenConj_neg]

/-- Golden Galois conjugation is the nonidentity automorphism. -/
theorem goldenConjugation_ne_refl :
    goldenConjugation ≠ (AlgEquiv.refl : GoldenField ≃ₐ[ℚ] GoldenField) := by
  intro h
  have homega := DFunLike.congr_fun h
    (QuadraticAlgebra.omega : GoldenField)
  have him := congrArg QuadraticAlgebra.im homega
  norm_num [goldenConjugation] at him

private theorem goldenEmbeddingPlus_conjugation (x : GoldenField) :
    goldenEmbeddingPlus (goldenConjugation x) = goldenEmbeddingMinus x := by
  rw [goldenEmbeddingPlus_apply, goldenEmbeddingMinus_apply]
  rw [goldenConjugation_re, goldenConjugation_im]
  push_cast
  rw [← Real.one_sub_goldenConj]
  ring

private theorem goldenEmbeddingMinus_conjugation (x : GoldenField) :
    goldenEmbeddingMinus (goldenConjugation x) = goldenEmbeddingPlus x := by
  rw [goldenEmbeddingMinus_apply, goldenEmbeddingPlus_apply]
  rw [goldenConjugation_re, goldenConjugation_im]
  push_cast
  rw [← Real.one_sub_goldenRatio]
  ring

/-- The squared absolute value of a real embedding on an algebraic integer. -/
def embeddingSquare {K : Type*} [Field K] (sigma : K →+* ℝ)
    (α : NumberField.RingOfIntegers K) : ℝ :=
  |sigma (α : K)| ^ 2

/-- The anisotropic quadratic form transported by the unit-flow parameter. -/
def anisotropicForm {K : Type*} [Field K] (sigmaPlus sigmaMinus : K →+* ℝ)
    (eta : ℝ) (α : NumberField.RingOfIntegers K) : ℝ :=
  Real.exp eta * embeddingSquare sigmaPlus α +
    Real.exp (-eta) * embeddingSquare sigmaMinus α

/-- One term of the Golden principal zeta on the concrete field `ℚ(φ)`. -/
def principalZetaTerm (s : ℂ) (eta : ℝ)
    (α : {α : NumberField.RingOfIntegers GoldenField // α ≠ 0}) : ℂ :=
  ((anisotropicForm (K := GoldenField)
    goldenEmbeddingPlus goldenEmbeddingMinus eta α : ℝ) : ℂ) ^ (-s)

/-- The Golden unit-flow principal zeta over the actual nonzero algebraic
integers of the concrete field `ℚ(φ)`. -/
def principalZeta (s : ℂ) (eta : ℝ) : ℂ :=
  ∑' α : {α : NumberField.RingOfIntegers GoldenField // α ≠ 0},
    principalZetaTerm s eta α

/-- Analytic well-formedness of the Golden zeta in its stated half-plane. -/
def PrincipalZetaSummable (s : ℂ) : Prop :=
  ∀ eta : ℝ, Summable (principalZetaTerm s eta)

/-- A certificate that the Golden zeta genuinely observes its flow parameter. -/
def PrincipalZetaNonconstant (s : ℂ) : Prop :=
  ∃ eta₁ eta₂ : ℝ, principalZeta s eta₁ ≠ principalZeta s eta₂

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

private theorem golden_embeddingSquare_swap
    (α : NumberField.RingOfIntegers GoldenField) :
    embeddingSquare goldenEmbeddingPlus (integerConjugation goldenConjugation α) =
        embeddingSquare goldenEmbeddingMinus α ∧
      embeddingSquare goldenEmbeddingMinus (integerConjugation goldenConjugation α) =
        embeddingSquare goldenEmbeddingPlus α := by
  have hplus :
      goldenEmbeddingPlus (goldenConjugation (α : GoldenField)) =
        goldenEmbeddingMinus (α : GoldenField) := by
    exact goldenEmbeddingPlus_conjugation (α : GoldenField)
  have hminus :
      goldenEmbeddingMinus (goldenConjugation (α : GoldenField)) =
        goldenEmbeddingPlus (α : GoldenField) := by
    exact goldenEmbeddingMinus_conjugation (α : GoldenField)
  change
    |goldenEmbeddingPlus (goldenConjugation (α : GoldenField))| ^ 2 =
        |goldenEmbeddingMinus (α : GoldenField)| ^ 2 ∧
      |goldenEmbeddingMinus (goldenConjugation (α : GoldenField))| ^ 2 =
        |goldenEmbeddingPlus (α : GoldenField)| ^ 2
  exact ⟨congrArg (fun x : ℝ => |x| ^ 2) hplus,
    congrArg (fun x : ℝ => |x| ^ 2) hminus⟩

private theorem anisotropicForm_conjugation
    (eta : ℝ)
    (α : {α : NumberField.RingOfIntegers GoldenField // α ≠ 0}) :
    anisotropicForm (K := GoldenField) goldenEmbeddingPlus goldenEmbeddingMinus eta
        (nonzeroIntegerConjugation goldenConjugation α) =
      anisotropicForm (K := GoldenField)
        goldenEmbeddingPlus goldenEmbeddingMinus (-eta) α := by
  have hswap := golden_embeddingSquare_swap α
  have hplus :
      embeddingSquare (K := GoldenField) goldenEmbeddingPlus
          (nonzeroIntegerConjugation goldenConjugation α) =
        embeddingSquare (K := GoldenField) goldenEmbeddingMinus α := hswap.1
  have hminus :
      embeddingSquare (K := GoldenField) goldenEmbeddingMinus
          (nonzeroIntegerConjugation goldenConjugation α) =
        embeddingSquare (K := GoldenField) goldenEmbeddingPlus α := hswap.2
  simp only [anisotropicForm, hplus, hminus, neg_neg]
  ring

/-- Galois reflection for the Golden unit-flow principal zeta, together with
the faithful infinite-dihedral symmetry generated by the preceding regulator
period and this reflection. -/
theorem galois_reflection
    (s : ℂ) (_hs : 1 < s.re)
    (_hsummable : PrincipalZetaSummable s)
    (hregulator : Function.Periodic (principalZeta s) regulatorPeriod)
    (_hnonconstant : PrincipalZetaNonconstant s) :
    (∀ eta : ℝ,
        principalZeta s eta = principalZeta s (-eta)) ∧
      Function.Injective (unitFlowAction regulatorPeriod) ∧
      ∀ (g : DihedralGroup 0) (eta : ℝ),
        principalZeta s (unitFlowAction regulatorPeriod g eta) = principalZeta s eta := by
  have hreflection : ∀ eta : ℝ,
      principalZeta s eta = principalZeta s (-eta) := by
    intro eta
    unfold principalZeta principalZetaTerm
    calc
      ∑' α : {α : NumberField.RingOfIntegers GoldenField // α ≠ 0},
          ((anisotropicForm (K := GoldenField)
            goldenEmbeddingPlus goldenEmbeddingMinus eta α : ℝ) : ℂ) ^ (-s) =
          ∑' α : {α : NumberField.RingOfIntegers GoldenField // α ≠ 0},
            ((anisotropicForm (K := GoldenField) goldenEmbeddingPlus goldenEmbeddingMinus eta
              (nonzeroIntegerConjugation goldenConjugation α) : ℝ) : ℂ) ^ (-s) :=
        ((nonzeroIntegerConjugation goldenConjugation).tsum_eq _).symm
      _ = ∑' α : {α : NumberField.RingOfIntegers GoldenField // α ≠ 0},
          ((anisotropicForm (K := GoldenField)
            goldenEmbeddingPlus goldenEmbeddingMinus (-eta) α : ℝ) : ℂ) ^ (-s) := by
        apply tsum_congr
        intro α
        rw [anisotropicForm_conjugation]
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
    (s : ℂ) (hs : 1 < s.re)
    (hsummable : PrincipalZetaSummable s)
    (hregulator : Function.Periodic (principalZeta s) regulatorPeriod)
    (hnonconstant : PrincipalZetaNonconstant s) :
    principalZeta s 1 = principalZeta s (-1) ∧
      principalZeta s (unitFlowAction regulatorPeriod (.r 1) 1) =
        principalZeta s 1 ∧
      principalZeta s (unitFlowAction regulatorPeriod (.sr 0) 1) =
        principalZeta s 1 := by
  rcases galois_reflection s hs hsummable hregulator hnonconstant with
    ⟨hreflection, _, hinvariant⟩
  exact ⟨hreflection 1, hinvariant (.r 1) 1, hinvariant (.sr 0) 1⟩

/-- Nonvacuity probe: the public assumptions force the zeta itself, rather than
an unrelated action, to distinguish two flow parameters. -/
example (s : ℂ) (_hsummable : PrincipalZetaSummable s)
    (hnonconstant : PrincipalZetaNonconstant s) :
    ∃ eta₁ eta₂ : ℝ, principalZeta s eta₁ ≠ principalZeta s eta₂ := by
  exact hnonconstant

end

end D5.S3.Analytic.UnitFlow.GaloisReflection
