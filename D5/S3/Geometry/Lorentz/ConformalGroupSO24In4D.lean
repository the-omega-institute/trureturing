/- GID: D5/S3/Geometry/Lorentz/ConformalGroupSO24In4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/ConformalGroupSO24In4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conformal generators, Minkowski cross-ratios and the twistor Lie equivalence. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.DiracCliffordSpinors4D
import D5.S3.Geometry.Lorentz.WeylNullScreen
import OmegaMath.Geometry.OrthogonalMatrixGenerators
import OmegaMath.Geometry.ChiralClifford24
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The signed six-dimensional matrix model fixes the conformal bracket
conventions. In the Minkowski chart, inversion and special conformal maps
preserve four-point ratios through pairwise distance scaling. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix ComplexConjugate BigOperators

namespace D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D

open OmegaMath.OrthogonalMatrixGenerators

abbrev RMat6 := Matrix (Fin 6) (Fin 6) ℝ

def metricSign24 : Fin 6 → ℝ := ![1, -1, -1, -1, -1, 1]

def eta24 : RMat6 := metric metricSign24

private theorem sign_mul_self (i : Fin 6) : metricSign24 i * metricSign24 i = 1 := by
  fin_cases i <;> norm_num [metricSign24]

def L (a b : Fin 6) : RMat6 := generator metricSign24 a b

theorem so24_antisym_metric (a b : Fin 6) : (L a b)ᵀ * eta24 + eta24 * L a b = 0 :=
  generator_mem metricSign24 a b

theorem so24_commutator_universal (a b c d : Fin 6) :
    L a b * L c d - L c d * L a b =
      eta24 b c • L a d - eta24 a c • L b d -
        eta24 b d • L a c + eta24 a d • L b c :=
  generator_commutator metricSign24 a b c d

def so24Subspace : Submodule ℝ RMat6 := orthogonalSubspace metricSign24

abbrev ConformalPair := OrderedPair (Fin 6)

def so24Basis (p : ConformalPair) : RMat6 := L p.val.1 p.val.2

def so24Coordinates : RMat6 →ₗ[ℝ] (ConformalPair → ℝ) := coordinates metricSign24

private theorem so24_coord_basis (p q : ConformalPair) :
    so24Coordinates (so24Basis q) p = if p = q then 1 else 0 :=
  coordinates_generator metricSign24 sign_mul_self p q

theorem so24_expansion (X : RMat6) (hX : X ∈ so24Subspace) :
    (∑ p : ConformalPair, (X p.val.1 p.val.2 * metricSign24 p.val.2) • so24Basis p) = X :=
  generator_expansion metricSign24 sign_mul_self X hX

theorem so24_basis15_linearIndependent : LinearIndependent ℝ so24Basis :=
  generator_linearIndependent metricSign24 sign_mul_self

def so24CoordinateEquiv : so24Subspace ≃ₗ[ℝ] (ConformalPair → ℝ) :=
  coordinateEquiv metricSign24 sign_mul_self

theorem so24_subspace_finrank_15 : Module.finrank ℝ so24Subspace = 15 := by
  rw [so24CoordinateEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  decide

private abbrev spacetimeIndex (μ : Fin 4) : Fin 6 := μ.castSucc.castSucc

def LorentzGen (μ ν : Fin 4) : RMat6 := L (spacetimeIndex μ) (spacetimeIndex ν)
def dilatation : RMat6 := L 4 5
def translationGen (μ : Fin 4) : RMat6 := L (spacetimeIndex μ) 4 + L (spacetimeIndex μ) 5
def specialGen (μ : Fin 4) : RMat6 := L (spacetimeIndex μ) 4 - L (spacetimeIndex μ) 5

def bracket (X Y : RMat6) : RMat6 := X * Y - Y * X

private theorem bracket_add_left (X Y Z : RMat6) :
    bracket (X + Y) Z = bracket X Z + bracket Y Z := by
  simp only [bracket, Matrix.add_mul, Matrix.mul_add]
  abel

private theorem bracket_add_right (X Y Z : RMat6) :
    bracket X (Y + Z) = bracket X Y + bracket X Z := by
  simp only [bracket, Matrix.add_mul, Matrix.mul_add]
  abel

private theorem bracket_sub_left (X Y Z : RMat6) :
    bracket (X - Y) Z = bracket X Z - bracket Y Z := by
  simp only [bracket, Matrix.sub_mul, Matrix.mul_sub]
  abel

private theorem bracket_sub_right (X Y Z : RMat6) :
    bracket X (Y - Z) = bracket X Y - bracket X Z := by
  simp only [bracket, Matrix.sub_mul, Matrix.mul_sub]
  abel

private theorem bracket_L (a b c d : Fin 6) :
    bracket (L a b) (L c d) = eta24 b c • L a d - eta24 a c • L b d -
      eta24 b d • L a c + eta24 a d • L b c := so24_commutator_universal a b c d

private theorem eta_spacetime_four (μ : Fin 4) : eta24 (spacetimeIndex μ) 4 = 0 := by
  apply Matrix.diagonal_apply_ne
  intro h
  have hv := congr_arg Fin.val h
  have hb := μ.isLt
  change μ.val = 4 at hv
  omega

private theorem eta_spacetime_five (μ : Fin 4) : eta24 (spacetimeIndex μ) 5 = 0 := by
  apply Matrix.diagonal_apply_ne
  intro h
  have hv := congr_arg Fin.val h
  have hb := μ.isLt
  change μ.val = 5 at hv
  omega

private theorem eta_four_spacetime (μ : Fin 4) : eta24 4 (spacetimeIndex μ) = 0 := by
  rw [show eta24 _ _ = eta24 _ _ from metric_symm metricSign24 _ _]
  exact eta_spacetime_four μ

private theorem eta_five_spacetime (μ : Fin 4) : eta24 5 (spacetimeIndex μ) = 0 := by
  rw [show eta24 _ _ = eta24 _ _ from metric_symm metricSign24 _ _]
  exact eta_spacetime_five μ

private theorem L_swap (a b : Fin 6) : L b a = -L a b :=
  generator_swap metricSign24 a b

private theorem L_diag (a : Fin 6) : L a a = 0 := generator_diag metricSign24 a

private theorem eta_four_four : eta24 4 4 = -1 := by norm_num [eta24, metric, metricSign24]
private theorem eta_five_five : eta24 5 5 = 1 := by norm_num [eta24, metric, metricSign24]
private theorem eta_four_five : eta24 4 5 = 0 := by norm_num [eta24, metric, Matrix.diagonal_apply]
private theorem eta_five_four : eta24 5 4 = 0 := by norm_num [eta24, metric, Matrix.diagonal_apply]

theorem conformal_algebra_commutators (μ ν ρ : Fin 4) :
    bracket (translationGen μ) (translationGen ν) = 0 ∧
    bracket (specialGen μ) (specialGen ν) = 0 ∧
    bracket dilatation (LorentzGen μ ν) = 0 ∧
    bracket dilatation (translationGen μ) = translationGen μ ∧
    bracket dilatation (specialGen μ) = -specialGen μ ∧
    bracket (specialGen μ) (translationGen ν) =
      (2 : ℝ) • (LorentzGen μ ν - eta24 (spacetimeIndex μ) (spacetimeIndex ν) • dilatation) ∧
    bracket (LorentzGen μ ν) (translationGen ρ) =
      eta24 (spacetimeIndex ν) (spacetimeIndex ρ) • translationGen μ -
      eta24 (spacetimeIndex μ) (spacetimeIndex ρ) • translationGen ν ∧
    bracket (LorentzGen μ ν) (specialGen ρ) =
      eta24 (spacetimeIndex ν) (spacetimeIndex ρ) • specialGen μ -
      eta24 (spacetimeIndex μ) (spacetimeIndex ρ) • specialGen ν := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [translationGen, specialGen, dilatation, LorentzGen,
      bracket_add_left, bracket_add_right, bracket_sub_left, bracket_sub_right, bracket_L,
      eta_four_four, eta_five_five, eta_four_five, eta_five_four,
      eta_four_spacetime, eta_five_spacetime, eta_spacetime_four, eta_spacetime_five,
      L_diag, zero_smul, smul_zero, one_smul, neg_one_smul, smul_add, smul_sub,
      two_smul] <;>
    (try simp only [L_swap 4 5, L_swap (spacetimeIndex μ) 4, L_swap (spacetimeIndex μ) 5,
      smul_neg, neg_neg]) <;> abel

open SL2CLorentzCover4D (V4 minkowskiNormSq)
open ContinuousLinearMap
open Matrix

/-! ## Inversion and special conformal transformations -/

/-- The time-positive Minkowski bilinear form. -/
def minkowski (x y : V4) : ℝ := -WeylNullScreen.minkowski x y

private theorem minkowski_self (x : V4) : minkowski x x = minkowskiNormSq x := by
  unfold minkowski WeylNullScreen.minkowski minkowskiNormSq
  ring

private theorem minkowski_comm (x y : V4) : minkowski x y = minkowski y x := by
  unfold minkowski WeylNullScreen.minkowski
  ring

private theorem minkowski_add_left (x y z : V4) :
    minkowski (x + y) z = minkowski x z + minkowski y z := by
  simp only [minkowski, WeylNullScreen.minkowski, Pi.add_apply]
  ring

private theorem minkowski_add_right (x y z : V4) :
    minkowski x (y + z) = minkowski x y + minkowski x z := by
  rw [minkowski_comm x, minkowski_add_left, minkowski_comm y, minkowski_comm z]

private theorem minkowski_sub_left (x y z : V4) :
    minkowski (x - y) z = minkowski x z - minkowski y z := by
  simp only [minkowski, WeylNullScreen.minkowski, Pi.sub_apply]
  ring

private theorem minkowski_sub_right (x y z : V4) :
    minkowski x (y - z) = minkowski x y - minkowski x z := by
  rw [minkowski_comm x, minkowski_sub_left, minkowski_comm y, minkowski_comm z]

private theorem minkowski_smul_left (a : ℝ) (x y : V4) :
    minkowski (a • x) y = a * minkowski x y := by
  simp only [minkowski, WeylNullScreen.minkowski, Pi.smul_apply, smul_eq_mul]
  ring

private theorem minkowski_smul_right (a : ℝ) (x y : V4) :
    minkowski x (a • y) = a * minkowski x y := by
  rw [minkowski_comm x, minkowski_smul_left, minkowski_comm y]

private theorem normSq_smul_sub (a c : ℝ) (x y : V4) :
    minkowskiNormSq (a • x - c • y) =
      a ^ 2 * minkowskiNormSq x + c ^ 2 * minkowskiNormSq y - 2 * a * c * minkowski x y := by
  rw [← minkowski_self (a • x - c • y)]
  simp only [minkowski_sub_left, minkowski_sub_right, minkowski_smul_left, minkowski_smul_right]
  rw [minkowski_self, minkowski_self, minkowski_comm y x]
  ring

private theorem normSq_smul_add (a c : ℝ) (x y : V4) :
    minkowskiNormSq (a • x + c • y) =
      a ^ 2 * minkowskiNormSq x + c ^ 2 * minkowskiNormSq y + 2 * a * c * minkowski x y := by
  rw [← minkowski_self (a • x + c • y)]
  simp only [minkowski_add_left, minkowski_add_right, minkowski_smul_left, minkowski_smul_right]
  rw [minkowski_self, minkowski_self, minkowski_comm y x]
  ring

private theorem normSq_smul (a : ℝ) (x : V4) :
    minkowskiNormSq (a • x) = a ^ 2 * minkowskiNormSq x := by
  rw [← minkowski_self, minkowski_smul_left, minkowski_smul_right, minkowski_self]
  ring

private theorem normSq_sub (x y : V4) :
    minkowskiNormSq (x - y) = minkowskiNormSq x + minkowskiNormSq y - 2 * minkowski x y := by
  simpa using normSq_smul_sub 1 1 x y

def conformalInv (x : V4) : V4 := (minkowskiNormSq x)⁻¹ • x

theorem conformalInv_involutive (x : V4) (hx : minkowskiNormSq x ≠ 0) :
    conformalInv (conformalInv x) = x ∧
      minkowskiNormSq (conformalInv x) = (minkowskiNormSq x)⁻¹ := by
  have hnorm : minkowskiNormSq (conformalInv x) = (minkowskiNormSq x)⁻¹ := by
    rw [conformalInv, normSq_smul]
    field_simp [hx]
  refine ⟨?_, hnorm⟩
  rw [conformalInv, hnorm, inv_inv, conformalInv, smul_smul, mul_inv_cancel₀ hx, one_smul]

theorem conformalInv_diff_normSq (x y : V4)
    (hx : minkowskiNormSq x ≠ 0) (hy : minkowskiNormSq y ≠ 0) :
    minkowskiNormSq (conformalInv x - conformalInv y) =
      minkowskiNormSq (x - y) / (minkowskiNormSq x * minkowskiNormSq y) := by
  rw [conformalInv, conformalInv, normSq_smul_sub, normSq_sub]
  field_simp [hx, hy]
  ring

private def minkowskiLinear (x : V4) : V4 →L[ℝ] ℝ :=
  x 0 • proj 0 - x 1 • proj 1 - x 2 • proj 2 - x 3 • proj 3

@[simp] private theorem minkowskiLinear_apply (x v : V4) :
    minkowskiLinear x v = minkowski x v := by
  simp [minkowskiLinear, minkowski, WeylNullScreen.minkowski]
  ring

private theorem normSq_hasFDerivAt (x : V4) :
    HasFDerivAt minkowskiNormSq ((2 : ℝ) • minkowskiLinear x) x := by
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) 0 x).pow 2
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) 1 x).pow 2
  have h2 := (hasFDerivAt_apply (𝕜 := ℝ) 2 x).pow 2
  have h3 := (hasFDerivAt_apply (𝕜 := ℝ) 3 x).pow 2
  have h := h0.sub ((h1.add h2).add h3)
  change HasFDerivAt minkowskiNormSq _ x at h
  convert h using 1
  ext v
  simp [minkowskiLinear]
  ring

/-- The derivative at a non-null point as a continuous real linear map. -/
def invDeriv (x : V4) : V4 →L[ℝ] V4 :=
  (minkowskiNormSq x)⁻¹ • ContinuousLinearMap.id ℝ V4 -
    ((2 / (minkowskiNormSq x) ^ 2) • minkowskiLinear x).smulRight x

@[simp] private theorem invDeriv_apply (x v : V4) :
    invDeriv x v = (minkowskiNormSq x)⁻¹ • v -
      (2 * minkowski x v / (minkowskiNormSq x) ^ 2) • x := by
  funext i
  simp only [invDeriv, _root_.sub_apply, _root_.smul_apply, id_apply,
    smulRight_apply, minkowskiLinear_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem conformalInv_hasFDerivAt (x : V4) (hx : minkowskiNormSq x ≠ 0) :
    HasFDerivAt conformalInv (invDeriv x) x := by
  have hinv := (hasFDerivAt_inv hx).comp x (normSq_hasFDerivAt x)
  have h := hinv.smul (hasFDerivAt_id x)
  change HasFDerivAt conformalInv _ x at h
  convert h using 1
  ext v i
  simp [invDeriv_apply, Pi.smul_apply, Pi.sub_apply, div_eq_mul_inv]
  ring

theorem conformalInv_metric_pullback (x v w : V4) (hx : minkowskiNormSq x ≠ 0) :
    minkowski (invDeriv x v) (invDeriv x w) =
      (minkowskiNormSq x) ^ (-2 : ℤ) * minkowski v w := by
  simp only [invDeriv_apply, minkowski_sub_left, minkowski_sub_right, minkowski_smul_left,
    minkowski_smul_right, minkowski_self, minkowski_comm v x, _root_.zpow_neg]
  field_simp [hx]
  ring

def sctDenom (b x : V4) : ℝ :=
  1 + 2 * minkowski b x + minkowskiNormSq b * minkowskiNormSq x

/-- The rational special conformal chart, including null inputs where its denominator is nonzero. -/
def sct (b x : V4) : V4 := (sctDenom b x)⁻¹ • (x + minkowskiNormSq x • b)

theorem sct_explicit_formula (b x : V4) (hx : minkowskiNormSq x ≠ 0)
    (hd : sctDenom b x ≠ 0) :
    sct b x = conformalInv (conformalInv x + b) := by
  have hnorm : minkowskiNormSq (conformalInv x + b) = sctDenom b x / minkowskiNormSq x := by
    calc
      _ = (minkowskiNormSq x)⁻¹ ^ 2 * minkowskiNormSq x + 1 ^ 2 * minkowskiNormSq b +
        2 * (minkowskiNormSq x)⁻¹ * 1 * minkowski x b := by
          simpa [conformalInv] using normSq_smul_add (minkowskiNormSq x)⁻¹ 1 x b
      _ = _ := by
        rw [sctDenom, minkowski_comm b x]
        field_simp [hx]
        ring
  rw [sct, conformalInv, hnorm, conformalInv]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  field_simp [hx, hd]

private theorem sct_numerator_normSq (b x : V4) :
    minkowskiNormSq (x + minkowskiNormSq x • b) = minkowskiNormSq x * sctDenom b x := by
  calc
    _ = 1 ^ 2 * minkowskiNormSq x + minkowskiNormSq x ^ 2 * minkowskiNormSq b +
        2 * 1 * minkowskiNormSq x * minkowski x b := by
      simpa using normSq_smul_add 1 (minkowskiNormSq x) x b
    _ = _ := by
      rw [sctDenom, minkowski_comm b x]
      ring

theorem sct_diff_normSq (b x y : V4) (hx : sctDenom b x ≠ 0) (hy : sctDenom b y ≠ 0) :
    minkowskiNormSq (sct b x - sct b y) =
      minkowskiNormSq (x - y) / (sctDenom b x * sctDenom b y) := by
  rw [sct, sct, normSq_smul_sub, sct_numerator_normSq, sct_numerator_normSq, normSq_sub]
  simp only [minkowski_add_left, minkowski_add_right, minkowski_smul_left, minkowski_smul_right,
    minkowski_self, minkowski_comm x b]
  field_simp [hx, hy]
  unfold sctDenom
  ring

/-! ## Four-point cross-ratios -/

def crossRatioU (x₁ x₂ x₃ x₄ : V4) : ℝ :=
  minkowskiNormSq (x₁ - x₂) * minkowskiNormSq (x₃ - x₄) /
    (minkowskiNormSq (x₁ - x₃) * minkowskiNormSq (x₂ - x₄))

def crossRatioV (x₁ x₂ x₃ x₄ : V4) : ℝ :=
  minkowskiNormSq (x₁ - x₄) * minkowskiNormSq (x₂ - x₃) /
    (minkowskiNormSq (x₁ - x₃) * minkowskiNormSq (x₂ - x₄))

/-- Both transformed ratios are defined and have their original values. -/
def PreservesCrossRatios (f : V4 → V4) (x : Fin 4 → V4) : Prop :=
  minkowskiNormSq (f (x 0) - f (x 2)) ≠ 0 ∧
  minkowskiNormSq (f (x 1) - f (x 3)) ≠ 0 ∧
    crossRatioU (f (x 0)) (f (x 1)) (f (x 2)) (f (x 3)) =
      crossRatioU (x 0) (x 1) (x 2) (x 3) ∧
    crossRatioV (f (x 0)) (f (x 1)) (f (x 2)) (f (x 3)) =
      crossRatioV (x 0) (x 1) (x 2) (x 3)

private theorem crossRatios_of_pair_scaling (f : V4 → V4) (x : Fin 4 → V4)
    (w : Fin 4 → ℝ) (hw : ∀ i, w i ≠ 0)
    (h13 : minkowskiNormSq (x 0 - x 2) ≠ 0) (h24 : minkowskiNormSq (x 1 - x 3) ≠ 0)
    (h : ∀ i j, minkowskiNormSq (f (x i) - f (x j)) =
      w i * w j * minkowskiNormSq (x i - x j)) : PreservesCrossRatios f x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]
    exact mul_ne_zero (mul_ne_zero (hw _) (hw _)) h13
  · rw [h]
    exact mul_ne_zero (mul_ne_zero (hw _) (hw _)) h24
  · simp only [crossRatioU, h]
    field_simp [hw, h13, h24]
  · simp only [crossRatioV, h]
    field_simp [hw, h13, h24]

private theorem minkowski_eq_dot (x y : V4) :
    minkowski x y = x ⬝ᵥ (SL2CLorentzCover4D.eta *ᵥ y) := by
  simp [minkowski, WeylNullScreen.minkowski, SL2CLorentzCover4D.eta, Matrix.mulVec_diagonal,
    dotProduct, Fin.sum_univ_four]
  ring

private theorem normSq_lorentz (Λ : Matrix (Fin 4) (Fin 4) ℝ)
    (hΛ : Λᵀ * SL2CLorentzCover4D.eta * Λ = SL2CLorentzCover4D.eta) (x : V4) :
    minkowskiNormSq (Λ *ᵥ x) = minkowskiNormSq x := by
  calc
    _ = (Λ *ᵥ x) ⬝ᵥ (SL2CLorentzCover4D.eta *ᵥ (Λ *ᵥ x)) := by
      rw [← minkowski_eq_dot, minkowski_self]
    _ = x ⬝ᵥ ((Λᵀ * SL2CLorentzCover4D.eta * Λ) *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
        dotProduct_comm]
    _ = _ := by rw [hΛ, ← minkowski_eq_dot, minkowski_self]

theorem crossRatios_conformal_invariant (x : Fin 4 → V4)
    (h13 : minkowskiNormSq (x 0 - x 2) ≠ 0) (h24 : minkowskiNormSq (x 1 - x 3) ≠ 0) :
    (∀ a, PreservesCrossRatios (fun y => y + a) x) ∧
    (∀ Λ : Matrix (Fin 4) (Fin 4) ℝ,
      Λᵀ * SL2CLorentzCover4D.eta * Λ = SL2CLorentzCover4D.eta →
      PreservesCrossRatios (fun y => Λ *ᵥ y) x) ∧
    (∀ a : ℝ, a ≠ 0 → PreservesCrossRatios (fun y => a • y) x) ∧
    ((∀ i, minkowskiNormSq (x i) ≠ 0) → PreservesCrossRatios conformalInv x) ∧
    (∀ b, (∀ i, sctDenom b (x i) ≠ 0) → PreservesCrossRatios (sct b) x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    apply crossRatios_of_pair_scaling _ x (fun _ => 1) (fun _ => one_ne_zero) h13 h24
    intro i j
    simp
  · intro Λ hΛ
    apply crossRatios_of_pair_scaling _ x (fun _ => 1) (fun _ => one_ne_zero) h13 h24
    intro i j
    simp [← Matrix.mulVec_sub, normSq_lorentz Λ hΛ]
  · intro a ha
    apply crossRatios_of_pair_scaling _ x (fun _ => a) (fun _ => ha) h13 h24
    intro i j
    rw [← smul_sub, normSq_smul, pow_two]
  · intro hq
    apply crossRatios_of_pair_scaling _ x (fun i => (minkowskiNormSq (x i))⁻¹)
      (fun i => inv_ne_zero (hq i)) h13 h24
    intro i j
    rw [conformalInv_diff_normSq _ _ (hq i) (hq j), div_eq_mul_inv, mul_inv]
    ring
  · intro b hd
    apply crossRatios_of_pair_scaling _ x (fun i => (sctDenom b (x i))⁻¹)
      (fun i => inv_ne_zero (hd i)) h13 h24
    intro i j
    rw [sct_diff_normSq _ _ _ (hd i) (hd j), div_eq_mul_inv, mul_inv]
    ring

open DiracCliffordSpinors4D (Mat4 γ gamma5 PL PR)

open OmegaMath.ChiralClifford24 OmegaMath.OrthogonalMatrixGenerators

attribute [local instance 100] LieRing.ofAssociativeRing
private theorem toComplexMatrix_gamma (μ : Fin 4) :
    toComplexMatrix (twistorGammaZ μ) = γ μ := rfl

private theorem toComplexMatrix_gamma5 : toComplexMatrix twistorGamma5Z = gamma5 := by
  rw [DiracCliffordSpinors4D.gamma5_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toComplexMatrix, twistorGamma5Z,
    GaussianInt.toComplex_zero, GaussianInt.toComplex_one, GaussianInt.toComplex_neg]

/-- The coefficient of each ordered metric-skew generator determines its spin action. -/
def twistorRep : RMat6 →ₗ[ℝ] Mat4 where
  toFun X := ∑ p : ConformalPair, so24Coordinates X p • spinGenerator p.val.1 p.val.2
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r X := by simp [smul_smul, Finset.smul_sum]

private theorem twistorRep_basis (p : ConformalPair) :
    twistorRep (so24Basis p) = spinGenerator p.val.1 p.val.2 := by
  change (∑ q : ConformalPair, so24Coordinates (so24Basis p) q •
    spinGenerator q.val.1 q.val.2) = spinGenerator p.val.1 p.val.2
  rw [Finset.sum_eq_single p]
  · simp only [so24_coord_basis, ite_true, one_smul]
  · intro q _ hq
    simp only [so24_coord_basis, hq, ite_false, zero_smul]
  · simp

set_option maxRecDepth 8192 in
private theorem spinGenerator_swap (A B : Fin 6) : spinGenerator B A = -spinGenerator A B := by
  simp only [spinGenerator, spinGeneratorZ_swap A B, map_neg, smul_neg]

private theorem spinGenerator_diag (A : Fin 6) : spinGenerator A A = 0 := by
  simp only [spinGenerator, spinGeneratorZ_diag, map_zero, smul_zero]

private theorem twistorRep_generator (A B : Fin 6) :
    twistorRep (L A B) = spinGenerator A B := by
  rcases lt_trichotomy A B with h | rfl | h
  · exact twistorRep_basis ⟨(A, B), h⟩
  · rw [show L A A = 0 by simp [L, generator], map_zero, spinGenerator_diag]
  · rw [show L A B = -L B A by simp [L, generator, neg_sub], map_neg,
      show twistorRep (L B A) = _ from twistorRep_basis ⟨(B, A), h⟩,
      ← spinGenerator_swap]

private theorem metricTwistorZ_cast (A B : Fin 6) :
    (metricTwistorZ A B : ℂ) = (eta24 A B : ℂ) := by
  by_cases h : A = B
  · subst B
    fin_cases A <;> simp [metricTwistorZ, eta24, metric, metricSign24, GaussianInt.toComplex_neg,
      GaussianInt.toComplex_one]
  · simp [metricTwistorZ, h, eta24, metric, GaussianInt.toComplex_zero]

private theorem spinGenerator_bracket (A B C D : Fin 6) :
    spinGenerator A B * spinGenerator C D - spinGenerator C D * spinGenerator A B =
      eta24 B C • spinGenerator A D - eta24 A C • spinGenerator B D -
        eta24 B D • spinGenerator A C + eta24 A D • spinGenerator B C := by
  have h := congrArg toComplexMatrix (spinGeneratorZ_bracket A B C D)
  simp only [map_sub, map_add, map_mul, toComplexMatrix_gaussian_smul,
    metricTwistorZ_cast] at h
  have htwo : ((2 : GaussianInt) : ℂ) = 2 := map_ofNat GaussianInt.toComplex 2
  rw [htwo] at h
  simp only [spinGenerator, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, h,
    mat4_real_smul, smul_smul]
  module

/-- The real form selected by the original Dirac Hermitian matrix. -/
def IsSU22Lie (X : Mat4) : Prop :=
  Xᴴ * γ 0 + γ 0 * X = 0 ∧ X.trace = 0

def su22Subspace : Submodule ℝ Mat4 := diracSkewSubspace

/-- The extension takes values in the real trace-free Dirac-skew subspace. -/
theorem twistorRep_mem_su22 (X : RMat6) : IsSU22Lie (twistorRep X) :=
  diracSkewSubspace.sum_mem fun p _ =>
    diracSkewSubspace.smul_mem (so24Coordinates X p) (spinGenerator_mem p.val.1 p.val.2)

/-- The spin action takes the matrix commutator to the matrix commutator. -/
theorem twistorRep_lie_hom (X Y : RMat6) (hX : X ∈ so24Subspace) (hY : Y ∈ so24Subspace) :
    twistorRep (X * Y - Y * X) = twistorRep X * twistorRep Y - twistorRep Y * twistorRep X := by
  change twistorRep ⁅X, Y⁆ = ⁅twistorRep X, twistorRep Y⁆
  have hp (p q : ConformalPair) :
      twistorRep ⁅so24Basis p, so24Basis q⁆ = ⁅twistorRep (so24Basis p), twistorRep (so24Basis q)⁆ := by
    simp only [LieRing.of_associative_ring_bracket, so24Basis, so24_commutator_universal,
      map_add, map_sub, map_smul, twistorRep_generator, spinGenerator_bracket]
  let c := so24Coordinates X
  let d := so24Coordinates Y
  have hx : (∑ p : ConformalPair, c p • so24Basis p) = X := so24_expansion X hX
  have hy : (∑ p : ConformalPair, d p • so24Basis p) = Y := so24_expansion Y hY
  rw [← hx, ← hy]
  simp only [sum_lie_sum, map_sum, map_smul, smul_lie, lie_smul, hp]

/-- Restrict the extension to the two metric-skew Lie algebras. -/
def twistorRepRestricted : so24Subspace →ₗ[ℝ] su22Subspace :=
  (twistorRep.comp so24Subspace.subtype).codRestrict su22Subspace
    (fun X => twistorRep_mem_su22 X.val)

set_option maxHeartbeats 1200000 in
theorem twistorRep_bijective_su22 : Function.Bijective twistorRepRestricted := by
  constructor
  · intro X Y h
    have hvalues : twistorRep X.val = twistorRep Y.val :=
      congrArg (fun Z : su22Subspace => Z.val) h
    have hzero : twistorRep (X.val - Y.val) = 0 := by rw [map_sub, hvalues, sub_self]
    change (∑ p : ConformalPair,
      so24Coordinates (X.val - Y.val) p • spinGenerator p.val.1 p.val.2) = 0 at hzero
    simp only [mat4_real_smul] at hzero
    have hcoeff := (Fintype.linearIndependent_iff.mp spinGenerator_independent) _ hzero
    have hz : so24Coordinates (X.val - Y.val) = 0 := by
      ext p
      exact Complex.ofReal_eq_zero.mp (hcoeff p)
    apply so24CoordinateEquiv.injective
    exact sub_eq_zero.mp (by
      change so24Coordinates X.val - so24Coordinates Y.val = 0
      rw [← map_sub, hz])
  · intro Y
    obtain ⟨c, hc⟩ := twistor_su22_real_expansion Y.val Y.property
    let X := so24CoordinateEquiv.symm c
    refine ⟨X, Subtype.ext ?_⟩
    have hcoords : so24Coordinates X.val = c := so24CoordinateEquiv.apply_symm_apply c
    change (∑ p : ConformalPair, so24Coordinates X.val p • spinGenerator p.val.1 p.val.2) = Y.val
    rw [hcoords]
    exact hc

/-- A real linear equivalence that preserves the matrix commutator by
    `twistorRep_lie_hom`. -/
def twistorEquiv : so24Subspace ≃ₗ[ℝ] su22Subspace :=
  LinearEquiv.ofBijective twistorRepRestricted twistorRep_bijective_su22

/-- The spin action on the physical generators in the chosen chiral convention. -/
theorem twistorRep_conformal_generators (μ ν : Fin 4) :
    twistorRep (LorentzGen μ ν) = (1 / 4 : ℂ) • (γ μ * γ ν - γ ν * γ μ) ∧
    twistorRep dilatation = (1 / 2 : ℂ) • gamma5 ∧
    twistorRep (translationGen μ) = Complex.I • (γ μ * PL) ∧
    twistorRep (specialGen μ) = (-Complex.I) • (γ μ * PR) := by
  obtain ⟨hM, hD, hP, hK⟩ := spinGeneratorZ_conformal μ ν
  have hMc := congrArg toComplexMatrix hM
  have hDc := congrArg toComplexMatrix hD
  have hPc := congrArg toComplexMatrix hP
  have hKc := congrArg toComplexMatrix hK
  have htwo : ((2 : GaussianInt) : ℂ) = 2 := map_ofNat GaussianInt.toComplex 2
  simp only [map_add, map_sub, map_mul, map_one, toComplexMatrix_gaussian_smul,
    toComplexMatrix_gamma, toComplexMatrix_gamma5, gaussianI_cast,
    GaussianInt.toComplex_neg, htwo] at hMc hDc hPc hKc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LorentzGen, twistorRep_generator, spinGenerator, ← hMc, smul_smul]
    norm_num
  · rw [dilatation, twistorRep_generator, spinGenerator, hDc]
  · rw [translationGen, map_add, twistorRep_generator, twistorRep_generator]
    simp only [spinGenerator, ← smul_add, hPc, PL, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  · rw [specialGen, map_sub, twistorRep_generator, twistorRep_generator]
    simp only [spinGenerator, ← smul_sub, hKc, PR, Matrix.mul_smul, smul_smul]
    congr 1
    ring

private theorem so24_lie_closed {X Y : RMat6} (hX : X ∈ so24Subspace) (hY : Y ∈ so24Subspace) :
    ⁅X, Y⁆ ∈ so24Subspace := by
  change Xᵀ * eta24 + eta24 * X = 0 at hX
  change Yᵀ * eta24 + eta24 * Y = 0 at hY
  have prod (A B : RMat6) (hA : Aᵀ * eta24 = -(eta24 * A))
      (hB : Bᵀ * eta24 = -(eta24 * B)) : (A * B)ᵀ * eta24 = eta24 * (B * A) := by
    calc
      (A * B)ᵀ * eta24 = Bᵀ * (Aᵀ * eta24) := by rw [Matrix.transpose_mul, mul_assoc]
      _ = -(Bᵀ * eta24) * A := by rw [hA, Matrix.mul_neg, Matrix.neg_mul, mul_assoc]
      _ = eta24 * (B * A) := by rw [hB, neg_neg, mul_assoc]
  change (X * Y - Y * X)ᵀ * eta24 + eta24 * (X * Y - Y * X) = 0
  simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub,
    prod X Y (eq_neg_of_add_eq_zero_left hX) (eq_neg_of_add_eq_zero_left hY),
    prod Y X (eq_neg_of_add_eq_zero_left hY) (eq_neg_of_add_eq_zero_left hX)]
  abel

/-- The metric-preserving matrix Lie algebra. -/
def so24LieAlgebra : LieSubalgebra ℝ RMat6 where
  __ := so24Subspace
  lie_mem' := so24_lie_closed

/-- The trace-free Dirac-skew matrix Lie algebra. -/
def su22LieAlgebra : LieSubalgebra ℝ Mat4 where
  __ := su22Subspace
  lie_mem' {X Y} hX hY := by
    obtain ⟨x, hx⟩ := twistorRep_bijective_su22.2 (⟨X, hX⟩ : su22Subspace)
    obtain ⟨y, hy⟩ := twistorRep_bijective_su22.2 (⟨Y, hY⟩ : su22Subspace)
    have hX' : twistorRep x.val = X := congrArg (fun Z : su22Subspace => Z.val) hx
    have hY' : twistorRep y.val = Y := congrArg (fun Z : su22Subspace => Z.val) hy
    change IsSU22Lie (X * Y - Y * X)
    rw [← hX', ← hY', ← twistorRep_lie_hom _ _ x.property y.property]
    exact twistorRep_mem_su22 _

/-- The real Lie algebra equivalence specified by the chiral spin action. -/
def twistorLieEquiv : so24LieAlgebra ≃ₗ⁅ℝ⁆ su22LieAlgebra where
  __ := (show so24LieAlgebra ≃ₗ[ℝ] su22LieAlgebra from twistorEquiv)
  map_lie' {X Y} := Subtype.ext (twistorRep_lie_hom X.val Y.val X.property Y.property)

end D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
