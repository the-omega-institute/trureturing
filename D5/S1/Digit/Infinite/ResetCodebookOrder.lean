/- GID: D5/S1/Digit/Infinite/ResetCodebookOrder
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ResetCodebookOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive matrix comparison and source return scalar estimates. -/

import D5.S1.Digit.Infinite.ResetCodebookModel
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Order.IntermediateValue
local notation "g_bounds" => And.intro D5.S1.Digit.Infinite.SixWindowForcing.algebra.2.1 D5.S1.Digit.Infinite.SixWindowForcing.algebra.2.2.1
local notation "g_relation" => D5.S1.Digit.Infinite.SixWindowForcing.algebra.1
local notation "g_eq" => D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations.2.2.2.1
local notation "t_sq" => D5.S1.Digit.Infinite.SixWindowForcing.algebra.2.2.2.2
local notation "t_linear" => D5.S1.Digit.Infinite.SixWindowForcing.algebra.2.2.2.1
local notation "complexify" => Complex.ofRealHom.mapMatrix
local notation "radius" => fun A => (spectralRadius ℂ (Complex.ofRealHom.mapMatrix A)).toReal
local notation "Vertex" => fun (lang : Set (ℤ → Bool)) (n : ℕ) =>
  {v : Fin n → Bool // ∃ w∈lang, ∃ i : ℤ, D5.S1.Digit.Infinite.ResetCodebook.Transfer.history n w i=v}
set_option autoImplicit false
open scoped Matrix.Norms.Operator Topology ENNReal NNReal
open Filter
namespace D5.S1.Digit.Infinite.ResetCodebook.Spectral
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
lemma radius_finite (A : Matrix ι ι ℝ) : spectralRadius ℂ (complexify A) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectrum.spectralRadius_le_nnnorm _)
lemma gelfand (A : Matrix ι ι ℝ) :
    Tendsto (fun k : ℕ => ‖complexify A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (radius A)) := by
  have hh := (ENNReal.tendsto_toReal (radius_finite A)).comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A))
  simpa only [ Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using hh
lemma positive_pow (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    ∀ i j, 0 ≤ (A^k) i j := by
  induction k with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split <;> positivity
  | succ k ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hA i x) (ih x j))
lemma positive_pow_le (A B : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) : ∀ i j, (A^k) i j ≤ (B^k) i j := by
  induction k with
  | zero => intro i j; simp
  | succ k ih =>
    intro i j
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul (hAB i x) (ih x j) (positive_pow A hA k x j)
      ((hA i x).trans (hAB i x))
lemma positive_norm_le (A B : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) : ‖complexify A‖ ≤ ‖complexify B‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  apply le_trans _ (Finset.le_sup hi)
  apply Finset.sum_le_sum
  intro j _
  change ‖(A i j : ℂ)‖₊ ≤ ‖(B i j : ℂ)‖₊
  apply NNReal.coe_le_coe.mp
  change ‖(A i j : ℂ)‖ ≤ ‖(B i j : ℂ)‖
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j),
    abs_of_nonneg ((hA i j).trans (hAB i j))] using hAB i j
lemma radius_mono (A B : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) : radius A ≤ radius B := by
  apply le_of_tendsto_of_tendsto (gelfand A) (gelfand B)
  apply Eventually.of_forall
  intro k
  apply Real.rpow_le_rpow (norm_nonneg _) _ (by positivity)
  change ‖Complex.ofRealHom.mapMatrix A ^ k‖ ≤ ‖Complex.ofRealHom.mapMatrix B ^ k‖
  rw [← map_pow Complex.ofRealHom.mapMatrix A k, ← map_pow Complex.ofRealHom.mapMatrix B k]
  exact positive_norm_le (A^k) (B^k) (positive_pow A hA k) (positive_pow_le A B hA hAB k)
end
end D5.S1.Digit.Infinite.ResetCodebook.Spectral
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Words.Powers (wordPower)
namespace D5.S1.Digit.Infinite.ResetCodebook
theorem lambda_linear : lambda=(1-g)/20 := by unfold lambda; rw [t_sq]; ring
theorem g_tight : 236067/1000000 < g ∧ g < 236068/1000000 := by
  have hb:=g_bounds
  have hr:=g_relation
  constructor <;> nlinarith
private theorem off_five : offset fiveLabel = ((1/2 : ℝ) + (-1/2 : ℝ)*g) := by
  norm_num [offset,fiveLabel]
  rw [t_sq]; ring
private theorem off_null : offset nullLabel = ((0 : ℝ) + (0 : ℝ)*g) := by
  norm_num [offset,nullLabel]
private theorem off_three : offset threeLabel = ((-1/2 : ℝ) + (-1/2 : ℝ)*g) := by
  norm_num [offset,threeLabel]
  rw [t_linear]; ring
private theorem off_two : offset twoLabel = ((1 : ℝ) + (0 : ℝ)*g) := by
  norm_num [offset,twoLabel]
  intro hn
  have hx := congrArg (fun i : Fin 3 => i.val) hn
  norm_num at hx
private theorem off_twoFive : offset twoFiveLabel = ((3/2 : ℝ) + (-1/2 : ℝ)*g) := by
  norm_num [offset,twoFiveLabel]
  rw [t_sq]; ring
private theorem U_center_6 : wordScalar (U.drop 6) c0=((1/5 : ℝ) + (1/5 : ℝ)*g) := by
  change c0 = _
  rw [center]; ring
private theorem U_center_5 : wordScalar (U.drop 5) c0=((-7/10 : ℝ) + (1/10 : ℝ)*g) := by
  change branch threeLabel (wordScalar (U.drop 6) c0)=_
  rw [branch, off_three, U_center_6]
  nlinarith [g_relation]
private theorem U_center_4 : wordScalar (U.drop 4) c0=((-3/5 : ℝ) + (3/5 : ℝ)*g) := by
  change branch threeLabel (wordScalar (U.drop 5) c0)=_
  rw [branch, off_three, U_center_5]
  nlinarith [g_relation]
private theorem U_center_3 : wordScalar (U.drop 3) c0=((-3/5 : ℝ) + (3 : ℝ)*g) := by
  change branch nullLabel (wordScalar (U.drop 4) c0)=_
  rw [branch, off_null, U_center_4]
  nlinarith [g_relation]
private theorem U_center_2 : wordScalar (U.drop 2) c0=((-7/2 : ℝ) + (121/10 : ℝ)*g) := by
  change branch threeLabel (wordScalar (U.drop 3) c0)=_
  rw [branch, off_three, U_center_3]
  nlinarith [g_relation]
private theorem U_center_1 : wordScalar (U.drop 1) c0=((-121/10 : ℝ) + (519/10 : ℝ)*g) := by
  change branch nullLabel (wordScalar (U.drop 2) c0)=_
  rw [branch, off_null, U_center_2]
  nlinarith [g_relation]
private theorem U_center_0 : wordScalar (U.drop 0) c0=((-257/5 : ℝ) + (1096/5 : ℝ)*g) := by
  change branch fiveLabel (wordScalar (U.drop 1) c0)=_
  rw [branch, off_five, U_center_1]
  nlinarith [g_relation]
theorem U_scalar_0 (x : ℝ) : wordScalar (U.drop 0) x = ((-257/5 : ℝ) + (1096/5 : ℝ)*g) + (-g)^6*(x-c0) := by
  have h1:=wordScalar_affine (U.drop 0) x
  have h2:=wordScalar_affine (U.drop 0) c0
  have h3:=U_center_0
  norm_num only [U, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [U, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem U_scalar_1 (x : ℝ) : wordScalar (U.drop 1) x = ((-121/10 : ℝ) + (519/10 : ℝ)*g) + (-g)^5*(x-c0) := by
  have h1:=wordScalar_affine (U.drop 1) x
  have h2:=wordScalar_affine (U.drop 1) c0
  have h3:=U_center_1
  norm_num only [U, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [U, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem U_scalar_2 (x : ℝ) : wordScalar (U.drop 2) x = ((-7/2 : ℝ) + (121/10 : ℝ)*g) + (-g)^4*(x-c0) := by
  have h1:=wordScalar_affine (U.drop 2) x
  have h2:=wordScalar_affine (U.drop 2) c0
  have h3:=U_center_2
  norm_num only [U, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [U, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem U_scalar_3 (x : ℝ) : wordScalar (U.drop 3) x = ((-3/5 : ℝ) + (3 : ℝ)*g) + (-g)^3*(x-c0) := by
  have h1:=wordScalar_affine (U.drop 3) x
  have h2:=wordScalar_affine (U.drop 3) c0
  have h3:=U_center_3
  norm_num only [U, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [U, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem U_scalar_4 (x : ℝ) : wordScalar (U.drop 4) x = ((-3/5 : ℝ) + (3/5 : ℝ)*g) + (-g)^2*(x-c0) := by
  have h1:=wordScalar_affine (U.drop 4) x
  have h2:=wordScalar_affine (U.drop 4) c0
  have h3:=U_center_4
  norm_num only [U, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [U, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem U_scalar_5 (x : ℝ) : wordScalar (U.drop 5) x = ((-7/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0) := by
  have h1:=wordScalar_affine (U.drop 5) x
  have h2:=wordScalar_affine (U.drop 5) c0
  have h3:=U_center_5
  norm_num only [U, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [U, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
private theorem V_center_6 : wordScalar (V.drop 6) c0=((1/5 : ℝ) + (1/5 : ℝ)*g) := by
  change c0 = _
  rw [center]; ring
private theorem V_center_5 : wordScalar (V.drop 5) c0=((-7/10 : ℝ) + (1/10 : ℝ)*g) := by
  change branch threeLabel (wordScalar (V.drop 6) c0)=_
  rw [branch, off_three, V_center_6]
  nlinarith [g_relation]
private theorem V_center_4 : wordScalar (V.drop 4) c0=((-1/10 : ℝ) + (11/10 : ℝ)*g) := by
  change branch nullLabel (wordScalar (V.drop 5) c0)=_
  rw [branch, off_null, V_center_5]
  nlinarith [g_relation]
private theorem V_center_3 : wordScalar (V.drop 3) c0=((-3/5 : ℝ) + (4 : ℝ)*g) := by
  change branch fiveLabel (wordScalar (V.drop 4) c0)=_
  rw [branch, off_five, V_center_4]
  nlinarith [g_relation]
private theorem V_center_2 : wordScalar (V.drop 2) c0=((-9/2 : ℝ) + (161/10 : ℝ)*g) := by
  change branch threeLabel (wordScalar (V.drop 3) c0)=_
  rw [branch, off_three, V_center_3]
  nlinarith [g_relation]
private theorem V_center_1 : wordScalar (V.drop 1) c0=((-83/5 : ℝ) + (342/5 : ℝ)*g) := by
  change branch threeLabel (wordScalar (V.drop 2) c0)=_
  rw [branch, off_three, V_center_2]
  nlinarith [g_relation]
private theorem V_center_0 : wordScalar (V.drop 0) c0=((-342/5 : ℝ) + (1451/5 : ℝ)*g) := by
  change branch nullLabel (wordScalar (V.drop 1) c0)=_
  rw [branch, off_null, V_center_1]
  nlinarith [g_relation]
theorem V_scalar_0 (x : ℝ) : wordScalar (V.drop 0) x = ((-342/5 : ℝ) + (1451/5 : ℝ)*g) + (-g)^6*(x-c0) := by
  have h1:=wordScalar_affine (V.drop 0) x
  have h2:=wordScalar_affine (V.drop 0) c0
  have h3:=V_center_0
  norm_num only [V, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [V, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem V_scalar_1 (x : ℝ) : wordScalar (V.drop 1) x = ((-83/5 : ℝ) + (342/5 : ℝ)*g) + (-g)^5*(x-c0) := by
  have h1:=wordScalar_affine (V.drop 1) x
  have h2:=wordScalar_affine (V.drop 1) c0
  have h3:=V_center_1
  norm_num only [V, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [V, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem V_scalar_2 (x : ℝ) : wordScalar (V.drop 2) x = ((-9/2 : ℝ) + (161/10 : ℝ)*g) + (-g)^4*(x-c0) := by
  have h1:=wordScalar_affine (V.drop 2) x
  have h2:=wordScalar_affine (V.drop 2) c0
  have h3:=V_center_2
  norm_num only [V, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [V, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem V_scalar_3 (x : ℝ) : wordScalar (V.drop 3) x = ((-3/5 : ℝ) + (4 : ℝ)*g) + (-g)^3*(x-c0) := by
  have h1:=wordScalar_affine (V.drop 3) x
  have h2:=wordScalar_affine (V.drop 3) c0
  have h3:=V_center_3
  norm_num only [V, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [V, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem V_scalar_4 (x : ℝ) : wordScalar (V.drop 4) x = ((-1/10 : ℝ) + (11/10 : ℝ)*g) + (-g)^2*(x-c0) := by
  have h1:=wordScalar_affine (V.drop 4) x
  have h2:=wordScalar_affine (V.drop 4) c0
  have h3:=V_center_4
  norm_num only [V, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [V, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem V_scalar_5 (x : ℝ) : wordScalar (V.drop 5) x = ((-7/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0) := by
  have h1:=wordScalar_affine (V.drop 5) x
  have h2:=wordScalar_affine (V.drop 5) c0
  have h3:=V_center_5
  norm_num only [V, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [V, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
private theorem C_center_20 : wordScalar (C.drop 20) c0=((1/5 : ℝ) + (1/5 : ℝ)*g) := by
  change c0 = _
  rw [center]; ring
private theorem C_center_19 : wordScalar (C.drop 19) c0=((3/10 : ℝ) + (1/10 : ℝ)*g) := by
  change branch fiveLabel (wordScalar (C.drop 20) c0)=_
  rw [branch, off_five, C_center_20]
  nlinarith [g_relation]
private theorem C_center_18 : wordScalar (C.drop 18) c0=((-1/10 : ℝ) + (1/10 : ℝ)*g) := by
  change branch nullLabel (wordScalar (C.drop 19) c0)=_
  rw [branch, off_null, C_center_19]
  nlinarith [g_relation]
private theorem C_center_17 : wordScalar (C.drop 17) c0=((-3/5 : ℝ) + (0 : ℝ)*g) := by
  change branch threeLabel (wordScalar (C.drop 18) c0)=_
  rw [branch, off_three, C_center_18]
  nlinarith [g_relation]
private theorem C_center_16 : wordScalar (C.drop 16) c0=((-1/2 : ℝ) + (1/10 : ℝ)*g) := by
  change branch threeLabel (wordScalar (C.drop 17) c0)=_
  rw [branch, off_three, C_center_17]
  nlinarith [g_relation]
private theorem C_center_15 : wordScalar (C.drop 15) c0=((7/5 : ℝ) + (2/5 : ℝ)*g) := by
  change branch twoFiveLabel (wordScalar (C.drop 16) c0)=_
  rw [branch, off_twoFive, C_center_16]
  nlinarith [g_relation]
private theorem C_center_14 : wordScalar (C.drop 14) c0=((3/5 : ℝ) + (1/5 : ℝ)*g) := by
  change branch twoLabel (wordScalar (C.drop 15) c0)=_
  rw [branch, off_two, C_center_15]
  nlinarith [g_relation]
private theorem C_center_13 : wordScalar (C.drop 13) c0=((4/5 : ℝ) + (1/5 : ℝ)*g) := by
  change branch twoLabel (wordScalar (C.drop 14) c0)=_
  rw [branch, off_two, C_center_14]
  nlinarith [g_relation]
private theorem C_center_12 : wordScalar (C.drop 12) c0=((-1/5 : ℝ) + (0 : ℝ)*g) := by
  change branch nullLabel (wordScalar (C.drop 13) c0)=_
  rw [branch, off_null, C_center_13]
  nlinarith [g_relation]
private theorem C_center_11 : wordScalar (C.drop 11) c0=((0 : ℝ) + (1/5 : ℝ)*g) := by
  change branch nullLabel (wordScalar (C.drop 12) c0)=_
  rw [branch, off_null, C_center_12]
  nlinarith [g_relation]
private theorem C_center_10 : wordScalar (C.drop 10) c0=((3/10 : ℝ) + (3/10 : ℝ)*g) := by
  change branch fiveLabel (wordScalar (C.drop 11) c0)=_
  rw [branch, off_five, C_center_11]
  nlinarith [g_relation]
private theorem C_center_9 : wordScalar (C.drop 9) c0=((6/5 : ℝ) + (2/5 : ℝ)*g) := by
  change branch twoFiveLabel (wordScalar (C.drop 10) c0)=_
  rw [branch, off_twoFive, C_center_10]
  nlinarith [g_relation]
private theorem C_center_8 : wordScalar (C.drop 8) c0=((-9/10 : ℝ) + (-1/10 : ℝ)*g) := by
  change branch threeLabel (wordScalar (C.drop 9) c0)=_
  rw [branch, off_three, C_center_9]
  nlinarith [g_relation]
private theorem C_center_7 : wordScalar (C.drop 7) c0=((-2/5 : ℝ) + (0 : ℝ)*g) := by
  change branch threeLabel (wordScalar (C.drop 8) c0)=_
  rw [branch, off_three, C_center_8]
  nlinarith [g_relation]
private theorem C_center_6 : wordScalar (C.drop 6) c0=((-1/2 : ℝ) + (-1/10 : ℝ)*g) := by
  change branch threeLabel (wordScalar (C.drop 7) c0)=_
  rw [branch, off_three, C_center_7]
  nlinarith [g_relation]
private theorem C_center_5 : wordScalar (C.drop 5) c0=((1/10 : ℝ) + (1/10 : ℝ)*g) := by
  change branch nullLabel (wordScalar (C.drop 6) c0)=_
  rw [branch, off_null, C_center_6]
  nlinarith [g_relation]
private theorem C_center_4 : wordScalar (C.drop 4) c0=((9/10 : ℝ) + (3/10 : ℝ)*g) := by
  change branch twoLabel (wordScalar (C.drop 5) c0)=_
  rw [branch, off_two, C_center_5]
  nlinarith [g_relation]
private theorem C_center_3 : wordScalar (C.drop 3) c0=((7/10 : ℝ) + (3/10 : ℝ)*g) := by
  change branch twoLabel (wordScalar (C.drop 4) c0)=_
  rw [branch, off_two, C_center_4]
  nlinarith [g_relation]
private theorem C_center_2 : wordScalar (C.drop 2) c0=((-4/5 : ℝ) + (0 : ℝ)*g) := by
  change branch threeLabel (wordScalar (C.drop 3) c0)=_
  rw [branch, off_three, C_center_3]
  nlinarith [g_relation]
private theorem C_center_1 : wordScalar (C.drop 1) c0=((1/2 : ℝ) + (3/10 : ℝ)*g) := by
  change branch fiveLabel (wordScalar (C.drop 2) c0)=_
  rw [branch, off_five, C_center_2]
  nlinarith [g_relation]
private theorem C_center_0 : wordScalar (C.drop 0) c0=((1/5 : ℝ) + (1/5 : ℝ)*g) := by
  change branch fiveLabel (wordScalar (C.drop 1) c0)=_
  rw [branch, off_five, C_center_1]
  nlinarith [g_relation]
theorem C_scalar_0 (x : ℝ) : wordScalar (C.drop 0) x = ((1/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^20*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 0) x
  have h2:=wordScalar_affine (C.drop 0) c0
  have h3:=C_center_0
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_1 (x : ℝ) : wordScalar (C.drop 1) x = ((1/2 : ℝ) + (3/10 : ℝ)*g) + (-g)^19*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 1) x
  have h2:=wordScalar_affine (C.drop 1) c0
  have h3:=C_center_1
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_2 (x : ℝ) : wordScalar (C.drop 2) x = ((-4/5 : ℝ) + (0 : ℝ)*g) + (-g)^18*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 2) x
  have h2:=wordScalar_affine (C.drop 2) c0
  have h3:=C_center_2
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_3 (x : ℝ) : wordScalar (C.drop 3) x = ((7/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^17*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 3) x
  have h2:=wordScalar_affine (C.drop 3) c0
  have h3:=C_center_3
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_4 (x : ℝ) : wordScalar (C.drop 4) x = ((9/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^16*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 4) x
  have h2:=wordScalar_affine (C.drop 4) c0
  have h3:=C_center_4
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_5 (x : ℝ) : wordScalar (C.drop 5) x = ((1/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^15*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 5) x
  have h2:=wordScalar_affine (C.drop 5) c0
  have h3:=C_center_5
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_6 (x : ℝ) : wordScalar (C.drop 6) x = ((-1/2 : ℝ) + (-1/10 : ℝ)*g) + (-g)^14*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 6) x
  have h2:=wordScalar_affine (C.drop 6) c0
  have h3:=C_center_6
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_7 (x : ℝ) : wordScalar (C.drop 7) x = ((-2/5 : ℝ) + (0 : ℝ)*g) + (-g)^13*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 7) x
  have h2:=wordScalar_affine (C.drop 7) c0
  have h3:=C_center_7
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_8 (x : ℝ) : wordScalar (C.drop 8) x = ((-9/10 : ℝ) + (-1/10 : ℝ)*g) + (-g)^12*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 8) x
  have h2:=wordScalar_affine (C.drop 8) c0
  have h3:=C_center_8
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_9 (x : ℝ) : wordScalar (C.drop 9) x = ((6/5 : ℝ) + (2/5 : ℝ)*g) + (-g)^11*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 9) x
  have h2:=wordScalar_affine (C.drop 9) c0
  have h3:=C_center_9
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_10 (x : ℝ) : wordScalar (C.drop 10) x = ((3/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^10*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 10) x
  have h2:=wordScalar_affine (C.drop 10) c0
  have h3:=C_center_10
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_11 (x : ℝ) : wordScalar (C.drop 11) x = ((0 : ℝ) + (1/5 : ℝ)*g) + (-g)^9*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 11) x
  have h2:=wordScalar_affine (C.drop 11) c0
  have h3:=C_center_11
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_12 (x : ℝ) : wordScalar (C.drop 12) x = ((-1/5 : ℝ) + (0 : ℝ)*g) + (-g)^8*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 12) x
  have h2:=wordScalar_affine (C.drop 12) c0
  have h3:=C_center_12
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_13 (x : ℝ) : wordScalar (C.drop 13) x = ((4/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^7*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 13) x
  have h2:=wordScalar_affine (C.drop 13) c0
  have h3:=C_center_13
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_14 (x : ℝ) : wordScalar (C.drop 14) x = ((3/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^6*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 14) x
  have h2:=wordScalar_affine (C.drop 14) c0
  have h3:=C_center_14
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_15 (x : ℝ) : wordScalar (C.drop 15) x = ((7/5 : ℝ) + (2/5 : ℝ)*g) + (-g)^5*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 15) x
  have h2:=wordScalar_affine (C.drop 15) c0
  have h3:=C_center_15
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_16 (x : ℝ) : wordScalar (C.drop 16) x = ((-1/2 : ℝ) + (1/10 : ℝ)*g) + (-g)^4*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 16) x
  have h2:=wordScalar_affine (C.drop 16) c0
  have h3:=C_center_16
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_17 (x : ℝ) : wordScalar (C.drop 17) x = ((-3/5 : ℝ) + (0 : ℝ)*g) + (-g)^3*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 17) x
  have h2:=wordScalar_affine (C.drop 17) c0
  have h3:=C_center_17
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_18 (x : ℝ) : wordScalar (C.drop 18) x = ((-1/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^2*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 18) x
  have h2:=wordScalar_affine (C.drop 18) c0
  have h3:=C_center_18
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
theorem C_scalar_19 (x : ℝ) : wordScalar (C.drop 19) x = ((3/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0) := by
  have h1:=wordScalar_affine (C.drop 19) x
  have h2:=wordScalar_affine (C.drop 19) c0
  have h3:=C_center_19
  norm_num only [C, List.drop, List.length_cons, List.length_nil] at h1 h2
  simp only [C, List.drop] at h3 ⊢
  linear_combination h1 - h2 + h3
private theorem power_six : g^6=305-1292*g := by
  linear_combination (g^4-4*g^3+17*g^2-72*g+305)*g_relation
theorem U_map (D : ℝ) : wordScalar U (coord false D)=coord false (A false+rho*D) := by
  have he := U_scalar_0 (coord false D)
  change wordScalar U (coord false D)=_ at he
  rw [he]
  norm_num [coord,A,h,rho,pow_succ,center]
  linear_combination (-6*g/380+39/380)*power_six + (102/5:ℝ)*g_relation
theorem V_map (D : ℝ) : wordScalar V (coord true D)=coord true (A true+rho*D) := by
  have he := V_scalar_0 (coord true D)
  change wordScalar V (coord true D)=_ at he
  rw [he]
  norm_num [coord,A,h,rho,pow_succ,center]
  linear_combination (-31*g/380-46/380)*power_six + (527/5:ℝ)*g_relation
theorem C_map (low : Bool) (D : ℝ) : wordScalar C (coord low D)=coord low (chi*D) := by
  have he:=C_scalar_0 (coord low D)
  change wordScalar C (coord low D)=_ at he
  rw [he]
  cases low <;> simp only [coord,chi, Bool.false_eq_true,if_false,if_true,Even.neg_pow (by decide : Even 20), center] <;> ring
end D5.S1.Digit.Infinite.ResetCodebook
set_option autoImplicit false
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
namespace D5.S1.Digit.Infinite.ResetCodebook
private theorem inside_target (l u x B : ℝ) (hlu : l<u) (hB : 0<B)
    (hc : intervalDistance x l u < B) :
    ∃ y : ℝ, l<y ∧ y<u ∧ |x-y|<B := by
  have hl : l-x<B := (le_max_left _ _).trans_lt hc
  have hu : x-u<B := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hc
  have hgap : max l (x-B)< min u (x+B) := by
    apply max_lt
    · exact lt_min hlu (by linarith)
    · exact lt_min (by linarith) (by linarith)
  obtain ⟨y,hy1,hy2⟩:=exists_between hgap
  refine ⟨y,(le_max_left _ _).trans_lt hy1,hy2.trans_le (min_le_left _ _),?_⟩
  rw [abs_lt]
  constructor
  · have hy:=hy2.trans_le (min_le_right _ _); linarith
  · have hy:=(le_max_right _ _).trans_lt hy1; linarith
private theorem cells_positive (i : Fin 6) : cellLower i<cellUpper i := by
  have hg:=g_bounds
  fin_cases i <;> norm_num [cellLower,cellUpper,cuts]
  all_goals simp only [lambda_linear,t_sq]
  all_goals try simp only [t_linear]
  all_goals linarith
private theorem cell_support (i : Fin 6) : -1≤cellLower i ∧ cellUpper i≤1+t := by
  have hg:=g_bounds
  fin_cases i <;> norm_num [cellLower,cellUpper,cuts]
  all_goals simp only [lambda_linear,t_sq]
  all_goals try simp only [t_linear]
  all_goals first | constructor <;> linarith | linarith
-- All departure errors are chosen against the successive tails of the same source.
theorem actual_errors (w : List Label) (r : List (Fin 6)) (x tail : LegalDigits)
    (hp : addressPrefix w x tail) (hlen : w.length=r.length)
    (b eps : ℝ) (heps : 0<eps) (hb : 0<b-eps)
    (hc : wordCost w r (kappa tail)≤b-2*eps)
    (Q : ℝ→Fin 6) (hQ : ∀ i y, y∈Set.Ioo (cellLower i) (cellUpper i) → Q y=i) :
    ∃ errors : List ℝ, errors.length=r.length ∧
      ∀ p : Fin r.length, |(errors[p.val]?.getD 0)|<b-eps ∧
        Q (min (1+t) (max (-1) (kappa (originalT^[p.val] x)+(errors[p.val]?.getD 0))))=r[p.val] := by
  induction w generalizing r x with
  | nil =>
    have hr : r=[] := List.length_eq_zero_iff.mp hlen.symm
    subst r
    exact ⟨[],rfl,fun p => Fin.elim0 p⟩
  | cons l w ih =>
    cases r with
    | nil => simp at hlen
    | cons i r =>
      have hlen' : w.length=r.length := by simpa using hlen
      have hc1 : intervalDistance (kappa x) (cellLower i) (cellUpper i)≤b-2*eps := by
        rw [prefix_scalar _ _ _ hp]
        exact (le_max_left _ _).trans hc
      have hc2 : wordCost w r (kappa tail)≤b-2*eps := (le_max_right _ _).trans hc
      obtain ⟨y,hy1,hy2,hy3⟩:=inside_target _ _ _ (b-eps) (cells_positive i) hb
        (hc1.trans_lt (by linarith))
      obtain ⟨es,hlenes,hes⟩:=ih r (originalT x) hp.2 hlen' hc2
      refine ⟨(y-kappa x)::es,by simp [hlenes],?_⟩
      intro p
      by_cases hp0 : p.val=0
      · have hpi : p=0 := Fin.ext hp0
        subst p
        simp only [List.getElem?_cons_zero,Option.getD_some,Fin.val_zero,Function.iterate_zero_apply]
        constructor
        · simpa [abs_sub_comm] using hy3
        · have hs:=cell_support i
          have hyX : -1≤y ∧ y≤1+t := ⟨hs.1.trans hy1.le,hy2.le.trans hs.2⟩
          rw [show kappa x+(y-kappa x)=y by ring,max_eq_right hyX.1,min_eq_right hyX.2]
          exact hQ i y ⟨hy1,hy2⟩
      · obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero hp0
        have hnr : n<r.length := by have := p.isLt; simp only [List.length_cons] at this; omega
        have he:=hes ⟨n,hnr⟩
        simpa [hn,Function.iterate_succ_apply] using he
end D5.S1.Digit.Infinite.ResetCodebook
