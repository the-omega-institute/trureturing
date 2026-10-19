/- GID: D5/S3/Quantum/Matrix/GanKimConjectureRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/GanKimConjectureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/GanKimConjectureRefutation.conjecture; result=D5/S3/Quantum/Matrix/GanKimConjectureRefutation.result; claim=D5/S3/Quantum/Matrix/GanKimConjectureRefutation.conjecture
   digest: Gan and Kim's Wasserstein power monotonicity fails at every interior weight. -/

import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Matrix.WassersteinMean
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! An exact two-dimensional obstruction at powers one half and one. -/

noncomputable section
open Matrix Filter Topology
open scoped MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Matrix.GanKimConjectureRefutation
open WassersteinMean AlternativeMeanLinearization
open SpectralPower (mpow LE mpow_one mpow_two posDef_two)
open D5.S3.Quantum.Hiai.PsiMeanTraceConcavity (geometricMean)

/-- Conjecture 5.7: decreasing weak-log-majorization convergence as p decreases to zero. -/
def conjecture : Prop :=
  ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ), A.PosDef → B.PosDef →
    ∀ t : ℝ, 0 < t → t < 1 →
      (∀ p q : ℝ, 0 < p → p < q →
        weakLogMajorization (powerMean A B t p) (powerMean A B t q)) ∧
      Tendsto (fun p : ℝ => powerMean A B t p) (𝓝[>] 0) (𝓝 (LE t A B))

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
private def block (a b d : ℝ) : Mat := !![(a : ℂ), (b : ℂ); (b : ℂ), (d : ℂ)]
private def P : Mat := block 9 0 1
private def Q : Mat := block 5 4 5
private def A : Mat := block 81 0 1
private def B : Mat := block 41 40 41
private def T₁ : Mat := (1 / Real.sqrt 17 : ℝ) • block 3 2 7
private def T₂ : Mat := (1 / Real.sqrt 881 : ℝ) • block 21 20 61

private lemma block_pos {a b d : ℝ} (ha : 0 < a - b) (hd : 0 < d - b)
    (hb : 0 ≤ b) : (block a b d).PosDef := by
  apply posDef_two
  · linarith
  · have hprod : 0 < (a - b) * (d - b) := mul_pos ha hd
    have hleft : 0 ≤ b * (a - b) := mul_nonneg hb ha.le
    have hright : 0 ≤ b * (d - b) := mul_nonneg hb hd.le
    nlinarith

private lemma P_pos : P.PosDef := block_pos (by norm_num) (by norm_num) (by norm_num)
private lemma Q_pos : Q.PosDef := block_pos (by norm_num) (by norm_num) (by norm_num)
private lemma A_pos : A.PosDef := block_pos (by norm_num) (by norm_num) (by norm_num)
private lemma B_pos : B.PosDef := block_pos (by norm_num) (by norm_num) (by norm_num)

private lemma squares : P * P = A ∧ Q * Q = B := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, Q, A, B, block, Matrix.mul_apply, Fin.sum_univ_two]

private lemma half_powers : mpow A (1 / 2) = P ∧ mpow B (1 / 2) = Q := by
  constructor
  · rw [mpow, ← CFC.rpow_eq_cfc_real A_pos.posSemidef.nonneg, ← CFC.sqrt_eq_rpow]
    exact CFC.sqrt_unique squares.1 P_pos.posSemidef.nonneg
  · rw [mpow, ← CFC.rpow_eq_cfc_real B_pos.posSemidef.nonneg, ← CFC.sqrt_eq_rpow]
    exact CFC.sqrt_unique squares.2 Q_pos.posSemidef.nonneg

open scoped Matrix.Norms.L2Operator in
private lemma geometric_inverse {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) : geometricMean (1 / 2) X⁻¹ Y = gmInv X Y := by
  have hS : (CFC.rpow X (1 / 2)).PosDef :=
    (hX.isStrictlyPositive.rpow X (1 / 2)).posDef
  have hM : (CFC.rpow X (1 / 2) * Y * CFC.rpow X (1 / 2)).PosDef := by
    simpa only [star_eq_conjTranspose, hS.isHermitian.eq] using
      hS.isUnit.posDef_star_right_conjugate_iff.mpr hY
  have hinv (s : ℝ) : CFC.rpow X⁻¹ s = CFC.rpow X (-s) := by
    rw [Matrix.nonsing_inv_eq_ringInverse,
      CFC.inverse_eq_rpow_neg_one hX.isStrictlyPositive]
    exact (CFC.rpow_rpow X (-1) s (by norm_num) hX.isStrictlyPositive).trans
      (congrArg (CFC.rpow X) (by ring : (-1 : ℝ) * s = -s))
  have hi₁ : CFC.rpow X⁻¹ (1 / 2) = CFC.rpow X (-(1 / 2)) := hinv _
  have hi₂ : CFC.rpow X⁻¹ (-1 / 2) = CFC.rpow X (1 / 2) := by
    simpa only [neg_div, neg_neg] using hinv (-1 / 2)
  have hp {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.PosSemidef) (s : ℝ) :
      CFC.rpow Z s = cfc (fun x : ℝ => x ^ s) Z :=
    CFC.rpow_eq_cfc_real hZ.nonneg
  unfold geometricMean
  change CFC.rpow X⁻¹ (1 / 2) *
    CFC.rpow (CFC.rpow X⁻¹ (-1 / 2) * Y * CFC.rpow X⁻¹ (-1 / 2)) (1 / 2) *
    CFC.rpow X⁻¹ (1 / 2) = gmInv X Y
  rw [hi₁, hi₂, hp hM.posSemidef]
  simp only [hp hX.posSemidef, gmInv]

private lemma transports : geometricMean (1 / 2) P⁻¹ Q = T₁ ∧ geometricMean (1 / 2) A⁻¹ B = T₂ := by
  have h17 : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have h881 : 0 < Real.sqrt 881 := Real.sqrt_pos.mpr (by norm_num)
  have sq17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have sq881 := Real.sq_sqrt (show (0 : ℝ) ≤ 881 by norm_num)
  constructor
  · rw [geometric_inverse P_pos Q_pos]
    apply riccati_unique P_pos
    · exact (block_pos (by norm_num) (by norm_num) (by norm_num)).smul (one_div_pos.mpr h17)
    · ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [T₁, P, Q, block, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;>
        field_simp [ne_of_gt h17] <;> nlinarith
  · rw [geometric_inverse A_pos B_pos]
    apply riccati_unique A_pos
    · exact (block_pos (by norm_num) (by norm_num) (by norm_num)).smul (one_div_pos.mpr h881)
    · ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [T₂, A, B, block, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;>
        field_simp [ne_of_gt h881] <;> nlinarith

private lemma mean_factor {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) (t : ℝ) :
    wassersteinMean X Y t = ((1 - t) • 1 + t • gmInv X Y) * X *
      ((1 - t) • 1 + t • gmInv X Y) := by
  rw [wassersteinMean, geometric_inverse hX hY]
  have he := (riccati hX hY).2
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [he]
  module

private lemma mean_pos {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (wassersteinMean X Y t).PosDef := by
  have hC : (((1 - t) • 1 : Matrix (Fin n) (Fin n) ℂ) + t • gmInv X Y).PosDef :=
    (Matrix.PosDef.one.smul (sub_pos.mpr ht1)).add ((riccati hX hY).1.smul ht)
  rw [mean_factor hX hY]
  simpa only [star_eq_conjTranspose, hC.isHermitian.eq] using
    hC.isUnit.posDef_star_right_conjugate_iff.mpr hX

private lemma endpoint_powers {X : Mat} (hX : X.IsHermitian) :
    mpow X 1 = X ∧ mpow X 2 = X ^ 2 := by
  exact ⟨mpow_one hX, (mpow_two hX).trans (pow_two X).symm⟩

private lemma family_values {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    powerMean A B t (1 / 2) = wassersteinMean P Q t ^ 2 ∧
    powerMean A B t 1 = wassersteinMean A B t := by
  constructor
  · simp only [powerMean, half_powers.1, half_powers.2]
    norm_num only [one_div_div, div_one]
    exact (endpoint_powers (mean_pos P_pos Q_pos ht ht1).isHermitian).2
  · simp only [powerMean, (endpoint_powers A_pos.isHermitian).1,
      (endpoint_powers B_pos.isHermitian).1, div_one]
    exact (endpoint_powers (mean_pos A_pos B_pos ht ht1).isHermitian).1

private lemma determinants (t : ℝ) :
    (wassersteinMean P Q t).det.re = 9 * (1 + t * (1-t) * (10 / Real.sqrt 17 - 2)) ^ 2 ∧
    (wassersteinMean A B t).det.re = 81 * (1 + t * (1-t) * (82 / Real.sqrt 881 - 2)) ^ 2 := by
  have sq17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have sq881 := Real.sq_sqrt (show (0 : ℝ) ≤ 881 by norm_num)
  have h17 : Real.sqrt 17 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h881 : Real.sqrt 881 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have cub17 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, sq17]
  have quart17 : Real.sqrt 17 ^ 4 = 17 ^ 2 := by
    calc
      _ = (Real.sqrt 17 ^ 2) ^ 2 := by ring
      _ = _ := by rw [sq17]
  have cub881 : Real.sqrt 881 ^ 3 = 881 * Real.sqrt 881 := by rw [pow_succ, sq881]
  have quart881 : Real.sqrt 881 ^ 4 = 881 ^ 2 := by
    calc
      _ = (Real.sqrt 881 ^ 2) ^ 2 := by ring
      _ = _ := by rw [sq881]
  constructor
  · rw [wassersteinMean, transports.1]
    simp [P, Q, T₁, block, Matrix.det_fin_two, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Complex.real_smul,
      Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.mul_im,
      Complex.add_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring_nf
    norm_num [sq17, sq881, cub17, quart17, cub881, quart881] <;> ring
  · rw [wassersteinMean, transports.2]
    simp [A, B, T₂, block, Matrix.det_fin_two, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Complex.real_smul,
      Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.mul_im,
      Complex.add_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring_nf
    norm_num [sq17, sq881, cub17, quart17, cub881, quart881] <;> ring

private lemma strict_determinants {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (powerMean A B t 1).det.re < (powerMean A B t (1 / 2)).det.re := by
  let u := 10 / Real.sqrt 17 - 2
  let v := 82 / Real.sqrt 881 - 2
  have s17 : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have s881 : 0 < Real.sqrt 881 := Real.sqrt_pos.mpr (by norm_num)
  have sq17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have sq881 := Real.sq_sqrt (show (0 : ℝ) ≤ 881 by norm_num)
  have hu : 2 / 5 < u := by
    dsimp [u]
    rw [lt_sub_iff_add_lt, lt_div_iff₀ s17]
    nlinarith
  have hv : 0 < v := by
    dsimp [v]
    rw [sub_pos, lt_div_iff₀ s881]
    nlinarith
  have hv' : v < 4 / 5 := by
    dsimp [v]
    rw [sub_lt_iff_lt_add, div_lt_iff₀ s881]
    nlinarith
  let h := t * (1-t)
  have hh : 0 < h := mul_pos ht (sub_pos.mpr ht1)
  have hcomp : 1 + h * v < (1 + h * u) ^ 2 := by
    have hm : 0 < h * (2*u-v) := mul_pos hh (by linarith)
    nlinarith [sq_nonneg (h*u)]
  have hbase : 0 < 1 + h * v := by positivity
  have hfour : (1 + h*v) ^ 2 < (1 + h*u) ^ 4 := by
    have hhfour := (sq_lt_sq₀ hbase.le (sq_nonneg (1+h*u))).2 hcomp
    convert hhfour using 1 <;> ring
  rw [(family_values ht ht1).1, (family_values ht ht1).2, Matrix.det_pow]
  have hreal : ((wassersteinMean P Q t).det ^ 2).re =
      (wassersteinMean P Q t).det.re ^ 2 := by
    have hd := (mean_pos P_pos Q_pos ht ht1).isHermitian.det_eq_prod_eigenvalues
    rw [hd]
    simp [RCLike.ofReal_eq_complex_ofReal, Fin.prod_univ_two, pow_two,
      Complex.mul_re, Complex.mul_im]
  rw [hreal, (determinants t).1, (determinants t).2]
  change 81 * (1+h*v)^2 < (9*(1+h*u)^2)^2
  nlinarith

/-- The same pair of positive definite matrices contradicts Conjecture 5.7. -/
theorem result : ¬ conjecture := by
  intro hc
  have hm := (hc 2 A B A_pos B_pos (1/2) (by norm_num) (by norm_num)).1
    (1/2) 1 (by norm_num) (by norm_num)
  have hd := weakLogMajorization_det_le hm
  exact (not_le_of_gt (strict_determinants (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)<1))) hd

end D5.S3.Quantum.Matrix.GanKimConjectureRefutation
