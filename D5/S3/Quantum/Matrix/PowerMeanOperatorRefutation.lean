/- GID: D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/PowerMeanOperatorRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.claim; result=D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.result; claim=D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.claim
   digest: An exact positive definite pair violates p=2 Euclidean operator-norm monotonicity. -/

import D5.S3.Quantum.Matrix.SpectralPower
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
The claim is the p=2 Euclidean operator-norm specialization of Conjecture 9
in Dumitru and Franco, arXiv:1701.07023v1. The preprint is withdrawn; no
later-resolution, originality, or priority claim is made. Its universal
all-norm assertion implies this specialization, which is the only assertion
encoded here. The published successor's p=2 Frobenius result is unaffected.

All matrix norms use Matrix.Norms.L2Operator, induced by EuclideanSpace on
complex vectors. The power mean uses positive spectral powers. The explicit
positive root (S+rI)/w and a strict Rayleigh quotient give the counterexample
X=diag(1/10,4), Y=[[19/50,-24/25],[-24/25,93/25]], s=0, t=1/100.
-/

set_option maxRecDepth 8192

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.PowerMeanOperatorRefutation

open D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_two posDef_two)

/-- The p=2 power mean, using positive spectral powers on PSD inputs. -/
def mu2 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  mpow (t • mpow A 2 + (1 - t) • mpow B 2) (1 / 2)

/-- Only the p=2 Euclidean operator-norm specialization of v1 Conjecture 9.
The PSD hypotheses and the nonincreasing direction are retained. -/
def claim : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ),
    A.PosSemidef → B.PosSemidef → 0 ≤ s → s ≤ t → t ≤ 1 →
      ‖A - mu2 A B t‖ ≤ ‖A - mu2 A B s‖

/-- The second argument B of the counterexample. -/
def X : QubitMatrix := !![1 / 10, 0; 0, 4]

/-- The first argument A of the counterexample. -/
def Y : QubitMatrix := !![19 / 50, -24 / 25; -24 / 25, 93 / 25]

private def S : QubitMatrix :=
  !![257 / 12500, -123 / 3125; -123 / 3125, 39969 / 2500]
private def d : ℝ := 51118101 / 156250000
private def T : ℝ := 100051 / 6250
private def r : ℝ := Real.sqrt d
private def w : ℝ := Real.sqrt (T + 2 * r)
private def K : QubitMatrix := S + r • (1 : QubitMatrix)
private def Q : QubitMatrix := w⁻¹ • K
private def a : ℝ := 127521 / 12500
private def c : ℝ := 649 / 250
private def v : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![3 / 5, 4 / 5]

private lemma X_pos : X.PosDef := by
  convert posDef_two (1 / 10) 0 4 (by norm_num) (by norm_num) using 1 <;>
    norm_num [X]

private lemma Y_pos : Y.PosDef := by
  convert posDef_two (19 / 50) (-24 / 25) (93 / 25)
    (by norm_num) (by norm_num) using 1 <;> norm_num [Y]

private lemma S_pos : S.PosDef := by
  convert posDef_two (257 / 12500) (-123 / 3125) (39969 / 2500)
    (by norm_num) (by norm_num) using 1 <;> norm_num [S]

private lemma r_nonneg : 0 ≤ r := Real.sqrt_nonneg d

private lemma r_square : r ^ 2 = d :=
  Real.sq_sqrt (by norm_num [d])

private lemma w_pos : 0 < w := by
  apply Real.sqrt_pos.mpr
  have hr := r_nonneg
  dsimp [T]
  linarith

private lemma w_square : w ^ 2 = T + 2 * r := by
  apply Real.sq_sqrt
  have hr := r_nonneg
  dsimp [T]
  linarith

/-- Direct two by two multiplication uses r²=det S. -/
private lemma K_square : K * K = (T + 2 * r) • S := by
  have hr : (r : ℂ) ^ 2 = (51118101 / 156250000 : ℂ) := by
    rw [← Complex.ofReal_pow, r_square]
    norm_num [d]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, S, T, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
      Matrix.one_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
  all_goals first | ring1 | linear_combination hr

private lemma Q_square : Q * Q = S := by
  have hw0 : w ≠ 0 := ne_of_gt w_pos
  have hscale : w⁻¹ * w⁻¹ * (T + 2 * r) = 1 := by
    rw [← w_square]
    field_simp [hw0]
  simp only [Q, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [K_square, smul_smul, hscale, one_smul]

private lemma Q_nonneg : 0 ≤ Q := by
  exact ((S_pos.posSemidef.add (Matrix.PosSemidef.one.smul r_nonneg)).smul
    (inv_nonneg.mpr (le_of_lt w_pos))).nonneg

/-- The spectral p=2 mean at the positive parameter is the explicit positive root. -/
private lemma mean_at_t : mu2 Y X (1 / 100) = Q := by
  have hweighted :
      (1 / 100 : ℝ) • mpow Y 2 + (1 - (1 / 100 : ℝ)) • mpow X 2 = S := by
    rw [mpow_two Y_pos.isHermitian, mpow_two X_pos.isHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [X, Y, S, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
        RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  unfold mu2
  rw [hweighted, mpow, ← CFC.rpow_eq_cfc_real S_pos.posSemidef.nonneg,
    ← CFC.sqrt_eq_rpow]
  exact CFC.sqrt_unique Q_square Q_nonneg

private lemma mean_at_zero : mu2 Y X 0 = X := by
  have hXX : (X * X).PosSemidef := by
    simpa only [X_pos.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self X
  simp only [mu2, zero_smul, sub_zero, one_smul, zero_add]
  rw [mpow_two X_pos.isHermitian, mpow, ← CFC.rpow_eq_cfc_real hXX.nonneg,
    ← CFC.sqrt_eq_rpow]
  exact CFC.sqrt_mul_self X X_pos.posSemidef.nonneg

private lemma reflection : (X - Y)ᴴ * (X - Y) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, Y, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply, map_ofNat]

private lemma endpoint_norm : ‖Y - mu2 Y X 0‖ = 1 := by
  have hsq : ‖X - Y‖ * ‖X - Y‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, reflection]
    exact norm_one
  have hnorm : ‖X - Y‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg (X - Y)) zero_le_one).mp
    simpa only [pow_two, one_mul] using hsq
  rw [mean_at_zero, norm_sub_rev]
  exact hnorm

private lemma v_norm : ‖v‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [v, PiLp.toLp_apply, norm_div, Fin.sum_univ_two]

/-- The exact strict scalar certificate; all square roots are positive real roots. -/
private lemma root_rayleigh_gt : c < (a + r) / w := by
  have hr0 := r_nonneg
  have hr2 : r ^ 2 = (51118101 / 156250000 : ℝ) := by
    simpa only [d] using r_square
  have hr : (57 / 100 : ℝ) < r := by
    by_contra h
    have hle : r ≤ (57 / 100 : ℝ) := le_of_not_gt h
    have hsq : r ^ 2 ≤ (57 / 100 : ℝ) ^ 2 :=
      (sq_le_sq₀ hr0 (by norm_num)).mpr hle
    nlinarith [hr2]
  have hdiff : (a + r) ^ 2 - c ^ 2 * w ^ 2 =
      -339943099 / 97656250 + (108202 / 15625) * r := by
    rw [w_square]
    dsimp [a, c, T]
    nlinarith [hr2]
  have hgap : 0 < (a + r) ^ 2 - c ^ 2 * w ^ 2 := by
    rw [hdiff]
    nlinarith
  have har : 0 < a + r := by dsimp [a]; linarith
  have hcw : 0 < c * w := mul_pos (by norm_num [c]) w_pos
  have hsquare : (c * w) ^ 2 < (a + r) ^ 2 := by nlinarith [hgap]
  have hlt : c * w < a + r :=
    (sq_lt_sq₀ (le_of_lt hcw) (le_of_lt har)).mp hsquare
  exact (lt_div_iff₀ w_pos).mpr hlt

private lemma rayleigh :
    inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Q - Y) v) =
      (((a + r) / w - 399 / 250 : ℝ) : ℂ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  change ((Q - Y) *ᵥ (![3 / 5, 4 / 5] : Fin 2 → ℂ)) ⬝ᵥ
      star (![3 / 5, 4 / 5] : Fin 2 → ℂ) = _
  norm_num [Q, K, S, Y, a, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_inv,
    map_ofNat] <;>
    ring

private lemma strict_norm : 1 < ‖Y - mu2 Y X (1 / 100)‖ := by
  have hreal : 1 < (a + r) / w - 399 / 250 := by
    have h := root_rayleigh_gt
    dsimp [c] at h
    linarith
  have hop : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Q - Y) v‖ ≤ ‖Q - Y‖ := by
    simpa only [v_norm, mul_one, Matrix.l2_opNorm_toEuclideanCLM] using
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Q - Y)).le_opNorm v
  rw [mean_at_t, norm_sub_rev]
  calc
    1 < (a + r) / w - 399 / 250 := hreal
    _ = ‖inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Q - Y) v)‖ := by
      rw [rayleigh, Complex.norm_of_nonneg (by linarith : 0 ≤ (a + r) / w - 399 / 250)]
    _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Q - Y) v‖ := norm_inner_le_norm _ _
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Q - Y) v‖ := by rw [v_norm, one_mul]
    _ ≤ ‖Q - Y‖ := hop

/-- Exact positive definite witnesses with endpoint distance one and a strictly larger
distance at t=1/100, in the Euclidean induced operator norm. -/
private theorem counterexample :
    X.PosDef ∧ Y.PosDef ∧ ‖Y - mu2 Y X 0‖ = 1 ∧
      1 < ‖Y - mu2 Y X (1 / 100)‖ :=
  ⟨X_pos, Y_pos, endpoint_norm, strict_norm⟩

/-- The closed p=2 operator-norm specialization of the withdrawn v1 claim is false. -/
theorem result : Not claim := by
  intro h
  obtain ⟨hX, hY, hzero, hstrict⟩ := counterexample
  have hparameters : (0 : ℝ) < 1 / 100 ∧ (1 / 100 : ℝ) < 1 := by norm_num
  have hmono := h 2 Y X 0 (1 / 100) hY.posSemidef hX.posSemidef
    (by norm_num) hparameters.1.le hparameters.2.le
  rw [hzero] at hmono
  exact (not_le_of_gt hstrict) hmono

end D5.S3.Quantum.Matrix.PowerMeanOperatorRefutation
