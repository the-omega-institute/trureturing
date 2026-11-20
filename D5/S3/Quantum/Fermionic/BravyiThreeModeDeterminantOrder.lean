/- GID: D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder
   mirror-E: none(waiver:symbolic-determinant-certificate)
   anchors: []
   utility: none
   digest: Shifted determinant order for the real isotropic three-mode Bravyi blocks. -/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shifted determinants of the three-mode Bravyi blocks

Bravyi, *Classical capacity of fermionic product channels*,
arXiv:quant-ph/0507282, §V.B, studies the isotropic three-mode channel.
The real chiral and complementary blocks below compare with the blocks
at `c = q = √(1/2)` and `p = 0`.

The determinant differences are polynomials in the scalar shift. The quadratic
and linear chiral coefficients are nonnegative, and homogenizing the constant
coefficient on the sphere gives a sum with nonnegative coefficients. The
complementary difference is constant in the shift.
-/

namespace D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder

open scoped Matrix

noncomputable section

private def aCoeff (t : ℝ) : ℝ := t * (1 + t) / 2
private def bCoeff (t : ℝ) : ℝ := t * (1 - t) / 2

-- The factors of C and D after removing the common factor λ.
private def cCoeff (t : ℝ) : ℝ := (1 + t) ^ 2 / 4
private def dCoeff (t : ℝ) : ℝ := (1 - t) ^ 2 / 4

-- x is the square of the first amplitude.
private def kPlus (t x : ℝ) : ℝ := (1 - t ^ 2) * (1 - t * (2 * x - 1)) / 8
private def kMinus (t x : ℝ) : ℝ := (1 - t ^ 2) * (1 + t * (2 * x - 1)) / 8

private def sparse4 (a b d e u v w f g : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a, u, v, w; u, b, f, 0; v, f, d, g; w, 0, g, e]

/-- The real chiral block, in the basis of equation (12). -/
def chiral (lam c p q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let t := lam ^ 2
  sparse4
    (kPlus t (c ^ 2) + aCoeff t * c ^ 2 - bCoeff t * p ^ 2)
    (kPlus t (c ^ 2) - bCoeff t * q ^ 2)
    (kMinus t (c ^ 2) + aCoeff t * p ^ 2 - bCoeff t * c ^ 2)
    (kMinus t (c ^ 2) + aCoeff t * q ^ 2)
    (-bCoeff t * p * q)
    (lam ^ 3 * c * p)
    (lam * cCoeff t * c * q)
    (-lam * dCoeff t * c * q)
    (aCoeff t * p * q)

/-- The complementary block of equation (9), occurring twice in the reduction. -/
def complement (lam c q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let t := lam ^ 2
  let v := lam * (1 - t ^ 2) * c * q / 4
  !![kPlus t (c ^ 2), v; v, kMinus t (c ^ 2)]

def comparatorAmplitude : ℝ := Real.sqrt (1 / 2)

private theorem sq_comparatorAmplitude : comparatorAmplitude ^ 2 = 1 / 2 :=
  Real.sq_sqrt (by norm_num)

def chiralComparator (lam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  chiral lam comparatorAmplitude 0 comparatorAmplitude

def complementComparator (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  complement lam comparatorAmplitude comparatorAmplitude

def invariantX (c : ℝ) : ℝ := (2 * c ^ 2 - 1) ^ 2
def invariantZ (c p : ℝ) : ℝ := 4 * c ^ 2 * p ^ 2
def invariantR (c q : ℝ) : ℝ := 4 * c ^ 2 * q ^ 2

private theorem invariants_sum {c p q : ℝ} (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    invariantX c + invariantZ c p + invariantR c q = 1 := by
  unfold invariantX invariantZ invariantR
  linear_combination (4 * c ^ 2) * hn

private def H (t : ℝ) : ℝ := 1 + 5 * t + 3 * t ^ 2 - t ^ 3
private def J (t : ℝ) : ℝ := 1 + 5 * t - 3 * t ^ 2 + t ^ 3

/-- The coefficient of the quadratic shift term in equation (19). -/
def delta2 (t x z : ℝ) : ℝ :=
  t * (1 - t) / 32 * ((t ^ 4 + 6 * t ^ 2 + 1) * x + H t * z)

/-- The coefficient of the linear shift term in equation (20). -/
def delta3 (t x z : ℝ) : ℝ :=
  t * (1 - t) ^ 2 * (1 + t) / 128 * ((1 - t ^ 4) * x + J t * z)

/-- The bracket in equation (23). -/
private def rawBracket (t x z : ℝ) : ℝ :=
  2 * t * (1 - t ^ 2) ^ 2 * x + 2 * t * H t * z
    + t ^ 2 * (1 - t ^ 2) ^ 2 * x ^ 2 + t ^ 2 * (t ^ 2 - 6 * t + 1) * z ^ 2
    - 2 * t ^ 2 * (t ^ 3 + 5 * t ^ 2 + 3 * t - 1) * x * z

/-- The homogeneous certificate in equation (22). -/
private def homogeneousBracket (t x z r : ℝ) : ℝ :=
  t * (t + 2) * (1 - t ^ 2) ^ 2 * x ^ 2 + t * (2 + 11 * t - t ^ 3) * z ^ 2
    + 4 * t * (1 - t ^ 2) * (3 * t + 1) * x * z + 2 * t * (1 - t ^ 2) ^ 2 * x * r
    + 2 * t * H t * z * r

private def delta4Factor (t : ℝ) : ℝ := (1 - t) ^ 4 * (1 + t) ^ 2 / 4096

/-- The constant shift coefficient in equation (21). -/
def delta4 (t x z r : ℝ) : ℝ := delta4Factor t * homogeneousBracket t x z r

private theorem rawBracket_eq_homogeneous (t x z r : ℝ) (hsum : x + z + r = 1) :
    rawBracket t x z = homogeneousBracket t x z r := by
  calc
    rawBracket t x z =
        2 * t * (1 - t ^ 2) ^ 2 * x * (x + z + r) + 2 * t * H t * z * (x + z + r)
          + t ^ 2 * (1 - t ^ 2) ^ 2 * x ^ 2 + t ^ 2 * (t ^ 2 - 6 * t + 1) * z ^ 2
          - 2 * t ^ 2 * (t ^ 3 + 5 * t ^ 2 + 3 * t - 1) * x * z := by
      rw [hsum]
      simp [rawBracket]
    _ = homogeneousBracket t x z r := by
      unfold homogeneousBracket H
      ring

/-- The determinant difference of the complementary blocks in equation (26). -/
def complementDelta (t x z : ℝ) : ℝ :=
  t * (1 - t ^ 2) ^ 2 / 64 * ((1 - t) * x + z)

open Polynomial (C X)

/-- The polynomial whose value at `s` is the determinant of `sI + M`. -/
def shiftedDetPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : Polynomial ℝ :=
  (-M).charpoly

private theorem eval_shiftedDetPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (s : ℝ) :
    (shiftedDetPolynomial M).eval s = (Matrix.scalar n s + M).det := by
  rw [shiftedDetPolynomial, Matrix.eval_charpoly, sub_neg_eq_add]

private theorem scalar_add_sparse4 (s a b d e u v w f g : ℝ) :
    Matrix.scalar (Fin 4) s + sparse4 a b d e u v w f g =
      sparse4 (s + a) (s + b) (s + d) (s + e) u v w f g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sparse4, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.add_apply]

-- The square collects the two disjoint edge pairings and the four-cycle.
private theorem det_sparse4 (a b d e u v w f g : ℝ) :
    (sparse4 a b d e u v w f g).det =
      a * b * d * e - u ^ 2 * d * e - v ^ 2 * b * e - w ^ 2 * b * d
        - f ^ 2 * a * e - g ^ 2 * a * b + (u * g - w * f) ^ 2
        + 2 * u * v * f * e + 2 * v * w * g * b := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, sparse4,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val']
  ring

-- In every term of the Laplace expansion the amplitudes occur to even powers.
private def chiralExpanded (s t x y z : ℝ) : ℝ :=
  let a := s + (kPlus t x + aCoeff t * x - bCoeff t * y)
  let b := s + (kPlus t x - bCoeff t * z)
  let d := s + (kMinus t x + aCoeff t * y - bCoeff t * x)
  let e := s + (kMinus t x + aCoeff t * z)
  a * b * d * e - bCoeff t ^ 2 * y * z * d * e - t ^ 3 * x * y * b * e
    - t * cCoeff t ^ 2 * x * z * b * d - t * dCoeff t ^ 2 * x * z * a * e
    - aCoeff t ^ 2 * y * z * a * b
    + (-bCoeff t * aCoeff t * y * z + t * cCoeff t * dCoeff t * x * z) ^ 2
    + 2 * bCoeff t * t ^ 2 * dCoeff t * x * y * z * e
    + 2 * t ^ 2 * cCoeff t * aCoeff t * x * y * z * b

private theorem chiral_det_expand (s lam c p q : ℝ) :
    (Matrix.scalar (Fin 4) s + chiral lam c p q).det =
      chiralExpanded s (lam ^ 2) (c ^ 2) (p ^ 2) (q ^ 2) := by
  rw [chiral, scalar_add_sparse4, det_sparse4]
  dsimp only [chiralExpanded]
  ring

/-- The comparator polynomial from equations (17) and (24). -/
private def chiralBase (t : ℝ) : Polynomial ℝ :=
  X ^ 4 + C ((1 + t ^ 2) / 2) * X ^ 3
    + C ((1 - t) * (t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + 2 * t + 3) / 32) * X ^ 2
    + C ((1 - t) ^ 3 * (1 + t) ^ 2 * (1 + t ^ 2) / 128) * X
    + C ((1 - t) ^ 6 * (1 + t) ^ 4 / 4096)

private theorem chiral_base_eval (s t : ℝ) :
    (chiralBase t).eval s =
      s ^ 4 + (1 + t ^ 2) / 2 * s ^ 3
        + (1 - t) * (t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + 2 * t + 3) / 32 * s ^ 2
        + (1 - t) ^ 3 * (1 + t) ^ 2 * (1 + t ^ 2) / 128 * s
        + (1 - t) ^ 6 * (1 + t) ^ 4 / 4096 := by
  simp [chiralBase]

private theorem chiral_comparator_det_polynomial (lam : ℝ) :
    shiftedDetPolynomial (chiralComparator lam) = chiralBase (lam ^ 2) := by
  apply Polynomial.funext
  intro s
  rw [eval_shiftedDetPolynomial, chiralComparator, chiral_det_expand, sq_comparatorAmplitude,
    chiral_base_eval]
  norm_num [chiralExpanded, aCoeff, bCoeff, cCoeff, dCoeff, kPlus, kMinus] <;> ring

set_option maxHeartbeats 2000000 in
-- Normalize the expanded chiral determinant after eliminating the third square.
private theorem chiral_expanded_normalized (s t x y : ℝ) :
    chiralExpanded s t x y (1 - x - y) =
      (chiralBase t).eval s
        + (delta2 t ((2 * x - 1) ^ 2) (4 * x * y) * s ^ 2
          + delta3 t ((2 * x - 1) ^ 2) (4 * x * y) * s
          + delta4Factor t * rawBracket t ((2 * x - 1) ^ 2) (4 * x * y)) := by
  rw [chiral_base_eval]
  dsimp only [chiralExpanded, aCoeff, bCoeff, cCoeff, dCoeff, kPlus, kMinus,
    delta2, delta3, delta4Factor, rawBracket, H, J]
  ring

/-- The literal determinant polynomial difference with the bracket of equation (23). -/
private theorem chiral_det_polynomial_difference_raw {lam c p q : ℝ}
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    shiftedDetPolynomial (chiral lam c p q) - shiftedDetPolynomial (chiralComparator lam) =
      C (delta2 (lam ^ 2) (invariantX c) (invariantZ c p)) * X ^ 2
        + C (delta3 (lam ^ 2) (invariantX c) (invariantZ c p)) * X
        + C (delta4Factor (lam ^ 2) * rawBracket (lam ^ 2) (invariantX c) (invariantZ c p)) := by
  have hq : q ^ 2 = 1 - c ^ 2 - p ^ 2 := by linarith only [hn]
  rw [chiral_comparator_det_polynomial]
  apply Polynomial.funext
  intro s
  simp only [Polynomial.eval_sub, eval_shiftedDetPolynomial, chiral_det_expand, hq,
    chiral_expanded_normalized, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    invariantX, invariantZ] <;> ring

/-- Equations (19)–(22) as an identity of actual shifted determinant polynomials. -/
theorem chiral_det_polynomial_difference {lam c p q : ℝ} (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    shiftedDetPolynomial (chiral lam c p q) - shiftedDetPolynomial (chiralComparator lam) =
      C (delta2 (lam ^ 2) (invariantX c) (invariantZ c p)) * X ^ 2
        + C (delta3 (lam ^ 2) (invariantX c) (invariantZ c p)) * X
        + C (delta4 (lam ^ 2) (invariantX c) (invariantZ c p) (invariantR c q)) := by
  rw [chiral_det_polynomial_difference_raw hn,
    rawBracket_eq_homogeneous (lam ^ 2) _ _ _ (invariants_sum hn), delta4]

private def complementBase (s t : ℝ) : ℝ :=
  s ^ 2 + (1 - t ^ 2) / 4 * s + (1 - t ^ 2) ^ 2 / 64 * (1 - t)

private theorem complement_det_expand (s lam c q : ℝ) :
    (Matrix.scalar (Fin 2) s + complement lam c q).det =
      s ^ 2 + (1 - (lam ^ 2) ^ 2) / 4 * s
        + (1 - (lam ^ 2) ^ 2) ^ 2 / 64 *
          (1 - (lam ^ 2) ^ 2 * invariantX c - lam ^ 2 * invariantR c q) := by
  norm_num [complement, Matrix.det_fin_two, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.add_apply, kPlus, kMinus, invariantX, invariantR] <;> ring

private theorem complement_det_normalized (s : ℝ) {lam c p q : ℝ}
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    (Matrix.scalar (Fin 2) s + complement lam c q).det =
      complementBase s (lam ^ 2) + complementDelta (lam ^ 2) (invariantX c) (invariantZ c p) := by
  have hr : invariantR c q = 1 - invariantX c - invariantZ c p := by
    linarith only [invariants_sum hn]
  rw [complement_det_expand, hr]
  unfold complementBase complementDelta
  ring

private theorem comparator_norm : comparatorAmplitude ^ 2 + (0 : ℝ) ^ 2 +
    comparatorAmplitude ^ 2 = 1 := by
  norm_num [sq_comparatorAmplitude]

private theorem complement_comparator_det (s lam : ℝ) :
    (Matrix.scalar (Fin 2) s + complementComparator lam).det = complementBase s (lam ^ 2) := by
  rw [complementComparator, complement_det_normalized s comparator_norm]
  norm_num [complementDelta, invariantX, invariantZ, sq_comparatorAmplitude]

/-- The complementary determinant polynomial difference is constant in the shift. -/
theorem complement_det_polynomial_difference {lam c p q : ℝ}
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    shiftedDetPolynomial (complement lam c q) - shiftedDetPolynomial (complementComparator lam) =
      C (complementDelta (lam ^ 2) (invariantX c) (invariantZ c p)) := by
  apply Polynomial.funext
  intro s
  simp only [Polynomial.eval_sub, eval_shiftedDetPolynomial, complement_det_normalized s hn,
    complement_comparator_det, Polynomial.eval_C] <;> ring

private theorem chiral_deltas_nonneg {t x z r : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hr : 0 ≤ r) :
    0 ≤ delta2 t x z ∧ 0 ≤ delta3 t x z ∧ 0 ≤ delta4 t x z r := by
  have h1 : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have h2 : 0 ≤ 1 - t ^ 2 := sub_nonneg.mpr (pow_le_one₀ ht ht1)
  have h4 : 0 ≤ 1 - t ^ 4 := sub_nonneg.mpr (pow_le_one₀ ht ht1)
  have hH : 0 ≤ H t := by
    rw [show H t = 1 + 5 * t + t ^ 2 * (2 + (1 - t)) by unfold H; ring]
    positivity
  have hJ : 0 ≤ J t := by
    have h2t : 0 ≤ 2 - t := by linarith only [ht1]
    rw [show J t = 1 + 3 * t + t * (1 - t) * (2 - t) by unfold J; ring]
    positivity
  have hzCoeff : 0 ≤ 2 + 11 * t - t ^ 3 := by
    rw [show 2 + 11 * t - t ^ 3 = 2 + 10 * t + t * (1 - t ^ 2) by ring]
    positivity
  unfold delta2 delta3 delta4 delta4Factor homogeneousBracket
  exact ⟨by positivity, by positivity, by positivity⟩

private theorem chiral_input_deltas_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (c p q : ℝ) :
    0 ≤ delta2 (lam ^ 2) (invariantX c) (invariantZ c p) ∧
      0 ≤ delta3 (lam ^ 2) (invariantX c) (invariantZ c p) ∧
      0 ≤ delta4 (lam ^ 2) (invariantX c) (invariantZ c p) (invariantR c q) :=
  chiral_deltas_nonneg (sq_nonneg lam) (pow_le_one₀ hlam hlam1)
    (by unfold invariantX; positivity) (by unfold invariantZ; positivity)
    (by unfold invariantR; positivity)

private theorem complement_input_delta_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (c p : ℝ) : 0 ≤ complementDelta (lam ^ 2) (invariantX c) (invariantZ c p) := by
  have ht : 0 ≤ 1 - lam ^ 2 := sub_nonneg.mpr (pow_le_one₀ hlam hlam1)
  unfold complementDelta invariantX invariantZ
  positivity

/-- The shifted determinant of each block is at least its comparator's for every
`s ≥ 0` and `λ ∈ [0,1]`. The amplitude conclusion holds on the whole real unit sphere. -/
theorem det_shift_order {s lam c p q : ℝ} (hs : 0 ≤ s) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    (s • (1 : Matrix (Fin 4) (Fin 4) ℝ) + chiralComparator lam).det ≤
        (s • (1 : Matrix (Fin 4) (Fin 4) ℝ) + chiral lam c p q).det ∧
      (s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + complementComparator lam).det ≤
        (s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + complement lam c q).det := by
  obtain ⟨h2, h3, h4⟩ := chiral_input_deltas_nonneg hlam hlam1 c p q
  have hN := complement_input_delta_nonneg hlam hlam1 c p
  have hMpoly := congrArg (Polynomial.eval s) (chiral_det_polynomial_difference (lam := lam) hn)
  have hNpoly := congrArg (Polynomial.eval s) (complement_det_polynomial_difference (lam := lam) hn)
  simp only [Polynomial.eval_sub, eval_shiftedDetPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at hMpoly hNpoly
  constructor
  · apply sub_nonneg.mp
    rw [hMpoly]
    positivity
  · apply sub_nonneg.mp
    rw [hNpoly]
    exact hN

end

end D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
