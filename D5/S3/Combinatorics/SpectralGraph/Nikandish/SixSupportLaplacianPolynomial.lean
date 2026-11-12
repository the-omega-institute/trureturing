/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLaplacianPolynomial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLaplacianPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supplied Nikandish tower and finite-root objects, pending current canonical admission. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportQuadraticTower
import D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 1024
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial

universe u v

variable {R : Type u} [CommRing R]

/-- Original support order `1,2,3,12,13,23`, over an arbitrary coefficient ring. -/
def quotientOver (a b c : R) : Matrix (Fin 6) (Fin 6) R :=
  !![b+c+b*c, -b, -c, 0, 0, -b*c;
     -a, a+c+a*c, -c, 0, -a*c, 0;
     -a, -b, a+b+a*b, -a*b, 0, 0;
     0, 0, -c, c, 0, 0;
     0, -b, 0, 0, b, 0;
     -a, 0, 0, 0, 0, a]

private theorem map_quotientOver {S : Type v} [CommRing S] (f : R →+* S)
    (a b c : R) :
    (quotientOver a b c).map f = quotientOver (f a) (f b) (f c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quotientOver, Matrix.map_apply]

/-- Exact polynomial division by `X`; no pointwise division at zero. -/
def reducedCharpoly (a b c : R) : Polynomial R :=
  (quotientOver a b c).charpoly.divX

private theorem det_quotientOver (a b c : R) : (quotientOver a b c).det = 0 := by
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (v := fun _ : Fin 6 => (1 : R)) (i := 0)
  · ext i
    fin_cases i <;>
      simp [quotientOver, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  · exact (nonZeroDivisors R).one_mem

private theorem charpoly_coeff_zero (a b c : R) :
    (quotientOver a b c).charpoly.coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpoly]
  simp [Matrix.det_neg, det_quotientOver]

theorem charpoly_zero_factor (a b c : R) :
    (quotientOver a b c).charpoly = Polynomial.X * reducedCharpoly a b c := by
  have h := Polynomial.X_mul_divX_add (quotientOver a b c).charpoly
  rw [charpoly_coeff_zero, Polynomial.C_0, add_zero] at h
  exact h.symm

private theorem reduced_eval_mul (a b c x : R) :
    x * (reducedCharpoly a b c).eval x =
      (Matrix.scalar (Fin 6) x - quotientOver a b c).det := by
  have h := congrArg (fun p : Polynomial R => p.eval x) (charpoly_zero_factor a b c)
  simpa only [Matrix.eval_charpoly, Polynomial.eval_mul, Polynomial.eval_X] using h.symm

private theorem reduced_eval_one (a b c : R) :
    (reducedCharpoly a b c).eval 1 =
      (1 - quotientOver a b c).det := by
  simpa using reduced_eval_mul a b c 1

private theorem map_reducedCharpoly {S : Type v} [CommRing S] (f : R →+* S)
    (a b c : R) :
    (reducedCharpoly a b c).map f = reducedCharpoly (f a) (f b) (f c) := by
  unfold reducedCharpoly
  rw [← map_quotientOver f a b c, Matrix.charpoly_map]
  ext n
  simp only [Polynomial.coeff_map, Polynomial.coeff_divX]

def d₁ (a b c x : R) : R := (x-a)*(x-b-c-b*c)-a*b*c
def d₂ (a b c x : R) : R := (x-b)*(x-a-c-a*c)-a*b*c
def d₃ (a b c x : R) : R := (x-c)*(x-a-b-a*b)-a*b*c

private def sparse_minor_3_rhs (a b c x : R) : R := (0)*(0)*(x-a)-(0)*(0)*(0)-(a*c)*(a*b)*(x-a)+(a*c)*(0)*(0)+(0)*(a*b)*(0)-(0)*(0)*(0)
private theorem sparse_minor_3 (a b c x : R) : (!![0, a*c, 0;
    a*b, 0, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R).det = sparse_minor_3_rhs a b c x := by
  simpa [sparse_minor_3_rhs] using Matrix.det_fin_three (!![0, a*c, 0;
    a*b, 0, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R)

private def sparse_minor_4_rhs (a b c x : R) : R := (a)*(a*b)*(0)-(a)*(0)*(0)-(0)*(a)*(0)+(0)*(0)*(a)+(a*c)*(a)*(0)-(a*c)*(a*b)*(a)
private theorem sparse_minor_4 (a b c x : R) : (!![a, 0, a*c;
    a, a*b, 0;
    a, 0, 0] : Matrix (Fin 3) (Fin 3) R).det = sparse_minor_4_rhs a b c x := by
  simpa [sparse_minor_4_rhs] using Matrix.det_fin_three (!![a, 0, a*c;
    a, a*b, 0;
    a, 0, 0] : Matrix (Fin 3) (Fin 3) R)

private def sparse_minor_2_rhs (a b c x : R) : R := ((-1 : R)^(0+0)*(x-(b+c+b*c))*sparse_minor_3_rhs a b c x)+((-1 : R)^(0+3)*(b*c)*sparse_minor_4_rhs a b c x)
private theorem sparse_minor_2 (a b c x : R) : (!![x-(b+c+b*c), 0, 0, b*c;
    a, 0, a*c, 0;
    a, a*b, 0, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).det = sparse_minor_2_rhs a b c x := by
  have h0 : (!![x-(b+c+b*c), 0, 0, b*c;
    a, 0, a*c, 0;
    a, a*b, 0, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).submatrix (0 : Fin 4).succAbove (0 : Fin 4).succAbove =
    (!![0, a*c, 0;
    a*b, 0, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h3 : (!![x-(b+c+b*c), 0, 0, b*c;
    a, 0, a*c, 0;
    a, a*b, 0, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).submatrix (0 : Fin 4).succAbove (3 : Fin 4).succAbove =
    (!![a, 0, a*c;
    a, a*b, 0;
    a, 0, 0] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 0, Fin.sum_univ_four]
  rw [h0, h3]
  norm_num [sparse_minor_2_rhs, (sparse_minor_3 a b c x), (sparse_minor_4 a b c x)]

private def sparse_minor_6_rhs (a b c x : R) : R := (b)*(a*b)*(x-a)-(b)*(0)*(0)-(0)*(b)*(x-a)+(0)*(0)*(0)+(b*c)*(b)*(0)-(b*c)*(a*b)*(0)
private theorem sparse_minor_6 (a b c x : R) : (!![b, 0, b*c;
    b, a*b, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R).det = sparse_minor_6_rhs a b c x := by
  simpa [sparse_minor_6_rhs] using Matrix.det_fin_three (!![b, 0, b*c;
    b, a*b, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R)

private def sparse_minor_7_rhs (a b c x : R) : R := (x-(b+c+b*c))*(a*b)*(x-a)-(x-(b+c+b*c))*(0)*(0)-(0)*(a)*(x-a)+(0)*(0)*(a)+(b*c)*(a)*(0)-(b*c)*(a*b)*(a)
private theorem sparse_minor_7 (a b c x : R) : (!![x-(b+c+b*c), 0, b*c;
    a, a*b, 0;
    a, 0, x-a] : Matrix (Fin 3) (Fin 3) R).det = sparse_minor_7_rhs a b c x := by
  simpa [sparse_minor_7_rhs] using Matrix.det_fin_three (!![x-(b+c+b*c), 0, b*c;
    a, a*b, 0;
    a, 0, x-a] : Matrix (Fin 3) (Fin 3) R)

private def sparse_minor_5_rhs (a b c x : R) : R := ((-1 : R)^(1+0)*(a)*sparse_minor_6_rhs a b c x)+((-1 : R)^(1+1)*(x-(a+c+a*c))*sparse_minor_7_rhs a b c x)
private theorem sparse_minor_5 (a b c x : R) : (!![x-(b+c+b*c), b, 0, b*c;
    a, x-(a+c+a*c), 0, 0;
    a, b, a*b, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).det = sparse_minor_5_rhs a b c x := by
  have h0 : (!![x-(b+c+b*c), b, 0, b*c;
    a, x-(a+c+a*c), 0, 0;
    a, b, a*b, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).submatrix (1 : Fin 4).succAbove (0 : Fin 4).succAbove =
    (!![b, 0, b*c;
    b, a*b, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h1 : (!![x-(b+c+b*c), b, 0, b*c;
    a, x-(a+c+a*c), 0, 0;
    a, b, a*b, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).submatrix (1 : Fin 4).succAbove (1 : Fin 4).succAbove =
    (!![x-(b+c+b*c), 0, b*c;
    a, a*b, 0;
    a, 0, x-a] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 1, Fin.sum_univ_four]
  rw [h0, h1]
  norm_num [sparse_minor_5_rhs, (sparse_minor_6 a b c x), (sparse_minor_7 a b c x)]

private def sparse_minor_1_rhs (a b c x : R) : R := ((-1 : R)^(3+1)*(b)*sparse_minor_2_rhs a b c x)+((-1 : R)^(3+3)*(x-b)*sparse_minor_5_rhs a b c x)
private theorem sparse_minor_1 (a b c x : R) : (!![x-(b+c+b*c), b, 0, 0, b*c;
    a, x-(a+c+a*c), 0, a*c, 0;
    a, b, a*b, 0, 0;
    0, b, 0, x-b, 0;
    a, 0, 0, 0, x-a] : Matrix (Fin 5) (Fin 5) R).det = sparse_minor_1_rhs a b c x := by
  have h1 : (!![x-(b+c+b*c), b, 0, 0, b*c;
    a, x-(a+c+a*c), 0, a*c, 0;
    a, b, a*b, 0, 0;
    0, b, 0, x-b, 0;
    a, 0, 0, 0, x-a] : Matrix (Fin 5) (Fin 5) R).submatrix (3 : Fin 5).succAbove (1 : Fin 5).succAbove =
    (!![x-(b+c+b*c), 0, 0, b*c;
    a, 0, a*c, 0;
    a, a*b, 0, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h3 : (!![x-(b+c+b*c), b, 0, 0, b*c;
    a, x-(a+c+a*c), 0, a*c, 0;
    a, b, a*b, 0, 0;
    0, b, 0, x-b, 0;
    a, 0, 0, 0, x-a] : Matrix (Fin 5) (Fin 5) R).submatrix (3 : Fin 5).succAbove (3 : Fin 5).succAbove =
    (!![x-(b+c+b*c), b, 0, b*c;
    a, x-(a+c+a*c), 0, 0;
    a, b, a*b, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 3, Fin.sum_univ_five]
  rw [h1, h3]
  norm_num [sparse_minor_1_rhs, (sparse_minor_2 a b c x), (sparse_minor_5 a b c x)]

private def sparse_minor_10_rhs (a b c x : R) : R := (c)*(a*c)*(x-a)-(c)*(0)*(0)-(0)*(c)*(x-a)+(0)*(0)*(0)+(b*c)*(c)*(0)-(b*c)*(a*c)*(0)
private theorem sparse_minor_10 (a b c x : R) : (!![c, 0, b*c;
    c, a*c, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R).det = sparse_minor_10_rhs a b c x := by
  simpa [sparse_minor_10_rhs] using Matrix.det_fin_three (!![c, 0, b*c;
    c, a*c, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R)

private def sparse_minor_11_rhs (a b c x : R) : R := (x-(b+c+b*c))*(a*c)*(x-a)-(x-(b+c+b*c))*(0)*(0)-(0)*(a)*(x-a)+(0)*(0)*(a)+(b*c)*(a)*(0)-(b*c)*(a*c)*(a)
private theorem sparse_minor_11 (a b c x : R) : (!![x-(b+c+b*c), 0, b*c;
    a, a*c, 0;
    a, 0, x-a] : Matrix (Fin 3) (Fin 3) R).det = sparse_minor_11_rhs a b c x := by
  simpa [sparse_minor_11_rhs] using Matrix.det_fin_three (!![x-(b+c+b*c), 0, b*c;
    a, a*c, 0;
    a, 0, x-a] : Matrix (Fin 3) (Fin 3) R)

private def sparse_minor_9_rhs (a b c x : R) : R := ((-1 : R)^(2+0)*(a)*sparse_minor_10_rhs a b c x)+((-1 : R)^(2+1)*(x-(a+b+a*b))*sparse_minor_11_rhs a b c x)
private theorem sparse_minor_9 (a b c x : R) : (!![x-(b+c+b*c), c, 0, b*c;
    a, c, a*c, 0;
    a, x-(a+b+a*b), 0, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).det = sparse_minor_9_rhs a b c x := by
  have h0 : (!![x-(b+c+b*c), c, 0, b*c;
    a, c, a*c, 0;
    a, x-(a+b+a*b), 0, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).submatrix (2 : Fin 4).succAbove (0 : Fin 4).succAbove =
    (!![c, 0, b*c;
    c, a*c, 0;
    0, 0, x-a] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h1 : (!![x-(b+c+b*c), c, 0, b*c;
    a, c, a*c, 0;
    a, x-(a+b+a*b), 0, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).submatrix (2 : Fin 4).succAbove (1 : Fin 4).succAbove =
    (!![x-(b+c+b*c), 0, b*c;
    a, a*c, 0;
    a, 0, x-a] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 2, Fin.sum_univ_four]
  rw [h0, h1]
  norm_num [sparse_minor_9_rhs, (sparse_minor_10 a b c x), (sparse_minor_11 a b c x)]

private def sparse_minor_13_rhs (a b c x : R) : R := (b)*(c)*(0)-(b)*(0)*(x-(a+b+a*b))-(c)*(x-(a+c+a*c))*(0)+(c)*(0)*(b)+(b*c)*(x-(a+c+a*c))*(x-(a+b+a*b))-(b*c)*(c)*(b)
private theorem sparse_minor_13 (a b c x : R) : (!![b, c, b*c;
    x-(a+c+a*c), c, 0;
    b, x-(a+b+a*b), 0] : Matrix (Fin 3) (Fin 3) R).det = sparse_minor_13_rhs a b c x := by
  simpa [sparse_minor_13_rhs] using Matrix.det_fin_three (!![b, c, b*c;
    x-(a+c+a*c), c, 0;
    b, x-(a+b+a*b), 0] : Matrix (Fin 3) (Fin 3) R)

private def sparse_minor_14_rhs (a b c x : R) : R := (x-(b+c+b*c))*(x-(a+c+a*c))*(x-(a+b+a*b))-(x-(b+c+b*c))*(c)*(b)-(b)*(a)*(x-(a+b+a*b))+(b)*(c)*(a)+(c)*(a)*(b)-(c)*(x-(a+c+a*c))*(a)
private theorem sparse_minor_14 (a b c x : R) : (!![x-(b+c+b*c), b, c;
    a, x-(a+c+a*c), c;
    a, b, x-(a+b+a*b)] : Matrix (Fin 3) (Fin 3) R).det = sparse_minor_14_rhs a b c x := by
  simpa [sparse_minor_14_rhs] using Matrix.det_fin_three (!![x-(b+c+b*c), b, c;
    a, x-(a+c+a*c), c;
    a, b, x-(a+b+a*b)] : Matrix (Fin 3) (Fin 3) R)

private def sparse_minor_12_rhs (a b c x : R) : R := ((-1 : R)^(3+0)*(a)*sparse_minor_13_rhs a b c x)+((-1 : R)^(3+3)*(x-a)*sparse_minor_14_rhs a b c x)
private theorem sparse_minor_12 (a b c x : R) : (!![x-(b+c+b*c), b, c, b*c;
    a, x-(a+c+a*c), c, 0;
    a, b, x-(a+b+a*b), 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).det = sparse_minor_12_rhs a b c x := by
  have h0 : (!![x-(b+c+b*c), b, c, b*c;
    a, x-(a+c+a*c), c, 0;
    a, b, x-(a+b+a*b), 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).submatrix (3 : Fin 4).succAbove (0 : Fin 4).succAbove =
    (!![b, c, b*c;
    x-(a+c+a*c), c, 0;
    b, x-(a+b+a*b), 0] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h3 : (!![x-(b+c+b*c), b, c, b*c;
    a, x-(a+c+a*c), c, 0;
    a, b, x-(a+b+a*b), 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R).submatrix (3 : Fin 4).succAbove (3 : Fin 4).succAbove =
    (!![x-(b+c+b*c), b, c;
    a, x-(a+c+a*c), c;
    a, b, x-(a+b+a*b)] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 3, Fin.sum_univ_four]
  rw [h0, h3]
  norm_num [sparse_minor_12_rhs, (sparse_minor_13 a b c x), (sparse_minor_14 a b c x)]

private def sparse_minor_8_rhs (a b c x : R) : R := ((-1 : R)^(3+1)*(b)*sparse_minor_9_rhs a b c x)+((-1 : R)^(3+3)*(x-b)*sparse_minor_12_rhs a b c x)
private theorem sparse_minor_8 (a b c x : R) : (!![x-(b+c+b*c), b, c, 0, b*c;
    a, x-(a+c+a*c), c, a*c, 0;
    a, b, x-(a+b+a*b), 0, 0;
    0, b, 0, x-b, 0;
    a, 0, 0, 0, x-a] : Matrix (Fin 5) (Fin 5) R).det = sparse_minor_8_rhs a b c x := by
  have h1 : (!![x-(b+c+b*c), b, c, 0, b*c;
    a, x-(a+c+a*c), c, a*c, 0;
    a, b, x-(a+b+a*b), 0, 0;
    0, b, 0, x-b, 0;
    a, 0, 0, 0, x-a] : Matrix (Fin 5) (Fin 5) R).submatrix (3 : Fin 5).succAbove (1 : Fin 5).succAbove =
    (!![x-(b+c+b*c), c, 0, b*c;
    a, c, a*c, 0;
    a, x-(a+b+a*b), 0, 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h3 : (!![x-(b+c+b*c), b, c, 0, b*c;
    a, x-(a+c+a*c), c, a*c, 0;
    a, b, x-(a+b+a*b), 0, 0;
    0, b, 0, x-b, 0;
    a, 0, 0, 0, x-a] : Matrix (Fin 5) (Fin 5) R).submatrix (3 : Fin 5).succAbove (3 : Fin 5).succAbove =
    (!![x-(b+c+b*c), b, c, b*c;
    a, x-(a+c+a*c), c, 0;
    a, b, x-(a+b+a*b), 0;
    a, 0, 0, x-a] : Matrix (Fin 4) (Fin 4) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 3, Fin.sum_univ_five]
  rw [h1, h3]
  norm_num [sparse_minor_8_rhs, (sparse_minor_9 a b c x), (sparse_minor_12 a b c x)]

private def sparse_minor_0_rhs (a b c x : R) : R := ((-1 : R)^(3+2)*(c)*sparse_minor_1_rhs a b c x)+((-1 : R)^(3+3)*(x-c)*sparse_minor_8_rhs a b c x)
private theorem sparse_minor_0 (a b c x : R) : (!![x-(b+c+b*c), b, c, 0, 0, b*c;
    a, x-(a+c+a*c), c, 0, a*c, 0;
    a, b, x-(a+b+a*b), a*b, 0, 0;
    0, 0, c, x-c, 0, 0;
    0, b, 0, 0, x-b, 0;
    a, 0, 0, 0, 0, x-a] : Matrix (Fin 6) (Fin 6) R).det = sparse_minor_0_rhs a b c x := by
  have h2 : (!![x-(b+c+b*c), b, c, 0, 0, b*c;
    a, x-(a+c+a*c), c, 0, a*c, 0;
    a, b, x-(a+b+a*b), a*b, 0, 0;
    0, 0, c, x-c, 0, 0;
    0, b, 0, 0, x-b, 0;
    a, 0, 0, 0, 0, x-a] : Matrix (Fin 6) (Fin 6) R).submatrix (3 : Fin 6).succAbove (2 : Fin 6).succAbove =
    (!![x-(b+c+b*c), b, 0, 0, b*c;
    a, x-(a+c+a*c), 0, a*c, 0;
    a, b, a*b, 0, 0;
    0, b, 0, x-b, 0;
    a, 0, 0, 0, x-a] : Matrix (Fin 5) (Fin 5) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h3 : (!![x-(b+c+b*c), b, c, 0, 0, b*c;
    a, x-(a+c+a*c), c, 0, a*c, 0;
    a, b, x-(a+b+a*b), a*b, 0, 0;
    0, 0, c, x-c, 0, 0;
    0, b, 0, 0, x-b, 0;
    a, 0, 0, 0, 0, x-a] : Matrix (Fin 6) (Fin 6) R).submatrix (3 : Fin 6).succAbove (3 : Fin 6).succAbove =
    (!![x-(b+c+b*c), b, c, 0, b*c;
    a, x-(a+c+a*c), c, a*c, 0;
    a, b, x-(a+b+a*b), 0, 0;
    0, b, 0, x-b, 0;
    a, 0, 0, 0, x-a] : Matrix (Fin 5) (Fin 5) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 3, Fin.sum_univ_six]
  rw [h2, h3]
  norm_num [sparse_minor_0_rhs, (sparse_minor_1 a b c x), (sparse_minor_8 a b c x)]

theorem determinant_formula (a b c x : R) :
    (Matrix.scalar (Fin 6) x - quotientOver a b c).det =
      d₁ a b c x * d₂ a b c x * d₃ a b c x
      - b*c*(x-b)*(x-c)*d₁ a b c x
      - a*c*(x-a)*(x-c)*d₂ a b c x
      - a*b*(x-a)*(x-b)*d₃ a b c x
      + 2*a*b*c*(x-a)*(x-b)*(x-c) := by
  have hm : Matrix.scalar (Fin 6) x - quotientOver a b c =
(!![x-(b+c+b*c), b, c, 0, 0, b*c;
    a, x-(a+c+a*c), c, 0, a*c, 0;
    a, b, x-(a+b+a*b), a*b, 0, 0;
    0, 0, c, x-c, 0, 0;
    0, b, 0, 0, x-b, 0;
    a, 0, 0, 0, 0, x-a] : Matrix (Fin 6) (Fin 6) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quotientOver,Matrix.scalar_apply,Matrix.diagonal_apply]
  rw [hm,sparse_minor_0]
  dsimp [d₁,d₂,d₃,sparse_minor_3_rhs,sparse_minor_4_rhs,sparse_minor_2_rhs,sparse_minor_6_rhs,sparse_minor_7_rhs,sparse_minor_5_rhs,sparse_minor_1_rhs,sparse_minor_10_rhs,sparse_minor_11_rhs,sparse_minor_9_rhs,sparse_minor_13_rhs,sparse_minor_14_rhs,sparse_minor_12_rhs,sparse_minor_8_rhs,sparse_minor_0_rhs]
  ring
/-- Published endpoint parameter, with the original order of `a,b,c`. -/
def endpointT (b : R) : R := b*(b+2)

def endpointA (b : R) : R := 3*b-1
def endpointB (b : R) : R := b*(b^2+4*b-1)
def endpointC₀ (b : R) : R :=
  -(b^2+2*b-1)*(b^2+3*b-1)*(b^3+3*b^2+3*b-1)

/-- `R(q)=Aq²+Bq+C₀`, before substituting `q=a(t-a)`. -/
def endpointR (b q : R) : R := endpointA b*q^2 + endpointB b*q + endpointC₀ b

/-- The actual equality-curve polynomial; the factor `b-1` is not canceled. -/
def endpointG (a b : R) : R := endpointR b (a*(endpointT b-a))

private theorem endpoint_determinant (a b : R) :
    (1 - quotientOver a b (endpointT b-a)).det = -(b-1)*endpointG a b := by
  calc
    _ = (Matrix.scalar (Fin 6) (1 : R) - quotientOver a b (endpointT b-a)).det := by
      rw [map_one]
    _ = -(b-1)*endpointG a b := by
      rw [determinant_formula]
      dsimp [d₁, d₂, d₃, endpointG, endpointR, endpointT, endpointA, endpointB, endpointC₀]
      ring

private theorem endpoint_reduced (a b : R) :
    (reducedCharpoly a b (endpointT b-a)).eval 1 = -(b-1)*endpointG a b := by
  rw [reduced_eval_one, endpoint_determinant]

/-- Universal integer coefficients in the ordered variables `a,b,c`. -/
abbrev Universal := MvPolynomial (Fin 3) ℤ

def universalMatrix : Matrix (Fin 6) (Fin 6) Universal :=
  quotientOver (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

def universalCharpoly : Polynomial Universal := universalMatrix.charpoly
def universalReduced : Polynomial Universal := universalCharpoly.divX

def specialize (a b c : R) : Universal →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![a,b,c]

private theorem universal_matrix_specialize (a b c : R) :
    universalMatrix.map (specialize a b c) = quotientOver a b c := by
  simpa [universalMatrix, specialize] using
    map_quotientOver (specialize a b c)
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

private theorem universal_charpoly_specialize (a b c : R) :
    universalCharpoly.map (specialize a b c) = (quotientOver a b c).charpoly := by
  rw [universalCharpoly, ← Matrix.charpoly_map, universal_matrix_specialize]

private theorem universal_reduced_specialize (a b c : R) :
    universalReduced.map (specialize a b c) = reducedCharpoly a b c := by
  simpa [universalReduced, universalCharpoly, universalMatrix, reducedCharpoly, specialize] using
    map_reducedCharpoly (specialize a b c)
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

/-- The same literal matrix with rational polynomial coefficients. -/
abbrev RationalCoefficients := MvPolynomial (Fin 3) ℚ

def rationalMatrix : Matrix (Fin 6) (Fin 6) RationalCoefficients :=
  quotientOver (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

def integerToRational : Universal →+* RationalCoefficients :=
  MvPolynomial.map (Int.castRingHom ℚ)

private theorem universal_matrix_rational :
    universalMatrix.map integerToRational = rationalMatrix := by
  simpa [universalMatrix, rationalMatrix, integerToRational] using
    map_quotientOver integerToRational
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

def rationalSpecialize [Algebra ℚ R] (a b c : R) : RationalCoefficients →+* R :=
  MvPolynomial.eval₂Hom (algebraMap ℚ R) ![a,b,c]

/-- Literal rational polynomial model, coefficient extension, and exact reduced
characteristic polynomial for every parameter in every commutative `ℚ`-algebra.
The endpoint identity is proved without assumptions on `b-1`. -/
theorem rational_polynomial_correspondence [Algebra ℚ R] (a b c : R) :
    universalMatrix.map integerToRational = rationalMatrix ∧
    rationalMatrix.map (rationalSpecialize a b c) = quotientOver a b c ∧
    rationalMatrix.charpoly.map (rationalSpecialize a b c) =
      (quotientOver a b c).charpoly ∧
    rationalMatrix.charpoly.divX.map (rationalSpecialize a b c) =
      reducedCharpoly a b c ∧
    (quotientOver a b c).charpoly = Polynomial.X * reducedCharpoly a b c ∧
    (reducedCharpoly a b c).eval 1 = (1 - quotientOver a b c).det ∧
    (reducedCharpoly a b (endpointT b-a)).eval 1 = -(b-1)*endpointG a b := by
  have hm : rationalMatrix.map (rationalSpecialize a b c) = quotientOver a b c := by
    simpa [rationalMatrix, rationalSpecialize] using
      map_quotientOver (rationalSpecialize a b c)
        (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
  refine ⟨universal_matrix_rational, hm, ?_, ?_, charpoly_zero_factor a b c,
    reduced_eval_one a b c, endpoint_reduced a b⟩
  · rw [← Matrix.charpoly_map, hm]
  · simpa [rationalMatrix, reducedCharpoly, rationalSpecialize] using
      map_reducedCharpoly (rationalSpecialize a b c)
        (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

/-- The universal coefficients evaluate to the existing named real quotient itself,
its characteristic polynomial, and its exact `divX` factor, including the published
endpoint substitution. No positivity or ordering is needed for these algebraic links. -/
theorem actual_real_correspondence (a b c : ℝ) :
    universalMatrix.map (specialize a b c) =
      SixSupportLaplacianLowRoot.quotient a b c ∧
    universalCharpoly.map (specialize a b c) =
      (SixSupportLaplacianLowRoot.quotient a b c).charpoly ∧
    universalReduced.map (specialize a b c) =
      (SixSupportLaplacianLowRoot.quotient a b c).charpoly.divX ∧
    (SixSupportLaplacianLowRoot.quotient a b c).charpoly =
      Polynomial.X * (SixSupportLaplacianLowRoot.quotient a b c).charpoly.divX ∧
    (SixSupportLaplacianLowRoot.quotient a b c).charpoly.divX.eval 1 =
      (1 - SixSupportLaplacianLowRoot.quotient a b c).det ∧
    (SixSupportLaplacianLowRoot.quotient a b (endpointT b-a)).charpoly.divX.eval 1 =
      -(b-1)*endpointG a b := by
  exact ⟨universal_matrix_specialize a b c, universal_charpoly_specialize a b c,
    universal_reduced_specialize a b c, charpoly_zero_factor a b c,
    reduced_eval_one a b c, endpoint_reduced a b⟩

/-- Inner variable is `b`, outer variable is `a`; coefficient field is exactly `ℚ`. -/
def curvePolynomial : Polynomial (Polynomial ℚ) :=
  endpointG Polynomial.X (Polynomial.C (Polynomial.X : Polynomial ℚ))

/-- Exact published coefficient order in `a`, before any degree argument. -/
private theorem curvePolynomial_expansion :
    curvePolynomial =
      Polynomial.C (endpointA (Polynomial.X : Polynomial ℚ)) * Polynomial.X^4
      - Polynomial.C (2*endpointA (Polynomial.X : Polynomial ℚ)*endpointT Polynomial.X) *
        Polynomial.X^3
      + Polynomial.C (endpointA (Polynomial.X : Polynomial ℚ)*(endpointT Polynomial.X)^2
          - endpointB Polynomial.X) * Polynomial.X^2
      + Polynomial.C (endpointB (Polynomial.X : Polynomial ℚ)*endpointT Polynomial.X) *
        Polynomial.X
      + Polynomial.C (endpointC₀ (Polynomial.X : Polynomial ℚ)) := by
  dsimp [curvePolynomial, endpointG, endpointR, endpointT, endpointA, endpointB, endpointC₀]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one]
  ring

private theorem curvePolynomial_natDegree : curvePolynomial.natDegree = 4 := by
  have hA : endpointA (Polynomial.X : Polynomial ℚ) ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : Polynomial ℚ => p.eval 0) h
    norm_num [endpointA] at h0
  rw [curvePolynomial_expansion]
  compute_degree!

/-- A coefficient-ring hom, not pointwise substitution in the spectral variable.
It sends `(a,b,c)` to `(a,b,b(b+2)-a)` in `ℚ[b][a]`. -/
def endpointSubstitution : Universal →+* Polynomial (Polynomial ℚ) :=
  specialize Polynomial.X (Polynomial.C (Polynomial.X : Polynomial ℚ))
    (endpointT (Polynomial.C (Polynomial.X : Polynomial ℚ))-Polynomial.X)

/-- The universal characteristic polynomial and its `divX` factor realize the
actual endpoint polynomial in `ℚ[b][a]`, whose degree in `a` is four.
This does not assert total degree seven or any geometric property. -/
theorem endpoint_polynomial_correspondence :
    universalCharpoly.map endpointSubstitution =
      Polynomial.X * universalReduced.map endpointSubstitution ∧
    (universalReduced.map endpointSubstitution).eval 1 =
      -(Polynomial.C (Polynomial.X : Polynomial ℚ)-1)*curvePolynomial ∧
    curvePolynomial.natDegree = 4 := by
  refine ⟨?_, ?_, curvePolynomial_natDegree⟩
  · rw [endpointSubstitution, universal_charpoly_specialize, universal_reduced_specialize]
    exact charpoly_zero_factor _ _ _
  · rw [endpointSubstitution, universal_reduced_specialize]
    exact endpoint_reduced _ _

/-- The exact endpoint spectral locus of the existing real quotient. In particular,
`b=1` is a separate component and has not been canceled to obtain `G=0`. -/
theorem actual_real_endpoint_spectrum (a b : ℝ) :
    (1 : ℝ) ∈ spectrum ℝ
      (SixSupportLaplacianLowRoot.quotient a b (endpointT b-a)) ↔
        b = 1 ∨ endpointG a b = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (quotientOver a b (endpointT b-a)).charpoly.eval 1 = 0 ↔
    b = 1 ∨ endpointG a b = 0
  rw [charpoly_zero_factor]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, endpoint_reduced,
    mul_eq_zero, neg_eq_zero, sub_eq_zero]

/-- Two independent variables, in the order a,b. -/
def planePolynomial : MvPolynomial (Fin 2) ℚ :=
  endpointG (MvPolynomial.X 0) (MvPolynomial.X 1)

/-- The degree-seven term in b has coefficient -1. -/
theorem planePolynomial_septic_coefficient :
    planePolynomial.coeff (Finsupp.single 1 7) = -1 := by
  classical
  unfold planePolynomial endpointG endpointR endpointA endpointB endpointC₀ endpointT
  ring_nf
  simp only [← map_ofNat (MvPolynomial.C : ℚ →+* MvPolynomial (Fin 2) ℚ)]
  simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X, MvPolynomial.C_apply,
    MvPolynomial.monomial_pow, MvPolynomial.monomial_mul_monomial, MvPolynomial.coeff_add,
    MvPolynomial.coeff_monomial, MvPolynomial.coeff_one, MvPolynomial.coeff_neg, MvPolynomial.coeff_sub]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_two]

private theorem td_add {p q : MvPolynomial (Fin 2) ℚ} {m n : ℕ}
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    (p+q).totalDegree ≤ max m n :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le_max hp hq)
private theorem td_sub {p q : MvPolynomial (Fin 2) ℚ} {m n : ℕ}
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    (p-q).totalDegree ≤ max m n :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le_max hp hq)
private theorem td_mul {p q : MvPolynomial (Fin 2) ℚ} {m n : ℕ}
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    (p*q).totalDegree ≤ m+n :=
  (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
private theorem td_pow {p : MvPolynomial (Fin 2) ℚ} {m : ℕ}
    (hp : p.totalDegree ≤ m) (n : ℕ) : (p^n).totalDegree ≤ n*m :=
  (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left n hp)

/-- Total degree in the actual independent variables a,b, including all terms. -/
theorem planePolynomial_totalDegree : planePolynomial.totalDegree = 7 := by
  classical
  let x : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0
  let y : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 1
  have hx : x.totalDegree ≤ 1 := by simp [x]
  have hy : y.totalDegree ≤ 1 := by simp [y]
  have hn (n : ℕ) : (n : MvPolynomial (Fin 2) ℚ).totalDegree ≤ 0 := by
    simpa only [MvPolynomial.C_eq_coe_nat] using
      (MvPolynomial.totalDegree_C (σ := Fin 2) (n : ℚ)).le
  have ht : (endpointT y).totalDegree ≤ 2 := by
    unfold endpointT
    exact td_mul hy (td_add hy (hn 2))
  have hA : (endpointA y).totalDegree ≤ 1 := by
    unfold endpointA
    exact td_sub (td_mul (hn 3) hy) (hn 1)
  have hB : (endpointB y).totalDegree ≤ 3 := by
    unfold endpointB
    exact td_mul hy
      (td_sub (td_add (td_pow hy 2) (td_mul (hn 4) hy)) (hn 1))
  have hc1 : (y^2+2*y-1).totalDegree ≤ 2 := by
    exact td_sub (td_add (td_pow hy 2) (td_mul (hn 2) hy)) (hn 1)
  have hc2 : (y^2+3*y-1).totalDegree ≤ 2 := by
    exact td_sub (td_add (td_pow hy 2) (td_mul (hn 3) hy)) (hn 1)
  have hc3 : (y^3+3*y^2+3*y-1).totalDegree ≤ 3 := by
    exact td_sub (td_add
      (td_add (td_pow hy 3) (td_mul (hn 3) (td_pow hy 2)))
      (td_mul (hn 3) hy)) (hn 1)
  have hC : (endpointC₀ y).totalDegree ≤ 7 := by
    unfold endpointC₀
    simp only [neg_mul, MvPolynomial.totalDegree_neg]
    exact td_mul (td_mul hc1 hc2) hc3
  have hq : (x*(endpointT y-x)).totalDegree ≤ 3 := by
    exact td_mul hx (td_sub ht hx)
  have hupper : planePolynomial.totalDegree ≤ 7 := by
    change (endpointR y (x*(endpointT y-x))).totalDegree ≤ 7
    unfold endpointR
    exact td_add (td_add (td_mul hA (td_pow hq 2)) (td_mul hB hq)) hC
  have hmem : Finsupp.single 1 7 ∈ planePolynomial.support := by
    rw [MvPolynomial.mem_support_iff, planePolynomial_septic_coefficient]
    norm_num
  have hlower := MvPolynomial.le_totalDegree hmem
  norm_num at hlower
  exact Nat.le_antisymm hupper hlower
/-- Evaluation in the two coefficient variables is the actual endpoint expression. -/
theorem curvePolynomial_evaluate {S : Type*} [CommRing S] [Algebra ℚ S] (a b : S) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℚ S) b) a
      curvePolynomial = endpointG a b := by
  simp [curvePolynomial,endpointG,endpointR,endpointT,endpointA,endpointB,endpointC₀,
    Polynomial.eval₂_pow,Polynomial.eval₂_mul]

/-- Identify the literal previously checked tower polynomial, rather than assuming a bridge. -/
theorem curvePolynomial_eq_actualQuartic :
    curvePolynomial = NikandishE3.actualQuartic := by
  dsimp [curvePolynomial, endpointG, endpointR, endpointT, endpointA, endpointB, endpointC₀,
    NikandishE3.actualQuartic, NikandishE3.A, NikandishE3.B, NikandishE3.t, NikandishE3.C₀]
  simp only [map_add,map_sub,map_mul,map_pow,map_neg,map_ofNat,map_one]
  ring

/-- This uses the actual matrix polynomial, with its coefficient extension checked above. -/
theorem actual_curve_geometric_irreducibility :
    Irreducible (curvePolynomial.map (NikandishE3.pk (AlgebraicClosure ℚ))) := by
  rw [curvePolynomial_eq_actualQuartic]
  exact NikandishE3.actual_geometric_irreducibility

/-- The bivariate model is the same polynomial, with a as the outer variable. -/
def planeToIterated : MvPolynomial (Fin 2) ℚ →+* Polynomial (Polynomial ℚ) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![Polynomial.X, Polynomial.C Polynomial.X]

theorem plane_to_iterated : planeToIterated planePolynomial = curvePolynomial := by
  simp [planeToIterated,planePolynomial,curvePolynomial,endpointG,endpointR,
    endpointT,endpointA,endpointB,endpointC₀]

def planeEndpointSubstitution : Universal →+* MvPolynomial (Fin 2) ℚ :=
  specialize (MvPolynomial.X 0) (MvPolynomial.X 1)
    (endpointT (MvPolynomial.X 1)-MvPolynomial.X 0)

theorem universal_plane_endpoint :
    (universalReduced.map planeEndpointSubstitution).eval 1 =
      -(MvPolynomial.X 1-1)*planePolynomial := by
  rw [planeEndpointSubstitution,universal_reduced_specialize]
  exact endpoint_reduced _ _

/-- The special component b=1 is retained for every real a. -/
theorem actual_real_b_one_spectrum (a : ℝ) :
    (1 : ℝ) ∈ spectrum ℝ
      (SixSupportLaplacianLowRoot.quotient a 1 (endpointT 1-a)) := by
  exact (actual_real_endpoint_spectrum a 1).2 (Or.inl rfl)

/-- Zero is an actual eigenvalue for every parameter triple; degeneracies are retained. -/
theorem actual_real_zero_spectrum (a b c : ℝ) :
    (0 : ℝ) ∈ spectrum ℝ (SixSupportLaplacianLowRoot.quotient a b c) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (quotientOver a b c).charpoly.eval 0 = 0
  rw [charpoly_zero_factor]
  simp

/-- Integer-to-rational coefficient extension commutes with both exact polynomials. -/
theorem integer_to_rational_charpoly :
    universalCharpoly.map integerToRational = rationalMatrix.charpoly ∧
    universalReduced.map integerToRational = rationalMatrix.charpoly.divX := by
  constructor
  · rw [universalCharpoly, ← Matrix.charpoly_map, universal_matrix_rational]
  · simpa [universalReduced,universalCharpoly,universalMatrix,rationalMatrix,
      reducedCharpoly,integerToRational] using
      map_reducedCharpoly integerToRational
        (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

/-- No remainder is discarded in the universal integer model. -/
theorem universal_exact_zero_factor :
    universalCharpoly = Polynomial.X * universalReduced :=
  charpoly_zero_factor (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

theorem actual_curve_fraction_polynomial (k : Type*) [Field k] [CharZero k] :
    (curvePolynomial.map (NikandishE3.pk k)).map
      (algebraMap (Polynomial k) (NikandishE3.K k)) = NikandishE3.g k := by
  rw [curvePolynomial_eq_actualQuartic,NikandishE3.coefficient_extension,NikandishE3.g_map]

/-- The existing real matrix is evaluated against the literal tower quartic. -/
theorem actual_real_tower_endpoint (a b : ℝ) :
    (SixSupportLaplacianLowRoot.quotient a b (endpointT b-a)).charpoly.divX.eval 1 =
      -(b-1)*Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℚ ℝ) b) a
        NikandishE3.actualQuartic := by
  rw [← curvePolynomial_eq_actualQuartic,curvePolynomial_evaluate]
  exact endpoint_reduced a b

theorem actual_real_tower_spectrum (a b : ℝ) :
    (1 : ℝ) ∈ spectrum ℝ
      (SixSupportLaplacianLowRoot.quotient a b (endpointT b-a)) ↔
      b = 1 ∨ Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℚ ℝ) b) a
        NikandishE3.actualQuartic = 0 := by
  rw [← curvePolynomial_eq_actualQuartic,curvePolynomial_evaluate]
  exact actual_real_endpoint_spectrum a b

/-- In a nontrivial coefficient ring, the characteristic polynomial has degree six. -/
theorem charpoly_degree_six [Nontrivial R] (a b c : R) :
    (quotientOver a b c).charpoly.natDegree = 6 := by
  rw [Matrix.charpoly_natDegree_eq_dim]
  rfl

/-- Exact X division has degree five, independently of additional zero multiplicities. -/
theorem reduced_degree_five [Nontrivial R] (a b c : R) :
    (reducedCharpoly a b c).natDegree = 5 := by
  rw [reducedCharpoly,Polynomial.natDegree_divX_eq_natDegree_tsub_one,charpoly_degree_six]

set_option pp.universes true

end D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial
