/- GID: D5/S3/Zeros/FiskToeplitzRefutation
   generality: I
   mirror-B: D5/B/S3/Zeros/FiskToeplitzRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/FiskToeplitzRefutation.claim; result=D5/S3/Zeros/FiskToeplitzRefutation.result; claim=D5/S3/Zeros/FiskToeplitzRefutation.claim
   digest: A positive upper bivariate polynomial has a non-Hurwitz coefficient-Toeplitz minor. -/
/- result: proof_shape: bind-only; escape_witness: none.
   admission_basis: open-problem-resolution (#21768; Refuted)
   Direct frozen dependencies: none (all declarations use pinned Mathlib only).
   Upper: proof_shape: bind-only (source definition); consumer: PositiveUpper.
   PositiveUpper: proof_shape: bind-only (source definition); consumers: claim, f_positive.
   HurwitzStable: proof_shape: bind-only (source definition); consumer: claim.
   toeplitz: proof_shape: bind-only (source definition); consumers: minor, minor_matrix.
   minor: proof_shape: bind-only (source definition); consumers: claim, minor_factor, minor_root.
   claim: proof_shape: bind-only (source definition); consumer: result.
   f: proof_shape: bind-only (concrete polynomial data); consumers: f_expanded, f_positive.
   z: proof_shape: bind-only (concrete complex data); consumers: z_re, z_quadratic, minor_root.
   f_expanded: proof_shape: bind-only; consumer: f_coeff; escape_witness: none.
   f_coeff: proof_shape: bind-only; consumers: f_positive, minor_matrix; escape_witness: none.
   f_positive: proof_shape: bind-only; consumer: result; escape_witness: none.
   det5: proof_shape: bind-only; consumer: minor_factor; escape_witness: none.
   minor_matrix: proof_shape: bind-only; consumer: minor_factor; escape_witness: none.
   minor_factor: proof_shape: bind-only; consumer: minor_root; escape_witness: none.
   z_re: proof_shape: bind-only; consumer: result; escape_witness: none.
   z_quadratic: proof_shape: bind-only; consumer: minor_root; escape_witness: none.
   minor_root: proof_shape: bind-only; consumer: result; escape_witness: none.
   The public result is the designated refutation result (`basis=refutes`) and is exempt
   from four-slot escape registration (CLAUDE.md §3.9).
   The real bivariate carrier is written without a type alias; evaluation and index maps
   use Mathlib operations directly, with the preregistered bodies unchanged.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace D5.S3.Zeros.FiskToeplitzRefutation

open Polynomial


/-- U₂: nonvanishing whenever both variables are in the open upper half plane. -/
def Upper (f : Polynomial (Polynomial ℝ)) : Prop :=
  ∀ (x : ℂ) (y : ℂ), x ∈ UpperHalfPlane.upperHalfPlaneSet →
    y ∈ UpperHalfPlane.upperHalfPlaneSet → f.eval₂ (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) x) y ≠ 0

/-- P₂⁺ in Question 10: U₂ and strictly positive coefficients on the support. -/
def PositiveUpper (f : Polynomial (Polynomial ℝ)) : Prop :=
  Upper f ∧ ∀ (i : ℕ) (j : ℕ), (f.coeff j).coeff i ≠ 0 →
    0 < (f.coeff j).coeff i

/-- All complex roots lie in the closed left half plane.
The root multiset of zero is empty, so structural zero minors are admitted. -/
def HurwitzStable (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, z ∈ (p.map (algebraMap ℝ ℂ)).roots → z.re ≤ 0

/-- Matrix (5), indexed from zero; coefficients above the degree are already zero. -/
noncomputable def toeplitz (f : Polynomial (Polynomial ℝ)) : Matrix ℕ ℕ (Polynomial ℝ) :=
  fun r c => if r ≤ c then f.coeff (c - r) else 0

/-- Rows and columns retain their increasing order. -/
noncomputable def minor (f : Polynomial (Polynomial ℝ)) (n : ℕ)
    (R C : Fin n → ℕ) : Polynomial ℝ :=
  Matrix.det (fun i j : Fin n => toeplitz f (R i) (C j))

/-- Fisk, arXiv:0808.1850v1, Question 10, with structural zero minors allowed. -/
def claim : Prop :=
  ∀ f : Polynomial (Polynomial ℝ), PositiveUpper f →
    ∀ (n : ℕ) (R : Fin n → ℕ) (C : Fin n → ℕ),
      StrictMono R → StrictMono C → HurwitzStable (minor f n R C)

set_option autoImplicit false
set_option maxHeartbeats 1000000

private noncomputable def f : Polynomial (Polynomial ℝ) :=
  (C (4 * X + 1) + X) * (C (X + 4) + X)

private theorem f_expanded :
    f = C (4 * X^2 + 17 * X + 4) + C (5 * X + 5) * X + X^2 := by
  unfold f
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one]
  ring

private theorem f_coeff (j : ℕ) :
    f.coeff j = if j = 0 then 4 * X^2 + 17 * X + 4
      else if j = 1 then 5 * X + 5 else if j = 2 then 1 else 0 := by
  rw [f_expanded]
  simp only [coeff_add, coeff_C_mul_X, coeff_X_pow, coeff_C]
  split_ifs <;> simp_all

private theorem f_positive : PositiveUpper f := by
  constructor
  · intro x y hx hy
    have hx' : 0 < x.im := hx
    have hy' : 0 < y.im := hy
    have h1 : (4*x+y+1 : ℂ) ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      norm_num at hi
      linarith
    have h2 : (x+y+4 : ℂ) ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      norm_num at hi
      linarith
    simpa [f, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.coe_eval₂RingHom, add_assoc, add_comm, add_left_comm] using mul_ne_zero h1 h2
  · intro i j h
    rcases j with _ | _ | _ | j <;>
      rcases i with _ | _ | _ | i <;>
      norm_num [f_coeff, coeff_add, coeff_ofNat_mul, coeff_X_pow, coeff_X,
        coeff_ofNat_zero, coeff_ofNat_succ, coeff_one] at h
    all_goals norm_num [f_coeff, coeff_add, coeff_ofNat_mul, coeff_X_pow, coeff_X,
      coeff_ofNat_zero, coeff_ofNat_succ, coeff_one]

private theorem det5 (a b : ℝ[X]) :
    Matrix.det !![b,1,0,0,0; a,b,1,0,0; 0,a,b,1,0; 0,0,a,b,1; 0,0,0,a,b] =
      b * (b^2 - a) * (b^2 - 3*a) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]
  ring


private theorem minor_matrix :
    (fun i j : Fin 5 => toeplitz f i.val (j.val + 1)) =
      !![5*X+5,1,0,0,0;
        4*X^2+17*X+4,5*X+5,1,0,0;
        0,4*X^2+17*X+4,5*X+5,1,0;
        0,0,4*X^2+17*X+4,5*X+5,1;
        0,0,0,4*X^2+17*X+4,5*X+5] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toeplitz, f_coeff]

private theorem minor_factor :
    minor f 5 Fin.val (fun i => i.val + 1) =
      5 * (X+1) * (21*X^2+33*X+21) * (13*X^2-X+13) := by
  unfold minor
  rw [minor_matrix, det5]
  ring

private noncomputable def z : ℂ := (1 + 15 * Complex.I * (Real.sqrt 3 : ℂ)) / 26

private theorem z_re : z.re = 1/26 := by
  norm_num [z, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

private theorem z_quadratic : (13*z^2 - z + 13 : ℂ) = 0 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    norm_num [z, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, pow_two]
  <;> nlinarith [hs]

private theorem minor_root :
    z ∈ ((minor f 5 Fin.val (fun i => i.val + 1)).map (algebraMap ℝ ℂ)).roots := by
  apply (Polynomial.mem_roots' ).2
  constructor
  · intro h
    have hh := congrArg (fun p : ℂ[X] => p.eval 0) h
    norm_num [minor_factor] at hh
  · change Polynomial.eval z ((minor f 5 Fin.val (fun i => i.val + 1)).map (algebraMap ℝ ℂ)) = 0
    simp [minor_factor, z_quadratic]

theorem result : ¬ D5.S3.Zeros.FiskToeplitzRefutation.claim := by
  intro hc
  have hr : StrictMono (Fin.val : Fin 5 → ℕ) := Fin.val_strictMono
  have hcol : StrictMono (fun i : Fin 5 => i.val + 1) := Fin.val_strictMono.add_const 1
  have hh := hc f f_positive 5 Fin.val (fun i => i.val + 1) hr hcol z minor_root
  rw [z_re] at hh
  norm_num at hh

end D5.S3.Zeros.FiskToeplitzRefutation
