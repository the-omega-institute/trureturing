/- GID: D5/S3/Geometry/FlatlandImageAlgebra
   generality: G
   mirror-B: D5/B/S3/Geometry/FlatlandImageAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial deformations and linear algebra for two-camera image closure. -/

/-
admission_basis: escape-witness
escape_witness: rank_two_pair_curves (used by diagonal_rank_two_pair_curves)
Direct frozen dependencies: C = D5/S3/Arith/Lattices/CofactorKernel.cofactor @
  sha256:3166337f4d6d020e4b4c7683bf2c13d3987b090b3e99f722181e1790e47736fd.
The signed-minor expression in cofactorMatrix is literal; proofs use the cofactor owner.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30117
Declaration classifications (same-delivery helpers expanded; C denotes the declaration above):
ImagingDomain | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: theta, imageClosure, imageClosure_polynomial_specialization, raw_imaging_realization, D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure, D5.S3.Geometry.FlatlandImageClosure.postcompose_actual, D5.S3.Geometry.FlatlandImageClosure.imageClosure_postcompose, D5.S3.Geometry.FlatlandImageEquations.imageClosure_equations_of_actual, D5.S3.Geometry.FlatlandImageEquations.actual_image_equations.
theta | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure, imageClosure_polynomial_specialization, raw_imaging_realization, D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure, D5.S3.Geometry.FlatlandImageClosure.postcompose_actual, D5.S3.Geometry.FlatlandImageClosure.imageClosure_postcompose, D5.S3.Geometry.FlatlandImageEquations.imageClosure_equations_of_actual, D5.S3.Geometry.FlatlandImageEquations.actual_image_equations.
coordinates | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure, imageClosure_polynomial_specialization, D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure, D5.S3.Geometry.FlatlandImageClosure.imageClosure_postcompose, D5.S3.Geometry.FlatlandImageEquations.minorPolynomial_eval, D5.S3.Geometry.FlatlandImageEquations.eightPointPolynomial_eval, D5.S3.Geometry.FlatlandImageEquations.imageClosure_equations_of_actual.
Multihomogeneous | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure, imageClosure_polynomial_specialization, D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure, D5.S3.Geometry.FlatlandImageClosure.imageClosure_postcompose, D5.S3.Geometry.FlatlandImageEquations.minorPolynomial_multihomogeneous, D5.S3.Geometry.FlatlandImageEquations.eightPointPolynomial_multihomogeneous.
imageClosure | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure_polynomial_specialization, rank_one_closure_from_rank_two, D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure, D5.S3.Geometry.FlatlandImageClosure.normalized_rank_one_closure, D5.S3.Geometry.FlatlandImageClosure.imageClosure_postcompose, D5.S3.Geometry.FlatlandImageClosure.closure_from_bilinear_normal_form, D5.S3.Geometry.FlatlandImageClosure.normalRankOne_closure, D5.S3.Geometry.FlatlandImageClosure.normalRankTwo_closure, D5.S3.Geometry.FlatlandImageClosure.singular_compatible_closure, D5.S3.Geometry.FlatlandImageEquations.imageClosure_equations_of_actual, D5.S3.Geometry.FlatlandImageEquations.imageClosure_implies_equations, D5.S3.Geometry.FlatlandImageEquations.claim, D5.S3.Geometry.FlatlandImageEquations.equations_imply_imageClosure, D5.S3.Geometry.FlatlandImageEquations.result.
segreMatrix | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: cofactorMatrix, equations, D5.S3.Geometry.FlatlandImageEquations.singular_kernel_implies_equations, D5.S3.Geometry.FlatlandImageEquations.equations_imply_singular_kernel, D5.S3.Geometry.FlatlandImageEquations.segre_kernel_bilinear, D5.S3.Geometry.FlatlandImageEquations.minorPolynomial_eval, D5.S3.Geometry.FlatlandImageEquations.imageClosure_equations_of_actual, D5.S3.Geometry.FlatlandImageEquations.actual_image_equations, D5.S3.Geometry.FlatlandImageEquations.equations_imply_imageClosure.
cofactorMatrix | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: equations, D5.S3.Geometry.FlatlandImageEquations.singular_kernel_implies_equations, D5.S3.Geometry.FlatlandImageEquations.equations_imply_singular_kernel, D5.S3.Geometry.FlatlandImageEquations.eightPointPolynomial_eval, D5.S3.Geometry.FlatlandImageEquations.imageClosure_equations_of_actual.
equations | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageEquations.singular_kernel_implies_equations, D5.S3.Geometry.FlatlandImageEquations.equations_imply_singular_kernel, D5.S3.Geometry.FlatlandImageEquations.imageClosure_equations_of_actual, D5.S3.Geometry.FlatlandImageEquations.actual_image_equations, D5.S3.Geometry.FlatlandImageEquations.imageClosure_implies_equations, D5.S3.Geometry.FlatlandImageEquations.claim, D5.S3.Geometry.FlatlandImageEquations.equations_imply_imageClosure, D5.S3.Geometry.FlatlandImageEquations.result.
deformX | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: deform_at_zero, deform_nonzero, deform_compatible, rank_one_closure_from_rank_two.
deformY | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: deform_at_zero, deform_nonzero, deform_compatible, rank_one_closure_from_rank_two.
deform_at_zero | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: rank_one_closure_from_rank_two.
deform_nonzero | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: rank_one_closure_from_rank_two.
deform_compatible | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: rank_one_closure_from_rank_two.
canonicalA | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: canonical_images, rank_two_pair_curves, diagonal_rank_two_pair_curves, D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure.
canonicalB | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: canonical_images, rank_two_pair_curves, diagonal_rank_two_pair_curves.
canonical_images | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: rank_two_pair_curves, diagonal_rank_two_pair_curves.
two_coordinate_ratio | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: rank_two_pair_curves.
rank_two_pair_curves | proof_shape: content; escape_witness: rank_two_pair_curves; Direct frozen dependencies: none; consumers: diagonal_rank_two_pair_curves.
block_weight | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: eval_block_scaling.
eval_block_scaling | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: eval_block_scaling_zero_iff.
eval_block_scaling_zero_iff | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: eval_projective_representatives_zero_iff.
eval_coordinate_curve | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: polynomial_curve_specialization.
polynomial_curve_specialization | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure_polynomial_specialization.
singular_in_matrix_subspace | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageEquations.equations_imply_singular_kernel.
homogeneous_substitution | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageClosure.imageClosure_postcompose.
homogeneous_determinant | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageEquations.minorPolynomial_multihomogeneous, D5.S3.Geometry.FlatlandImageEquations.cofactorPolynomial_homogeneous, D5.S3.Geometry.FlatlandImageEquations.eightPointPolynomial_multihomogeneous.
diagonalB | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: diagonal_image, diagonal_rank_two_pair_curves, D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure.
diagonal_image | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: diagonal_rank_two_pair_curves.
diagonal_rank_two_pair_curves | proof_shape: content; escape_witness: rank_two_pair_curves; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure.
eval_projective_representatives_zero_iff | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure_polynomial_specialization, D5.S3.Geometry.FlatlandImageClosure.imageClosure_postcompose.
imageClosure_polynomial_specialization | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: rank_one_closure_from_rank_two, D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure.
raw_imaging_realization | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageClosure.diagonal_rank_two_closure, D5.S3.Geometry.FlatlandImageClosure.postcompose_actual.
bilinear_projective_mk_zero_iff | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageClosure.compatible_coordinate_change, D5.S3.Geometry.FlatlandImageEquations.actual_image_equations.
rank_one_closure_from_rank_two | proof_shape: content; escape_witness: rank_one_closure_from_rank_two; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageClosure.normalized_rank_one_closure.
finite_row_basis | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: full_rank_row_minor, D5.S3.Geometry.FlatlandImageEquations.equations_imply_singular_kernel.
full_rank_row_minor | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: kernel_nonzero_of_maximal_minors.
kernel_nonzero_of_maximal_minors | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageEquations.equations_imply_singular_kernel.
arbitrary_row_minor_zero | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: cofactor_in_full_kernel.
cofactor_in_full_kernel | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: D5.S3.Geometry.FlatlandImageEquations.equations_imply_singular_kernel.
cofactor_kernel_cross | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: kernel_eq_smul_cofactor.
kernel_eq_smul_cofactor | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: D5.S3.Geometry.FlatlandImageEquations.singular_kernel_implies_equations.
cofactor_nonzero_of_independent_rows | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: C; consumers: D5.S3.Geometry.FlatlandImageEquations.equations_imply_singular_kernel.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Rank
import D5.S3.Arith.Lattices.CofactorKernel

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Geometry.FlatlandImageAlgebra
section
open Matrix

/-- Domain of the source rational imaging map: neither camera image is zero. -/
def ImagingDomain (n : ℕ) :=
  {s : (Fin n → (Projectivization ℂ (Fin 4 → ℂ))) × (Fin 2 → (Projectivization ℂ (Matrix (Fin 3) (Fin 4) ℂ))) //
    ∀ j : Fin n, ∀ i : Fin 2, (s.2 i).rep *ᵥ (s.1 j).rep ≠ 0}

/-- Definition 4.1 with N = 3 and m = (2,2), on its domain of definition. -/
def theta {n : ℕ} (s : ImagingDomain n) : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)) :=
  fun j i => Projectivization.mk ℂ ((s.val.2 i).rep *ᵥ (s.val.1 j).rep) (s.property j i)

/-- Homogeneous coordinates for all 2n image points, using Mathlib representatives. -/
def coordinates {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) : ((Fin n × Fin 2) × Fin 3) → ℂ :=
  fun k => (p k.1.1 k.1.2).rep k.2

/-- A polynomial separately homogeneous in each of the 2n projective blocks. -/
def Multihomogeneous {n : ℕ} (f : (MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ)) : Prop :=
  ∃ degree : Fin n × Fin 2 → ℕ, ∀ b : Fin n × Fin 2,
    f.IsWeightedHomogeneous (fun k => if k.1 = b then (1 : ℕ) else 0) (degree b)

/-- Zariski closure in the product of projective spaces, by multihomogeneous vanishing. -/
def imageClosure (n : ℕ) : Set ((Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) :=
  {p | ∀ f : (MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ), Multihomogeneous f →
    (∀ s : ImagingDomain n, MvPolynomial.eval (coordinates (theta s)) f = 0) →
    MvPolynomial.eval (coordinates p) f = 0}

/-- The n by 9 Segre matrix: x-coordinate first, y-coordinate second. -/
def segreMatrix {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) : Matrix (Fin n) (Fin 9) ℂ :=
  fun j k => (p j 0).rep ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k).1 *
    (p j 1).rep ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k).2

/-- Column vectorization: the entry F(b,a) pairs with x(a)y(b). -/
def cofactorMatrix {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (I : Fin 8 ↪ Fin n) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun b a => (-1 : ℂ) ^ (finProdFinEquiv (a,b)).val *
    Matrix.det ((segreMatrix p).submatrix I (finProdFinEquiv (a,b)).succAbove)

/-- Every 9 by 9 Segre minor and every eight-point cofactor determinant vanish. -/
def equations {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) : Prop :=
  (∀ J : Fin 9 ↪ Fin n, Matrix.det ((segreMatrix p).submatrix J id) = 0) ∧
  (∀ I : Fin 8 ↪ Fin n, Matrix.det (cofactorMatrix p I) = 0)

end

section
open Polynomial
variable {K : Type*} [Field K]
open scoped Classical

/-- Polynomial coordinate curves for the first member of a compatible pair. -/
private def deformX (x y : Fin 3 → K) : Fin 3 → K[X] :=
  if x 0 ≠ 0 then fun a => C (x a)
  else if y 0 ≠ 0 then ![-X ^ 2 * C (x 1 * y 1 / y 0), C (x 1), C (x 2)]
  else ![X * C (x 1), C (x 1), C (x 2)]

/-- Polynomial coordinate curves for the second member of a compatible pair. -/
private def deformY (x y : Fin 3 → K) : Fin 3 → K[X] :=
  if x 0 ≠ 0 then ![-X ^ 2 * C (x 1 * y 1 / x 0), C (y 1), C (y 2)]
  else if y 0 ≠ 0 then fun a => C (y a)
  else ![-X * C (y 1), C (y 1), C (y 2)]

private theorem deform_at_zero (x y : Fin 3 → K) (h : x 0 * y 0 = 0) :
    (fun a => (deformX x y a).eval 0) = x ∧
    (fun a => (deformY x y a).eval 0) = y := by
  rcases mul_eq_zero.mp h with hx | hy
  · by_cases hy' : y 0 = 0
    · constructor <;> funext a <;> fin_cases a <;> simp [deformX, deformY, hx, hy']
    · constructor <;> funext a <;> fin_cases a <;> simp [deformX, deformY, hx, hy']
  · by_cases hx : x 0 = 0
    · constructor <;> funext a <;> fin_cases a <;> simp [deformX, deformY, hx, hy]
    · constructor <;> funext a <;> fin_cases a <;> simp [deformX, deformY, hx, hy]

private theorem deform_nonzero (x y : Fin 3 → K) (hx : x ≠ 0) (hy : y ≠ 0) (h : x 0 * y 0 = 0) (t : K) :
    (fun a => (deformX x y a).eval t) ≠ 0 ∧
    (fun a => (deformY x y a).eval t) ≠ 0 := by
  have xnz : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext a
    fin_cases a <;> simp_all
  have ynz : y 0 ≠ 0 ∨ y 1 ≠ 0 ∨ y 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    funext a
    fin_cases a <;> simp_all
  by_cases h0 : x 0 = 0
  · by_cases h1 : y 0 = 0
    · rcases xnz with h | h | h <;> rcases ynz with h' | h' | h'
      all_goals try contradiction
      all_goals constructor
      all_goals intro e
      all_goals first | exact h (by simpa [deformX, h0, h1] using congrFun e 1) | exact h (by simpa [deformX, h0, h1] using congrFun e 2) | exact h' (by simpa [deformY, h0, h1] using congrFun e 1) | exact h' (by simpa [deformY, h0, h1] using congrFun e 2)
    · constructor
      · rcases xnz with h | h | h
        · contradiction
        · intro e; exact h (by simpa [deformX, h0, h1] using congrFun e 1)
        · intro e; exact h (by simpa [deformX, h0, h1] using congrFun e 2)
      · simpa [deformY, h0, h1] using hy
  · constructor
    · simpa [deformX, h0] using hx
    · by_cases h1 : y 1 = 0
      · by_cases h2 : y 2 = 0
        · have hy0 : y 0 = 0 := (mul_eq_zero.mp h).resolve_left h0
          exact False.elim (ynz.elim (fun e => e hy0) (fun e => e.elim (fun e => e h1) (fun e => e h2)))
        · intro e; exact h2 (by simpa [deformY, h0] using congrFun e 2)
      · intro e; exact h1 (by simpa [deformY, h0] using congrFun e 1)

private theorem deform_compatible (x y : Fin 3 → K) (h : x 0 * y 0 = 0) :
    deformX x y 0 * deformY x y 0 + X ^ 2 * deformX x y 1 * deformY x y 1 = 0 := by
  by_cases hx : x 0 = 0
  · by_cases hy : y 0 = 0
    · simp [deformX, deformY, hx, hy]; ring
    · have hc : C (x 1 * y 1 / y 0) * C (y 0) = C (x 1) * C (y 1) := by
        rw [← C_mul, div_mul_cancel₀ _ hy, C_mul]
      simp only [deformX, deformY, hx, ne_eq, not_true_eq_false, if_false, hy,
        not_false_eq_true, if_true, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -X ^ 2 * hc
  · have hc : C (x 1 * y 1 / x 0) * C (x 0) = C (x 1) * C (y 1) := by
      rw [← C_mul, div_mul_cancel₀ _ hx, C_mul]
    simp only [deformX, deformY, if_pos hx, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -X ^ 2 * hc

end

section
open Polynomial Matrix
open scoped Classical
variable {K : Type*} [Field K]

def canonicalA : Matrix (Fin 3) (Fin 4) K :=
  ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0]]

private def canonicalB : Matrix (Fin 3) (Fin 4) K :=
  ![![1,0,0,0], ![0,1,0,0], ![0,0,1,1]]

private theorem canonical_images (q : Fin 4 → K) :
    canonicalA *ᵥ q = ![q 0,q 1,q 2] ∧
    canonicalB *ᵥ q = ![q 0,q 1,q 2 + q 3] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [canonicalA, canonicalB, mulVec, dotProduct, Fin.sum_univ_succ]

private theorem two_coordinate_ratio (x y : Fin 3 → K)
    (hx : x 0 ≠ 0 ∨ x 1 ≠ 0) (hy : y 0 ≠ 0 ∨ y 1 ≠ 0)
    (h : x 0 * y 1 - x 1 * y 0 = 0) :
    ∃ a : K, a ≠ 0 ∧ y 0 = a * x 0 ∧ y 1 = a * x 1 := by
  by_cases h0 : x 0 = 0
  · have hx1 : x 1 ≠ 0 := hx.resolve_left (not_not_intro h0)
    have hy0 : y 0 = 0 := by
      have hh : x 1 * y 0 = 0 := by simpa [h0] using h
      exact (mul_eq_zero.mp hh).resolve_left hx1
    have hy1 : y 1 ≠ 0 := hy.resolve_left (not_not_intro hy0)
    refine ⟨y 1 / x 1, div_ne_zero hy1 hx1, ?_, ?_⟩
    · simp [hy0, h0]
    · rw [div_mul_cancel₀ _ hx1]
  · have hy0 : y 0 ≠ 0 := by
      intro he
      have hy1 : y 1 = 0 := (mul_eq_zero.mp (by simpa [he] using h)).resolve_left h0
      exact hy.elim (fun e => e he) (fun e => e hy1)
    refine ⟨y 0 / x 0, div_ne_zero hy0 h0, ?_, ?_⟩
    · rw [div_mul_cancel₀ _ h0]
    · rw [div_mul_eq_mul_div]
      apply (eq_div_iff h0).2
      linear_combination h

/-- Canonical rank-two compatibility admits simultaneous nonzero coordinate curves and raw reconstructions. -/
private theorem rank_two_pair_curves (x y : Fin 3 → K) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x 0 * y 1 - x 1 * y 0 = 0) :
    ∃ Xc Yc : Fin 3 → K[X],
      (fun a => (Xc a).eval 0) = x ∧
      (fun a => (Yc a).eval 0) = y ∧
      (∀ t, (fun a => (Xc a).eval t) ≠ 0 ∧ (fun a => (Yc a).eval t) ≠ 0) ∧
      ∀ t : K, t ≠ 0 → ∃ q : Fin 4 → K, ∃ a b : K,
        a ≠ 0 ∧ b ≠ 0 ∧
        canonicalA *ᵥ q = a • (fun k => (Xc k).eval t) ∧
        canonicalB *ᵥ q = b • (fun k => (Yc k).eval t) := by
  by_cases hxe : x 0 = 0 ∧ x 1 = 0
  · have hx2 : x 2 ≠ 0 := by
      intro he
      apply hx
      funext i
      fin_cases i <;> simp_all
    by_cases hye : y 0 = 0 ∧ y 1 = 0
    · refine ⟨fun i => C (x i), fun i => C (y i), ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro t; simpa using And.intro hx hy
      · intro t ht
        refine ⟨![0,0,x 2,y 2-x 2], 1, 1, one_ne_zero, one_ne_zero, ?_, ?_⟩
        · rw [(canonical_images _).1]
          funext i; fin_cases i <;> simp [hxe.1, hxe.2]
        · rw [(canonical_images _).2]
          funext i; fin_cases i <;> simp [hye.1, hye.2]
    · refine ⟨![X * C (y 0), X * C (y 1), C (x 2)], fun i => C (y i), ?_, ?_, ?_, ?_⟩
      · funext i; fin_cases i <;> simp [hxe.1, hxe.2]
      · simp
      · intro t
        constructor
        · intro he; exact hx2 (by simpa using congrFun he 2)
        · simpa using hy
      · intro t ht
        refine ⟨![t*y 0,t*y 1,x 2,t*y 2-x 2], 1, t, one_ne_zero, ht, ?_, ?_⟩
        · rw [(canonical_images _).1]
          funext i; fin_cases i <;> simp <;> ring
        · rw [(canonical_images _).2]
          funext i; fin_cases i <;> simp <;> ring
  · have hxn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by simpa only [not_and_or, ne_eq] using hxe
    by_cases hye : y 0 = 0 ∧ y 1 = 0
    · have hy2 : y 2 ≠ 0 := by
        intro he
        apply hy
        funext i; fin_cases i <;> simp_all
      refine ⟨fun i => C (x i), ![X * C (x 0), X * C (x 1), C (y 2)], ?_, ?_, ?_, ?_⟩
      · simp
      · funext i; fin_cases i <;> simp [hye.1, hye.2]
      · intro t
        constructor
        · simpa using hx
        · intro he; exact hy2 (by simpa using congrFun he 2)
      · intro t ht
        refine ⟨![t*x 0,t*x 1,t*x 2,y 2-t*x 2], t, 1, ht, one_ne_zero, ?_, ?_⟩
        · rw [(canonical_images _).1]
          funext i; fin_cases i <;> simp <;> ring
        · rw [(canonical_images _).2]
          funext i; fin_cases i <;> simp <;> ring
    · have hyn : y 0 ≠ 0 ∨ y 1 ≠ 0 := by simpa only [not_and_or, ne_eq] using hye
      obtain ⟨a, ha, ha0, ha1⟩ := two_coordinate_ratio x y hxn hyn h
      refine ⟨fun i => C (x i), fun i => C (y i), ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro t; simpa using And.intro hx hy
      · intro t ht
        refine ⟨![x 0,x 1,x 2,y 2/a-x 2], 1, a⁻¹, one_ne_zero, inv_ne_zero ha, ?_, ?_⟩
        · rw [(canonical_images _).1]
          funext i; fin_cases i <;> simp <;> ring
        · rw [(canonical_images _).2]
          funext i; fin_cases i <;> simp [ha0, ha1, ha, div_eq_mul_inv] <;> ring
end

section
open scoped BigOperators
open scoped Classical

variable {K B A : Type*} [Field K] [Fintype B] [Fintype A] [DecidableEq B]

private theorem block_weight (d : (B × A) →₀ ℕ) (b : B) :
    Finsupp.weight (fun k : B × A => if k.1 = b then (1 : ℕ) else 0) d =
      ∑ a : A, d (b,a) := by
  simp only [Finsupp.weight_eq_sum, Fintype.sum_prod_type, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- Evaluation transforms by its degree character under independent block scaling. -/
private theorem eval_block_scaling (f : MvPolynomial (B × A) K) (D : B → ℕ)
    (hf : ∀ b : B, f.IsWeightedHomogeneous
      (fun k : B × A => if k.1 = b then (1 : ℕ) else 0) (D b))
    (c : B → K) (z : B × A → K) :
    MvPolynomial.eval (fun k => c k.1 * z k) f =
      (∏ b : B, c b ^ D b) * MvPolynomial.eval z f := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdegree (b : B) : ∑ a : A, d (b,a) = D b := by
    rw [← block_weight]
    exact hf b (MvPolynomial.mem_support_iff.mp hd)
  simp_rw [mul_pow, Fintype.prod_prod_type, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdegree]
  ring

/-- A nonzero change of scale in each block preserves a multihomogeneous zero. -/
private theorem eval_block_scaling_zero_iff (f : MvPolynomial (B × A) K) (D : B → ℕ)
    (hf : ∀ b : B, f.IsWeightedHomogeneous
      (fun k : B × A => if k.1 = b then (1 : ℕ) else 0) (D b))
    (c : B → K) (hc : ∀ b, c b ≠ 0) (z : B × A → K) :
    MvPolynomial.eval (fun k => c k.1 * z k) f = 0 ↔ MvPolynomial.eval z f = 0 := by
  rw [eval_block_scaling f D hf c z, mul_eq_zero]
  have hn : (∏ b : B, c b ^ D b) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun b _ => pow_ne_zero _ (hc b))
  exact or_iff_right hn

/-- Polynomial substitution commutes with specialization of its coordinate curves. -/
private theorem eval_coordinate_curve (f : MvPolynomial (B × A) K)
    (z : B × A → _root_.Polynomial K) (t : K) :
    (MvPolynomial.eval₂ Polynomial.C z f).eval t =
      MvPolynomial.eval (fun k => (z k).eval t) f := by
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id K := by
    exact Polynomial.eval₂RingHom_comp_C (RingHom.id K) t
  have hh := MvPolynomial.hom_eval₂ f Polynomial.C (Polynomial.evalRingHom t) z
  rw [hC] at hh
  exact hh

/-- Vanishing at every nonzero parameter specializes to vanishing at zero. -/
private theorem polynomial_curve_specialization [Infinite K] (f : MvPolynomial (B × A) K)
    (z : B × A → _root_.Polynomial K)
    (h : ∀ t : K, t ≠ 0 → MvPolynomial.eval (fun k => (z k).eval t) f = 0) :
    MvPolynomial.eval (fun k => (z k).eval 0) f = 0 := by
  let q := MvPolynomial.eval₂ Polynomial.C z f
  have hq : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : K))).mono
    intro t ht
    exact (eval_coordinate_curve f z t).trans (h t ht.2)
  rw [← eval_coordinate_curve]
  change q.eval 0 = 0
  rw [hq]
  simp
end

section
open Matrix
open scoped Classical
variable {K m : Type*} [Field K] [IsAlgClosed K] [Fintype m] [DecidableEq m] [Nonempty m]

/-- A two-dimensional matrix subspace over an algebraically closed field meets the determinant locus. -/
theorem singular_in_matrix_subspace (W : Submodule K (Matrix m m K))
    (U V : Matrix m m K) (hU : U ∈ W) (hV : V ∈ W) (hU0 : U ≠ 0)
    (hVU : ∀ a : K, V ≠ a • U) :
    ∃ F ∈ W, F ≠ 0 ∧ F.det = 0 := by
  classical
  by_cases hdet : U.det = 0
  · exact ⟨U, hU, hU0, hdet⟩
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (U⁻¹ * V).mulVecLin
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  have he : (U⁻¹ * V) *ᵥ v = a • v := hv.apply_eq_smul
  have he' : V *ᵥ v = a • (U *ᵥ v) := by
    have hh := congrArg (fun z => U *ᵥ z) he
    simpa only [mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu, mulVec_smul] using hh
  refine ⟨V - a • U, W.sub_mem hV (W.smul_mem a hU), ?_, ?_⟩
  · exact fun h => hVU a (sub_eq_zero.mp h)
  · apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv.2, ?_⟩
    rw [sub_mulVec, smul_mulVec, he', sub_self]
end

section
open scoped BigOperators Classical

/-- Substituting forms with the prescribed weights preserves weighted homogeneity. -/
theorem homogeneous_substitution {R σ τ : Type*} [CommRing R]
    (w : σ → ℕ) (v : τ → ℕ) (f : MvPolynomial σ R) (m : ℕ)
    (hf : f.IsWeightedHomogeneous w m) (g : σ → MvPolynomial τ R)
    (hg : ∀ i, (g i).IsWeightedHomogeneous v (w i)) :
    (MvPolynomial.eval₂ MvPolynomial.C g f).IsWeightedHomogeneous v m := by
  classical
  refine MvPolynomial.IsWeightedHomogeneous.induction_on
    (motive := fun p _ => (MvPolynomial.eval₂ MvPolynomial.C g p).IsWeightedHomogeneous v m)
    ?_ ?_ ?_ hf
  · simpa using MvPolynomial.isWeightedHomogeneous_zero R v m
  · intro p q hp hq ihp ihq
    simpa only [MvPolynomial.eval₂_add] using ihp.add ihq
  · intro d r hd
    rw [MvPolynomial.eval₂_monomial]
    have hh := MvPolynomial.IsWeightedHomogeneous.prod d.support
      (fun i => g i ^ d i) (fun i => d i * w i)
      (fun i _ => by simpa [nsmul_eq_mul] using (hg i).pow (d i))
    have hdeg : ∑ i ∈ d.support, d i * w i = m := by
      simpa [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using hd
    simpa [Finsupp.prod, hdeg] using hh.C_mul r

/-- A determinant whose entries have a fixed degree in each row has the sum of those degrees. -/
theorem homogeneous_determinant {R σ ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (w : σ → ℕ) (M : Matrix ι ι (MvPolynomial σ R)) (d : ι → ℕ)
    (hM : ∀ i j, (M i j).IsWeightedHomogeneous w (d i)) :
    M.det.IsWeightedHomogeneous w (∑ i, d i) := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro s hs
  have hh := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i => M (s i) i) (fun i => d (s i)) (fun i _ => hM _ _)
  have hdeg : ∑ i, d (s i) = ∑ i, d i := Equiv.sum_comp s d
  have hh' : (∏ i, M (s i) i).IsWeightedHomogeneous w (∑ i, d i) := by
    simpa only [hdeg] using hh
  simpa using hh'.C_mul ((Equiv.Perm.sign s : ℤ) : R)
end

section
open Polynomial Matrix
open scoped Classical
variable {K : Type*} [Field K]

def diagonalB (c : K) : Matrix (Fin 3) (Fin 4) K :=
  ![![0,1,0,0], ![-c⁻¹,0,0,0], ![0,0,1,1]]

private theorem diagonal_image (c : K) (q : Fin 4 → K) :
    diagonalB c *ᵥ q = ![q 1,-c⁻¹*q 0,q 2+q 3] := by
  funext i; fin_cases i <;> simp [diagonalB, mulVec, dotProduct, Fin.sum_univ_succ]

/-- The diagonal rank-two form is realized by fixed cameras along polynomial curves. -/
theorem diagonal_rank_two_pair_curves (c : K) (hc : c ≠ 0)
    (x y : Fin 3 → K) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x 0 * y 0 + c * x 1 * y 1 = 0) :
    ∃ Xc Yc : Fin 3 → K[X],
      (fun a => (Xc a).eval 0) = x ∧
      (fun a => (Yc a).eval 0) = y ∧
      (∀ t, (fun a => (Xc a).eval t) ≠ 0 ∧ (fun a => (Yc a).eval t) ≠ 0) ∧
      ∀ t : K, t ≠ 0 → ∃ q : Fin 4 → K, ∃ a b : K,
        a ≠ 0 ∧ b ≠ 0 ∧
        canonicalA *ᵥ q = a • (fun k => (Xc k).eval t) ∧
        diagonalB c *ᵥ q = b • (fun k => (Yc k).eval t) := by
  let yy : Fin 3 → K := ![-c*y 1,y 0,y 2]
  have hyy : yy ≠ 0 := by
    intro he
    have h0 : y 0 = 0 := by simpa [yy] using congrFun he 1
    have h1 : y 1 = 0 := by
      have hh : -c*y 1 = 0 := by simpa [yy] using congrFun he 0
      exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr hc)
    have h2 : y 2 = 0 := by simpa [yy] using congrFun he 2
    apply hy
    funext i; fin_cases i <;> simp_all
  have hxy : x 0 * yy 1 - x 1 * yy 0 = 0 := by
    dsimp [yy]
    linear_combination h
  obtain ⟨Xc,Zc,hX,hZ,hn,hr⟩ := rank_two_pair_curves x yy hx hyy hxy
  let Yc : Fin 3 → K[X] := ![Zc 1, -C c⁻¹ * Zc 0, Zc 2]
  have hY : (fun a => (Yc a).eval 0) = y := by
    funext i
    have hz0 := congrFun hZ 0
    have hz1 := congrFun hZ 1
    have hz2 := congrFun hZ 2
    fin_cases i <;> simp_all [Yc, yy]
  have hYn t : (fun a => (Yc a).eval t) ≠ 0 := by
    intro he
    have h0 : (Zc 1).eval t = 0 := by simpa [Yc] using congrFun he 0
    have h1 : (Zc 0).eval t = 0 := by
      have hh : -c⁻¹ * (Zc 0).eval t = 0 := by simpa [Yc] using congrFun he 1
      exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr (inv_ne_zero hc))
    have h2 : (Zc 2).eval t = 0 := by simpa [Yc] using congrFun he 2
    apply (hn t).2
    funext i; fin_cases i <;> simp_all
  refine ⟨Xc,Yc,hX,hY,fun t => ⟨(hn t).1,hYn t⟩,?_⟩
  intro t ht
  obtain ⟨q,a,b,ha,hb,hA,hB⟩ := hr t ht
  refine ⟨q,a,b,ha,hb,hA,?_⟩
  rw [diagonal_image]
  have hh := (canonical_images q).2.symm.trans hB
  have hh0 := congrFun hh 0
  have hh1 := congrFun hh 1
  have hh2 := congrFun hh 2
  funext i
  fin_cases i <;> simp_all [Yc] <;> ring
end

section
open scoped Classical

theorem eval_projective_representatives_zero_iff
    {B A : Type*} [Fintype B] [Fintype A] [DecidableEq B]
    (f : MvPolynomial (B × A) ℂ) (D : B → ℕ)
    (hf : ∀ b : B, f.IsWeightedHomogeneous
      (fun k : B × A => if k.1 = b then (1 : ℕ) else 0) (D b))
    (z : B → A → ℂ) (hz : ∀ b, z b ≠ 0) :
    MvPolynomial.eval (fun k => (Projectivization.mk ℂ (z k.1) (hz k.1)).rep k.2) f = 0 ↔
      MvPolynomial.eval (fun k => z k.1 k.2) f = 0 := by
  choose c hc using fun b => Projectivization.exists_smul_eq_mk_rep ℂ (z b) (hz b)
  have he : (fun k : B × A => (Projectivization.mk ℂ (z k.1) (hz k.1)).rep k.2) =
      (fun k : B × A => (c k.1 : ℂ) * z k.1 k.2) := by
    funext k
    exact (congrFun (hc k.1) k.2).symm
  rw [he]
  exact eval_block_scaling_zero_iff f D hf (fun b => (c b : ℂ))
    (fun b => Units.ne_zero (c b)) (fun k => z k.1 k.2)

/-- Membership in the actual defined image closure is stable under nonzero polynomial curves. -/
theorem imageClosure_polynomial_specialization {n : ℕ}
    (z : (Fin n × Fin 2) → Fin 3 → _root_.Polynomial ℂ)
    (hz : ∀ t b, (fun a => (z b a).eval t) ≠ 0)
    (h : ∀ t : ℂ, t ≠ 0 →
      (fun j i => Projectivization.mk ℂ (fun a => (z (j,i) a).eval t) (hz t (j,i))) ∈
        imageClosure n) :
    (fun j i => Projectivization.mk ℂ (fun a => (z (j,i) a).eval 0) (hz 0 (j,i))) ∈
      imageClosure n := by
  intro f hf hvan
  obtain ⟨D, hD⟩ := hf
  apply (eval_projective_representatives_zero_iff f D hD
    (fun b a => (z b a).eval 0) (hz 0)).2
  apply polynomial_curve_specialization f (fun k => z k.1 k.2)
  intro t ht
  apply (eval_projective_representatives_zero_iff f D hD
    (fun b a => (z b a).eval t) (hz t)).1
  exact h t ht f ⟨D, hD⟩ hvan
end

section
open Matrix
open scoped Classical

/-- Raw nonzero camera matrices and world vectors give a point of the multihomogeneous imaging domain. -/
theorem raw_imaging_realization {n : ℕ}
    (A : Fin 2 → Matrix (Fin 3) (Fin 4) ℂ) (q : Fin n → Fin 4 → ℂ)
    (hA : ∀ i, A i ≠ 0) (hq : ∀ j, q j ≠ 0)
    (hAq : ∀ j i, A i *ᵥ q j ≠ 0) :
    ∃ s : ImagingDomain n,
      theta s = fun j i => Projectivization.mk ℂ (A i *ᵥ q j) (hAq j i) := by
  let cameras : Fin 2 → (Projectivization ℂ (Matrix (Fin 3) (Fin 4) ℂ)) := fun i => Projectivization.mk ℂ (A i) (hA i)
  let points : Fin n → (Projectivization ℂ (Fin 4 → ℂ)) := fun j => Projectivization.mk ℂ (q j) (hq j)
  choose c hc using fun i => Projectivization.exists_smul_eq_mk_rep ℂ (A i) (hA i)
  choose d hd using fun j => Projectivization.exists_smul_eq_mk_rep ℂ (q j) (hq j)
  have hcam i : (cameras i).rep = (c i : ℂ) • A i := (hc i).symm
  have hpoint j : (points j).rep = (d j : ℂ) • q j := (hd j).symm
  have himage j i : (cameras i).rep *ᵥ (points j).rep =
      ((c i : ℂ) * (d j : ℂ)) • (A i *ᵥ q j) := by
    rw [hcam, hpoint, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  have hn j i : (cameras i).rep *ᵥ (points j).rep ≠ 0 := by
    rw [himage]
    exact smul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (hAq j i)
  let s : ImagingDomain n := ⟨(points,cameras), hn⟩
  refine ⟨s, ?_⟩
  funext j i
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).2
  refine ⟨c i * d j, ?_⟩
  simpa only [Units.smul_def, Units.val_mul] using (himage j i).symm

theorem bilinear_projective_mk_zero_iff
    (F : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (Projectivization.mk ℂ y hy).rep ⬝ᵥ
      (F *ᵥ (Projectivization.mk ℂ x hx).rep) = 0 ↔ y ⬝ᵥ (F *ᵥ x) = 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y hy
  rw [← ha,← hb]
  simp only [Units.smul_def]
  rw [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul,mul_eq_zero,Units.ne_zero, false_or]
end

section
open scoped Classical

/-- The normalized rank-one boundary follows from the rank-two closure supplier, with no genericity on the tuple. -/
theorem rank_one_closure_from_rank_two {n : ℕ}
    (h2 : ∀ (t : ℂ), t ≠ 0 → ∀ q : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)),
      (∀ j, (q j 0).rep 0 * (q j 1).rep 0 +
        t ^ 2 * (q j 0).rep 1 * (q j 1).rep 1 = 0) → q ∈ imageClosure n)
    (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (hp : ∀ j, (p j 0).rep 0 * (p j 1).rep 0 = 0) :
    p ∈ imageClosure n := by
  let x : Fin n → Fin 3 → ℂ := fun j => (p j 0).rep
  let y : Fin n → Fin 3 → ℂ := fun j => (p j 1).rep
  let z : (Fin n × Fin 2) → Fin 3 → _root_.Polynomial ℂ :=
    fun b => if b.2 = 0 then deformX (x b.1) (y b.1) else deformY (x b.1) (y b.1)
  have hz : ∀ t b, (fun a => (z b a).eval t) ≠ 0 := by
    intro t b
    rcases b with ⟨j,i⟩
    have hh := deform_nonzero (x j) (y j) (p j 0).rep_nonzero
      (p j 1).rep_nonzero (hp j) t
    fin_cases i
    · simpa [z] using hh.1
    · simpa [z] using hh.2
  have hspec := imageClosure_polynomial_specialization z hz
  have hstart : (fun j i => Projectivization.mk ℂ (fun a => (z (j,i) a).eval 0)
      (hz 0 (j,i))) = p := by
    funext j i
    have hh := deform_at_zero (x j) (y j) (hp j)
    fin_cases i
    · simpa [z, hh.1, x] using (p j 0).mk_rep
    · simpa [z, hh.2, y] using (p j 1).mk_rep
  rw [← hstart]
  apply hspec
  intro t ht
  apply h2 t ht
  intro j
  let xx : Fin 3 → ℂ := fun a => (deformX (x j) (y j) a).eval t
  let yy : Fin 3 → ℂ := fun a => (deformY (x j) (y j) a).eval t
  have hn := deform_nonzero (x j) (y j) (p j 0).rep_nonzero (p j 1).rep_nonzero (hp j) t
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ xx hn.1
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ yy hn.2
  have hc : xx 0 * yy 0 + t ^ 2 * xx 1 * yy 1 = 0 := by
    simpa [xx, yy] using congrArg (_root_.Polynomial.eval t) (deform_compatible (x j) (y j) (hp j))
  change (Projectivization.mk ℂ xx hn.1).rep 0 * (Projectivization.mk ℂ yy hn.2).rep 0 +
    t ^ 2 * (Projectivization.mk ℂ xx hn.1).rep 1 * (Projectivization.mk ℂ yy hn.2).rep 1 = 0
  rw [← ha, ← hb]
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
  calc
    _ = (a : ℂ) * (b : ℂ) * (xx 0 * yy 0 + t ^ 2 * xx 1 * yy 1) := by ring
    _ = 0 := by rw [hc, mul_zero]
end

section
open Matrix Module
open scoped Classical

/-- A finite matrix has an independent row subset spanning all its rows. -/
theorem finite_row_basis {K ι d : Type*} [Field K] [Fintype ι] [Fintype d]
    (M : Matrix ι d K) :
    ∃ I : Fin M.rank ↪ ι,
      Submodule.span K (Set.range (M.submatrix I id).row) =
        Submodule.span K (Set.range M.row) ∧
      LinearIndependent K (M.submatrix I id).row := by
  classical
  obtain ⟨κ,a,ha,hspan,hlin⟩ := exists_linearIndependent' K M.row
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = M.rank := by
    calc
      Fintype.card κ = Module.finrank K (Submodule.span K (Set.range (M.row ∘ a))) :=
        (finrank_span_eq_card hlin).symm
      _ = Module.finrank K (Submodule.span K (Set.range M.row)) := by rw [hspan]
      _ = M.rank := M.rank_eq_finrank_span_row.symm
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let I : Fin M.rank ↪ ι := ⟨fun i => a (e i), ha.comp e.injective⟩
  refine ⟨I,?_,?_⟩
  · change Submodule.span K (Set.range ((M.row ∘ a) ∘ e)) = _
    rw [e.surjective.range_comp]
    exact hspan
  · exact hlin.comp e e.injective

/-- Full column rank is witnessed by a square row submatrix. -/
private theorem full_rank_row_minor {K m : Type*} [Field K] [Fintype m]
    {d : ℕ} (M : Matrix m (Fin d) K) (hM : M.rank = d) :
    ∃ I : Fin d ↪ m, (M.submatrix I id).det ≠ 0 := by
  classical
  have hb := finite_row_basis M
  rw [hM] at hb
  obtain ⟨I, _, hI⟩ := hb
  exact ⟨I, isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp hI))⟩

/-- Vanishing full-width minors force a nonzero kernel. -/
theorem kernel_nonzero_of_maximal_minors {K m : Type*} [Field K] [Fintype m]
    {d : ℕ} (M : Matrix m (Fin d) K)
    (h : ∀ I : Fin d ↪ m, (M.submatrix I id).det = 0) :
    ∃ v : Fin d → K, v ≠ 0 ∧ M *ᵥ v = 0 := by
  classical
  by_contra he
  push Not at he
  have hinj : Function.Injective M.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hv0
    exact he v hv0 hv
  have hr : M.rank = d := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨I,hI⟩ := full_rank_row_minor M hr
  exact hI (h I)
end

section
open Matrix
open scoped BigOperators Classical

/-- Repeated rows allow maximal-minor vanishing to be used for every row map. -/
private theorem arbitrary_row_minor_zero {K ι : Type*} [Field K]
    {d : ℕ} (M : Matrix ι (Fin d) K)
    (h : ∀ I : Fin d ↪ ι, (M.submatrix I id).det = 0) (a : Fin d → ι) :
    (M.submatrix a id).det = 0 := by
  classical
  by_cases ha : Function.Injective a
  · exact h ⟨a,ha⟩
  · obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp ha
    apply Matrix.det_zero_of_row_eq hne
    funext k
    exact congrArg (fun v => M v k) he

/-- A signed eight-row cofactor vector annihilates the entire matrix when all nine-row minors vanish. -/
theorem cofactor_in_full_kernel {K ι : Type*} [Field K]
    {d : ℕ} (M : Matrix ι (Fin (d+1)) K)
    (h : ∀ I : Fin (d+1) ↪ ι, (M.submatrix I id).det = 0)
    (I : Fin d ↪ ι) :
    M *ᵥ D5.S3.Arith.Lattices.CofactorKernel.cofactor (M.submatrix I id) = 0 := by
  classical
  funext j
  let N : Matrix (Fin (d+1)) (Fin (d+1)) K := Matrix.of (Fin.cases (M j) (fun i k => M (I i) k))
  have hn : N.det = 0 := by
    have he : N = M.submatrix (Fin.cases j (fun r => I r)) id := by
      ext i k
      refine Fin.cases ?_ (fun r => ?_) i <;> rfl
    rw [he]
    exact arbitrary_row_minor_zero M h (Fin.cases j (fun r => I r))
  rw [Matrix.det_succ_row_zero] at hn
  simpa [N, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, Matrix.mulVec, dotProduct,
    D5.S3.Arith.Lattices.CofactorKernel.cofactor, Matrix.submatrix,
    mul_comm, mul_left_comm, mul_assoc] using hn
end

section
open Matrix
open scoped BigOperators Classical
open D5.S3.Arith.Lattices.CofactorKernel (cofactor)

/-- Any kernel vector is proportional, coordinate by coordinate, to the signed cofactor vector. -/
private theorem cofactor_kernel_cross {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin (d+1)) K) (x : Fin (d+1) → K)
    (hx : A *ᵥ x = 0) (i k : Fin (d+1)) :
    cofactor A k * x i = x k * cofactor A i := by
  classical
  let N : Matrix (Fin (d+1)) (Fin (d+1)) K := Matrix.of (Fin.cases (Pi.single k 1) (fun i j => A i j))
  have hcof (j : Fin (d+1)) : N.adjugate j 0 = cofactor A j := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp [N, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, cofactor, Matrix.submatrix]
  have hdet : N.det = cofactor A k := by
    rw [Matrix.det_succ_row_zero]
    simp [N, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, cofactor, Matrix.submatrix, Pi.single_apply, mul_ite, ite_mul]
  have hNx : N *ᵥ x = Pi.single 0 (x k) := by
    funext j
    refine Fin.cases ?_ (fun r => ?_) j
    · simp [N, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mulVec, dotProduct, Pi.single_apply, ite_mul]
    · simpa [N, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mulVec, dotProduct] using congrFun hx r
  have hh := congrArg (fun C => (C *ᵥ x) i) (Matrix.adjugate_mul N)
  rw [← Matrix.mulVec_mulVec, hNx] at hh
  simpa [hdet, Matrix.mulVec_single, hcof, smul_mulVec, Matrix.col, mul_comm] using hh.symm

/-- A nonzero cofactor vector spans the kernel of the rectangular matrix. -/
theorem kernel_eq_smul_cofactor {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin (d+1)) K) (hc : cofactor A ≠ 0)
    (x : Fin (d+1) → K) (hx : A *ᵥ x = 0) :
    ∃ a : K, x = a • cofactor A := by
  classical
  obtain ⟨k,hk⟩ := Function.ne_iff.mp hc
  refine ⟨x k / cofactor A k, ?_⟩
  funext i
  have hh := cofactor_kernel_cross A x hx i k
  have hi : x i = (x k * cofactor A i) / cofactor A k :=
    (eq_div_iff hk).mpr (by simpa only [mul_comm] using hh)
  simpa [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hi
end

section
open Matrix Module
open scoped BigOperators Classical
open D5.S3.Arith.Lattices.CofactorKernel (cofactor)

/-- Independent rows of a d by d+1 matrix give a nonzero cofactor vector. -/
theorem cofactor_nonzero_of_independent_rows {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin (d+1)) K) (hA : LinearIndependent K A.row) :
    cofactor A ≠ 0 := by
  classical
  let S := Submodule.span K (Set.range A.row)
  have hdim : Module.finrank K S = d := by
    simpa [S] using finrank_span_eq_card hA
  have htop : S ≠ ⊤ := by
    intro he
    rw [he, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    omega
  obtain ⟨v,hv⟩ : ∃ v : Fin (d+1) → K, v ∉ S := by
    by_contra he
    push Not at he
    apply htop
    ext v
    simp only [Submodule.mem_top, iff_true]
    exact he v
  let N : Matrix (Fin (d+1)) (Fin (d+1)) K := Matrix.of (Fin.cases v (fun i j => A i j))
  have hN : LinearIndependent K N.row := by
    apply linearIndependent_finSucc.mpr
    exact ⟨hA,hv⟩
  have hdet : N.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp hN)).ne_zero
  intro hc
  apply hdet
  rw [Matrix.det_succ_row_zero]
  calc
    _ = ∑ k, v k * cofactor A k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [N, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, Fin.cases_zero, cofactor, Matrix.submatrix, id_eq]
      ring
    _ = 0 := by rw [hc]; simp
end
end D5.S3.Geometry.FlatlandImageAlgebra
