/- GID: D5/S3/Quantum/Divergence/UmegakiConditionalKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiConditionalKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native arithmetic inverse quadratic forms and quantum partial-trace residuals. -/

import D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-! The inverse and coordinates are those of the native arithmetic operator.
The real positive-form Cauchy--Schwarz inequality applies to arbitrary complex
matrix directions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open HilbertSchmidtOperatorSpace
open D5.S3.Quantum.Divergence.UmegakiArithmeticBKM

namespace D5.S3.Quantum.Divergence.UmegakiConditionalKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The arithmetic map in the original native matrix coordinates. -/
def arithmetic (Z X : Matrix ι ι ℂ) (u : ℝ) : Matrix ι ι ℂ :=
  (1-u) • (Z * X) + u • (X * Z)

/-- Matrix coordinates of the native Hilbert--Schmidt inverse. -/
def inverseMatrix (Z V : Matrix ι ι ℂ) (u : ℝ) : Matrix ι ι ℂ :=
  matrixHS.symm ((hsArithmeticMap Z u).inverse (matrixHS V))

/-- The quadratic form uses the actual continuous-linear-map inverse. -/
def q (Z V : Matrix ι ι ℂ) (u : ℝ) : ℝ :=
  (inner ℂ (matrixHS V) ((hsArithmeticMap Z u).inverse (matrixHS V))).re

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
lemma arithmetic_inverse_pairing_intervalIntegrable (Z H : Matrix ι ι ℂ)
    (hZ : Z.PosDef) :
    IntervalIntegrable (fun u : ℝ =>
      (inner ℂ (matrixHS H) ((hsArithmeticMap Z u).inverse (matrixHS H))).re)
      volume 0 1 := by
  let U : Matrix ι ι ℂ := hZ.isHermitian.eigenvectorUnitary
  let W := Uᴴ * H * U
  let f := fun (i j : ι) (u : ℝ) => Complex.normSq (W i j) *
    ((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j)⁻¹
  have hi (i j : ι) : IntervalIntegrable (f i j) volume 0 1 :=
    (affineKernel_integrable _ _ (hZ.eigenvalues_pos i)
      (hZ.eigenvalues_pos j)).const_mul _
  have hs : IntervalIntegrable (∑ i, ∑ j, f i j) volume 0 1 :=
    IntervalIntegrable.sum Finset.univ (fun i _ =>
      IntervalIntegrable.sum Finset.univ (fun j _ => hi i j))
  apply hs.congr
  intro u hu
  have hm : matrixHS H = ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H) := rfl
  simp only [hm, Finset.sum_apply, f, W, U]
  exact (hs_pair_spectral Z H hZ u (Set.Ioc_subset_Icc_self
      (by simpa only [Set.uIoc_of_le zero_le_one] using hu))).symm

def energy (Z X : Matrix ι ι ℂ) (u : ℝ) : ℝ :=
  (Xᴴ * arithmetic Z X u).trace.re

private lemma inner_matrix (X Y : Matrix ι ι ℂ) :
    inner ℂ (matrixHS X) (matrixHS Y) = (Xᴴ * Y).trace :=
  hsInner_matrix X Y

lemma arithmetic_inverseMatrix (Z V : Matrix ι ι ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    arithmetic Z (inverseMatrix Z V u) u = V := by
  apply matrixHS.injective
  unfold arithmetic
  rw [← arithmetic_apply]
  simp only [inverseMatrix, LinearEquiv.apply_symm_apply]
  exact (hsArithmeticMap_isInvertible Z u hZ hu).self_apply_inverse _

lemma inverseMatrix_arithmetic (Z X : Matrix ι ι ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    inverseMatrix Z (arithmetic Z X u) u = X := by
  apply matrixHS.injective
  simp only [inverseMatrix, LinearEquiv.apply_symm_apply]
  unfold arithmetic
  rw [← arithmetic_apply]
  exact (hsArithmeticMap_isInvertible Z u hZ hu).inverse_apply_self _

lemma q_eq_trace (Z V : Matrix ι ι ℂ) (u : ℝ) :
    q Z V u = (Vᴴ * inverseMatrix Z V u).trace.re := by
  unfold q
  rw [← inner_matrix]
  simp [inverseMatrix]

lemma q_zero_parameter (Z V : Matrix ι ι ℂ) (hZ : Z.PosDef) :
    q Z V 0 = (Vᴴ * Z⁻¹ * V).trace.re := by
  have hi := inverseMatrix_arithmetic Z (Z⁻¹ * V) 0 hZ (by simp)
  simp only [arithmetic, sub_zero, one_smul, zero_smul, add_zero,
    Matrix.mul_nonsing_inv_cancel_left Z V ((Matrix.isUnit_iff_isUnit_det Z).mp hZ.isUnit)] at hi
  rw [q_eq_trace, hi, Matrix.mul_assoc]

private lemma arithmetic_positive (Z : Matrix ι ι ℂ) (u : ℝ)
    (hZ : Z.PosSemidef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (hsArithmeticMap Z u).IsPositive := by
  have hz : 0 ≤ Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) Z :=
    map_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) hZ.nonneg
  have hl := leftMulHS_nonneg hz
  have hr : 0 ≤ rightMulHS (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) Z) := by
    simpa using map_nonneg (rightMulHSStarAlgHom (ℋ := EuclideanSpace ℂ ι))
      (show 0 ≤ MulOpposite.op (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) Z) from hz)
  have hpl := (ContinuousLinearMap.nonneg_iff_isPositive.mp hl).smul_of_nonneg
    (show (0 : ℂ) ≤ ((1-u : ℝ) : ℂ) by exact_mod_cast (sub_nonneg.mpr hu.2))
  have hpr := (ContinuousLinearMap.nonneg_iff_isPositive.mp hr).smul_of_nonneg
    (show (0 : ℂ) ≤ (u : ℂ) by exact_mod_cast hu.1)
  simpa only [Complex.coe_smul, hsArithmeticMap] using hpl.add hpr

lemma energy_nonneg (Z X : Matrix ι ι ℂ) (u : ℝ)
    (hZ : Z.PosSemidef) (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ energy Z X u := by
  have h := (arithmetic_positive Z u hZ hu).re_inner_nonneg_right (matrixHS X)
  simpa only [arithmetic_apply, inner_matrix, energy, arithmetic, RCLike.re_to_complex] using h

lemma q_eq_energy_inverse (Z V : Matrix ι ι ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    q Z V u = energy Z (inverseMatrix Z V u) u := by
  rw [energy, arithmetic_inverseMatrix Z V u hZ hu, q_eq_trace]
  simpa only [inner_matrix, RCLike.re_to_complex] using
    (inner_re_symm (𝕜 := ℂ) (matrixHS V) (matrixHS (inverseMatrix Z V u)))

lemma q_nonneg (Z V : Matrix ι ι ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ q Z V u := by
  rw [q_eq_energy_inverse Z V u hZ hu]
  exact energy_nonneg _ _ _ hZ.posSemidef hu

/-- Weighted Cauchy--Schwarz for the native inverse, with no Hermitian
restriction on either direction. -/
lemma weighted_cauchy (Z X V : Matrix ι ι ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ((Xᴴ * V).trace.re)^2 ≤ energy Z X u * q Z V u := by
  letI := InnerProductSpace.rclikeToReal ℂ (HSOp (EuclideanSpace ℂ ι))
  let M := hsArithmeticMap Z u
  let B : LinearMap.BilinForm ℝ (HSOp (EuclideanSpace ℂ ι)) :=
    (innerₗ (HSOp (EuclideanSpace ℂ ι))).compl₂ (M.toLinearMap.restrictScalars ℝ)
  have hp := arithmetic_positive Z u hZ.posSemidef hu
  have hb (x : HSOp (EuclideanSpace ℂ ι)) : 0 ≤ B x x := by
    exact hp.re_inner_nonneg_right x
  have hs : LinearMap.IsSymm B := by
    constructor
    intro x y
    change inner ℝ x (M y) = inner ℝ y (M x)
    calc
      inner ℝ x (M y) = inner ℝ (M x) y :=
        (hp.toLinearMap.isSymmetric.restrictScalars x y).symm
      _ = inner ℝ y (M x) := real_inner_comm _ _
  have hh := B.apply_sq_le_of_symm hb hs (matrixHS X)
    (matrixHS (inverseMatrix Z V u))
  change (inner ℝ (matrixHS X) (M (matrixHS (inverseMatrix Z V u))))^2 ≤
    inner ℝ (matrixHS X) (M (matrixHS X)) *
      inner ℝ (matrixHS (inverseMatrix Z V u))
        (M (matrixHS (inverseMatrix Z V u))) at hh
  simp only [M, arithmetic_apply, arithmetic_inverseMatrix Z V u hZ hu,
    real_inner_eq_re_inner ℂ, inner_matrix, RCLike.re_to_complex] at hh
  rw [q_eq_energy_inverse Z V u hZ hu]
  change ((Xᴴ * arithmetic Z (inverseMatrix Z V u) u).trace.re)^2 ≤
    energy Z X u * energy Z (inverseMatrix Z V u) u at hh
  rw [arithmetic_inverseMatrix Z V u hZ hu] at hh
  exact hh

lemma q_sub_arithmetic (Z H X : Matrix ι ι ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    q Z (H - arithmetic Z X u) u = q Z H u -
      2 * (Xᴴ * H).trace.re + energy Z X u := by
  have hp := arithmetic_positive Z u hZ.posSemidef hu
  have hi := hsArithmeticMap_isInvertible Z u hZ hu
  unfold q
  simp only [map_sub, arithmetic, ← arithmetic_apply, hi.inverse_apply_self,
    inner_sub_left, inner_sub_right, Complex.sub_re]
  rw [hp.inner_left_eq_inner_right, hi.self_apply_inverse]
  have hcomm := inner_re_symm (𝕜 := ℂ) (matrixHS H) (matrixHS X)
  have hself := inner_re_symm (𝕜 := ℂ)
    (hsArithmeticMap Z u (matrixHS X)) (matrixHS X)
  simp only [RCLike.re_to_complex] at hcomm hself
  rw [hcomm, hself, arithmetic_apply, inner_matrix, inner_matrix]
  unfold energy arithmetic
  ring

end D5.S3.Quantum.Divergence.UmegakiConditionalKernel
