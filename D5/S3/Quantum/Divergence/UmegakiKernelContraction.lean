/- GID: D5/S3/Quantum/Divergence/UmegakiKernelContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiKernelContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform endpoint contraction implies contraction of the arithmetic inverse forms. -/

import D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
import D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-! The endpoint bound yields the original universal positive trace test.
The simultaneous residual Gram bounds then give two weighted Cauchy–Schwarz
inequalities for the same output inverse direction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Divergence.UniversalPositiveScalarizer

section ArithmeticCoordinates
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
end ArithmeticCoordinates

section ReferenceChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Divergence.CanonicalChannelDPI

namespace D5.S3.Quantum.Divergence.UmegakiReferenceTransport
universe u
variable {a b R : Type u} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype R] [DecidableEq R]

lemma partialTraceRight_posDef [Nonempty a]
    (Z : Matrix (R × a) (R × a) ℂ) (hZ : Z.PosDef) :
    (partialTraceRight Z).PosDef := by
  have he : partialTraceRight Z =
      ∑ i : a, Z.submatrix (fun r => (r,i)) (fun r => (r,i)) := by
    ext r s
    simp [partialTraceRight, Matrix.sum_apply]
  rw [he]
  exact Matrix.posDef_sum Finset.univ_nonempty (fun i _ =>
    hZ.submatrix (fun r s h => (Prod.mk.inj h).1))

lemma partialTraceRight_mul_embed (Z : Matrix (R × a) (R × a) ℂ)
    (X : Matrix R R ℂ) :
    partialTraceRight (Z * (X ⊗ₖ (1 : Matrix a a ℂ))) = partialTraceRight Z * X := by
  ext r s
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

lemma partialTraceRight_embed_mul (Z : Matrix (R × a) (R × a) ℂ)
    (X : Matrix R R ℂ) :
    partialTraceRight ((X ⊗ₖ (1 : Matrix a a ℂ)) * Z) = X * partialTraceRight Z := by
  ext r s
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- Ordinary complex trace adjunction for the partial trace. -/
lemma trace_embed_pair (X : Matrix R R ℂ) (V : Matrix (R × a) (R × a) ℂ) :
    ((X ⊗ₖ (1 : Matrix a a ℂ))ᴴ * V).trace = (Xᴴ * partialTraceRight V).trace := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← trace_partialTraceRight, partialTraceRight_embed_mul]

lemma amp_kronecker (N : QuantumChannel a b) (X : Matrix R R ℂ)
    (Z : Matrix a a ℂ) : amp N (X ⊗ₖ Z) = X ⊗ₖ act N Z := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry]
  change (N.toCompletelyPositiveMap ((X r s) • CStarMatrix.ofMatrix Z)) i j = _
  rw [map_smul]
  rfl

lemma amp_mono (N : QuantumChannel a b)
    {X Z : Matrix (R × a) (R × a) ℂ} (h : X ≤ Z) : amp N X ≤ amp N Z := by
  have hp := referenceAction_nonneg N (CStarMatrix.ofMatrix (Z-X))
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (sub_nonneg.mpr h))
  have hn := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hp
  change 0 ≤ amp N (Z-X) at hn
  have he : amp N (Z-X) = amp N Z - amp N X := by
    exact (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      ((referenceLinear N).comp CStarMatrix.ofMatrixₗ.toLinearMap)).map_sub Z X
  rw [he] at hn
  exact sub_nonneg.mp hn

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
lemma positive_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : Matrix ι ι ℂ) (hZ : Z.PosDef) :
    ∃ m : ℝ, 0 < m ∧ m • (1 : Matrix ι ι ℂ) ≤ Z := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, zero_lt_one, le_of_eq (Subsingleton.elim _ _)⟩
  | inr h =>
    obtain ⟨m,hm,hfloor⟩ := (CFC.exists_pos_algebraMap_le_iff Z).mpr
      (fun x hx => hZ.isStrictlyPositive.spectrum_pos hx)
    exact ⟨m,hm,by simpa only [Algebra.algebraMap_eq_smul_one] using hfloor⟩

set_option maxHeartbeats 1200000 in
/-- Positivity of the channel image of the identity gives strict positivity
on every correlated positive-definite reference input. -/
lemma amp_posDef (N : QuantumChannel a b) (hN : (act N 1).PosDef)
    (Z : Matrix (R × a) (R × a) ℂ) (hZ : Z.PosDef) : (amp N Z).PosDef := by
  obtain ⟨m,hm,hfloor⟩ := positive_floor Z hZ
  have hmon : amp N (m • (1 : Matrix (R × a) (R × a) ℂ)) ≤ amp N Z :=
    amp_mono N hfloor
  have he : amp N (m • (1 : Matrix (R × a) (R × a) ℂ)) =
      m • ((1 : Matrix R R ℂ) ⊗ₖ act N 1) := by
    rw [amp_smul, ← Matrix.one_kronecker_one, amp_kronecker]
  rw [he] at hmon
  have hp : ((1 : Matrix R R ℂ) ⊗ₖ act N 1).PosDef :=
    (Matrix.PosDef.one (n := R)).kronecker hN
  exact ((hp.isStrictlyPositive.smul hm).of_le hmon).posDef

lemma amp_mul_embed (N : QuantumChannel a b)
    (Z : Matrix (R × a) (R × a) ℂ) (X : Matrix R R ℂ) :
    amp N (Z * (X ⊗ₖ (1 : Matrix a a ℂ))) = amp N Z * (X ⊗ₖ (1 : Matrix b b ℂ)) := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry]
  have h (p q : a) : (Z * (X ⊗ₖ (1 : Matrix a a ℂ))) (r,p) (s,q) =
      ∑ t, Z (r,p) (t,q) * X t s := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
      mul_ite, mul_assoc]
  have hblock : (fun p q => (Z * (X ⊗ₖ (1 : Matrix a a ℂ))) (r,p) (s,q)) =
      ∑ t, X t s • (fun p q => Z (r,p) (t,q)) := by
    ext p q
    simp [h, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]
  rw [hblock]
  let L : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (N.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
  change L (∑ t, X t s • (fun p q => Z (r,p) (t,q))) i j = _
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp [show ∀ Q, L Q = act N Q from fun _ => rfl, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, mul_assoc, amp_entry, mul_comm]

lemma amp_embed_mul (N : QuantumChannel a b)
    (Z : Matrix (R × a) (R × a) ℂ) (X : Matrix R R ℂ) :
    amp N ((X ⊗ₖ (1 : Matrix a a ℂ)) * Z) = (X ⊗ₖ (1 : Matrix b b ℂ)) * amp N Z := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry]
  have h (p q : a) : ((X ⊗ₖ (1 : Matrix a a ℂ)) * Z) (r,p) (s,q) =
      ∑ t, X r t * Z (t,p) (s,q) := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
      ite_mul, mul_ite]
  have hblock : (fun p q => ((X ⊗ₖ (1 : Matrix a a ℂ)) * Z) (r,p) (s,q)) =
      ∑ t, X r t • (fun p q => Z (t,p) (s,q)) := by
    ext p q
    simp [h, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hblock]
  let L : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (N.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
  change L (∑ t, X r t • (fun p q => Z (t,p) (s,q))) i j = _
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp [show ∀ Q, L Q = act N Q from fun _ => rfl, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, ite_mul, mul_ite, amp_entry]


section Adjoint
variable [Nonempty a] [Nonempty b]

private lemma Phi_trace_pair (N : QuantumChannel a b) (Y : Matrix b b ℂ)
    (Z : Matrix a a ℂ) : (Phi N Y * Z).trace = (Y * act N Z).trace := by
  rw [Matrix.trace_mul_comm (Phi N Y) Z, Matrix.trace_mul_comm Y (act N Z)]
  exact actual_kraus_trace_pair N Z Y

/-- The normalized canonical Kraus adjoint pairs with the actual channel
action on every complex joint matrix and every finite quantum reference. -/
lemma PhiR_trace_pair (N : QuantumChannel a b)
    (Y : Matrix (R × b) (R × b) ℂ) (Z : Matrix (R × a) (R × a) ℂ) :
    (PhiR N Y * Z).trace = (Y * amp N Z).trace := by
  change (∑ p, ∑ q, PhiR N Y p q * Z q p) =
    ∑ p, ∑ q, Y p q * amp N Z q p
  simp only [Fintype.sum_prod_type]
  calc
    (∑ r, ∑ x, ∑ s, ∑ y, PhiR N Y (r,x) (s,y) * Z (s,y) (r,x)) =
        ∑ r, ∑ s, (Phi N (Y.submatrix (fun i => (r,i)) (fun j => (s,j))) *
          Z.submatrix (fun i => (s,i)) (fun j => (r,j))).trace := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      rfl
    _ = ∑ r, ∑ s, ((Y.submatrix (fun i => (r,i)) (fun j => (s,j))) *
        act N (Z.submatrix (fun i => (s,i)) (fun j => (r,j)))).trace := by
      simp_rw [Phi_trace_pair]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      rfl

lemma PhiR_hs_pair (N : QuantumChannel a b)
    (Y : Matrix (R × b) (R × b) ℂ) (Z : Matrix (R × a) (R × a) ℂ) :
    ((PhiR N Y)ᴴ * Z).trace = (Yᴴ * amp N Z).trace := by
  rw [← PhiR_star, PhiR_trace_pair]


end Adjoint
end D5.S3.Quantum.Divergence.UmegakiReferenceTransport
end ReferenceChannel

open D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport

namespace D5.S3.Quantum.Divergence.UmegakiKernelContraction

universe u
variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Uniform left-endpoint bound on every complex direction in the
partial-trace kernel, with every finite quantum reference and correlated base. -/
def EndpointBound (N : QuantumChannel a b) (c : ℝ) : Prop :=
  ∀ {R : Type u} [Fintype R] [DecidableEq R]
    (Z V : Matrix (R × a) (R × a) ℂ), Z.PosDef → partialTraceRight V = 0 →
    q (amp N Z) (amp N V) 0 ≤ c * q Z V 0

private lemma energy_grams {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z Y : Matrix ι ι ℂ) (u : ℝ) :
    energy Z Y u = (1-u) * (Z * (Y * Yᴴ)).trace.re +
      u * (Z * (Yᴴ * Y)).trace.re := by
  simp only [energy, arithmetic, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [← Matrix.mul_assoc Yᴴ Z Y, Matrix.trace_mul_cycle Yᴴ Z Y,
    Matrix.trace_mul_comm (Y * Yᴴ) Z, ← Matrix.mul_assoc Yᴴ Y Z,
    Matrix.trace_mul_comm (Yᴴ * Y) Z]

private lemma trace_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Z D : Matrix ι ι ℂ} (hZ : Z.PosSemidef) (hD : D.PosSemidef) :
    0 ≤ (Z * D).trace.re :=
  RHLinalg.trace_mul_nonneg_of_posSemidef hZ hD

private lemma trace_sub_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z D G : Matrix ι ι ℂ) (k : ℝ) :
    (Z * ((k : ℂ) • D - G)).trace.re =
      k * (Z * D).trace.re - (Z * G).trace.re := by
  simp [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.mul_re]

section Local
variable [Nonempty a] [Nonempty b]
variable {R : Type u} [Fintype R] [DecidableEq R]

private lemma energy_defects (N : QuantumChannel a b)
    (Z : Matrix (R × a) (R × a) ℂ) (Y : Matrix (R × b) (R × b) ℂ) (u : ℝ) :
    energy (amp N Z) Y u - energy Z (PhiR N Y) u =
      (1-u) * (Z * defectR N Y).trace.re + u * (Z * defectR N Yᴴ).trace.re := by
  rw [energy_grams, energy_grams]
  simp only [defectR, PhiR_star, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.trace_sub, Complex.sub_re]
  rw [Matrix.trace_mul_comm Z (PhiR N _), PhiR_trace_pair,
    Matrix.trace_mul_comm (Y * Yᴴ) (amp N Z),
    Matrix.trace_mul_comm Z (PhiR N _), PhiR_trace_pair,
    Matrix.trace_mul_comm (Yᴴ * Y) (amp N Z)]
  ring

private lemma centered_pair (N : QuantumChannel a b)
    (Y : Matrix (R × b) (R × b) ℂ) (V : Matrix (R × a) (R × a) ℂ)
    (X : Matrix R R ℂ) (hV : partialTraceRight V = 0) :
    (((Y - X ⊗ₖ (1 : Matrix b b ℂ))ᴴ) * amp N V).trace =
      (((PhiR N Y - X ⊗ₖ (1 : Matrix a a ℂ))ᴴ) * V).trace := by
  have hOut : partialTraceRight (amp N V) = 0 := (ptr_amp N V).trans hV
  simp [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub,
    trace_embed_pair, hV, hOut, PhiR_hs_pair]

private lemma energy_zero_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z Y W : Matrix ι ι ℂ) (hZ : Z.IsHermitian) :
    energy Z (Y - W) 0 =
      energy Z Y 0 + energy Z W 0 - 2 * (Yᴴ * (Z * W)).trace.re := by
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (Yᴴ * (Z * W)))
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hZ.eq,
    Matrix.trace_conjTranspose, map_star, Complex.star_def, Complex.conj_re] at h
  simp only [energy, arithmetic, sub_zero, one_smul, zero_smul, add_zero,
    Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
    Complex.sub_re]
  rw [← Matrix.mul_assoc Wᴴ Z Y, h]
  ring

private lemma endpoint_trace_test (N : QuantumChannel a b) (c : ℝ)
    (hN : (act N 1).PosDef) (hc : 0 ≤ c) (hc1 : c < 1)
    (hEnd : EndpointBound N c) : UniversalPositiveTraceTest N (c / (1-c)) := by
  intro R _ _ Y Z hZ
  let S := partialTraceRight Z
  let F := PhiR N Y
  let X := S⁻¹ * partialTraceRight (Z * F)
  let Wa := X ⊗ₖ (1 : Matrix a a ℂ)
  let Wb := X ⊗ₖ (1 : Matrix b b ℂ)
  let K := F - Wa
  let G := Y - Wb
  let V := Z * K
  let a₀ := energy Z K 0
  let d := (Z * defectR N Y).trace.re
  let k := c / (1-c)
  have hu : (0 : ℝ) ∈ Set.Icc 0 1 := by simp
  have hTZ := amp_posDef N hN Z hZ
  have hs : S.PosDef := partialTraceRight_posDef Z hZ
  have hV : partialTraceRight V = 0 := by
    change partialTraceRight (Z * (F - Wa)) = 0
    rw [Matrix.mul_sub, show partialTraceRight (Z * F - Z * Wa) =
        partialTraceRight (Z * F) - partialTraceRight (Z * Wa) by
      simpa only [ptr, one_smul] using ptr_sub_smul 1 (Z * F) (Z * Wa),
      partialTraceRight_mul_embed, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hs.isUnit), Matrix.one_mul, sub_self]
  have hq : q Z V 0 = a₀ := by
    rw [q_zero_parameter Z V hZ, Matrix.mul_assoc]
    change ((Z*K)ᴴ * (Z⁻¹ * (Z*K))).trace.re = energy Z K 0
    simp only [Matrix.nonsing_inv_mul_cancel_left Z K ((Matrix.isUnit_iff_isUnit_det Z).mp hZ.isUnit),
      energy, arithmetic, sub_zero, one_smul, zero_smul, add_zero]
    rw [Matrix.conjTranspose_mul, hZ.isHermitian.eq, Matrix.mul_assoc]
  have hpair : (Gᴴ * amp N V).trace.re = a₀ := by
    rw [centered_pair N Y V X hV]
    change (Kᴴ * (Z*K)).trace.re = energy Z K 0
    simp only [energy, arithmetic, sub_zero, one_smul, zero_smul, add_zero]
  have hshift : energy (amp N Z) Wb 0 = energy Z Wa 0 := by
    simp only [energy, arithmetic, sub_zero, one_smul, zero_smul, add_zero, Wb, Wa,
      trace_embed_pair, partialTraceRight_mul_embed]
    rw [show partialTraceRight (amp N Z) = S from ptr_amp N Z]
  have hcross : (Yᴴ * (amp N Z * Wb)).trace = (Fᴴ * (Z * Wa)).trace := by
    rw [PhiR_hs_pair, amp_mul_embed]
  have he : energy (amp N Z) G 0 = a₀ + d := by
    have hd := energy_defects N Z Y 0
    simp only [sub_zero, one_mul, zero_mul, add_zero] at hd
    change energy (amp N Z) (Y-Wb) 0 = energy Z (F-Wa) 0 + d
    rw [energy_zero_sub _ Y Wb hTZ.isHermitian, energy_zero_sub _ F Wa hZ.isHermitian]
    linarith only [hd, hshift, congrArg Complex.re hcross]
  have ha : 0 ≤ a₀ := energy_nonneg _ _ _ hZ.posSemidef hu
  have hd : 0 ≤ d := trace_nonneg hZ.posSemidef (defectR_posSemidef N Y)
  have hk : 0 ≤ k := div_nonneg hc (sub_pos.mpr hc1).le
  have hcs := weighted_cauchy (amp N Z) G (amp N V) 0 hTZ hu
  rw [hpair, he] at hcs
  have hEnd' := hEnd Z V hZ hV
  rw [hq] at hEnd'
  have hsquare : a₀ ^ 2 ≤ (a₀ + d) * (c * a₀) :=
    hcs.trans (mul_le_mul_of_nonneg_left hEnd' (add_nonneg ha hd))
  have hab : a₀ ≤ k * d := by
    rcases ha.eq_or_lt with hz | hp
    · rw [← hz]
      exact mul_nonneg hk hd
    · have hcancel : a₀ ≤ (a₀ + d) * c := by
        apply le_of_mul_le_mul_right _ hp
        nlinarith only [hsquare]
      rw [show k * d = (c*d) / (1-c) by dsimp [k]; ring]
      apply (le_div_iff₀ (sub_pos.mpr hc1)).2
      nlinarith only [hcancel]
  let f := fun W : Matrix R R ℂ =>
    (Z * ((F - W ⊗ₖ (1 : Matrix a a ℂ)) *
      (F - W ⊗ₖ (1 : Matrix a a ℂ))ᴴ)).trace.re
  have hbelow : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact trace_nonneg hZ.posSemidef (Matrix.posSemidef_self_mul_conjTranspose _)
  have hcost : f X = a₀ := by
    change f X = energy Z K 0
    rw [energy_grams Z K 0]
    simp [f, K, Wa]
  change sInf (Set.range f) ≤ (Z * ((k : ℂ) • defectR N Y)).trace.re
  calc
    _ ≤ f X := csInf_le hbelow (Set.mem_range_self X)
    _ = a₀ := hcost
    _ ≤ k * d := hab
    _ = _ := by simp [d, Matrix.mul_smul, Matrix.trace_smul, Complex.mul_re]

/-- For every arithmetic parameter, the common-center residual and the
uncentered adjoint give simultaneous estimates of the output inverse form. -/
theorem kernel_contraction (N : QuantumChannel a b) (c : ℝ)
    (hN : (act N 1).PosDef) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hEnd : EndpointBound N c)
    (Z V : Matrix (R × a) (R × a) ℂ) (u : ℝ) (hZ : Z.PosDef)
    (hV : partialTraceRight V = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    q (amp N Z) (amp N V) u ≤ c * q Z V u := by
  let U := amp N V
  let T := amp N Z
  let Y := inverseMatrix T U u
  let F := PhiR N Y
  let p := q Z V u
  let q₀ := q T U u
  let f := energy Z F u
  let d := energy T Y u - f
  have hT : T.PosDef := amp_posDef N hN Z hZ
  have hp : 0 ≤ p := q_nonneg _ _ _ hZ hu
  have hq : 0 ≤ q₀ := q_nonneg _ _ _ hT hu
  have he : energy T Y u = q₀ := (q_eq_energy_inverse T U u hT hu).symm
  have hpair : (Yᴴ * U).trace.re = q₀ := by
    rw [← he, energy, arithmetic_inverseMatrix T U u hT hu]
  have hpairF : (Fᴴ * V).trace.re = q₀ := by
    rw [PhiR_hs_pair, hpair]
  have hcsF := weighted_cauchy Z F V u hZ hu
  rw [hpairF] at hcsF
  change q₀ ^ 2 ≤ f * p at hcsF
  have hd : 0 ≤ d := by
    change 0 ≤ energy T Y u - energy Z (PhiR N Y) u
    rw [energy_defects]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hu.2) (trace_nonneg hZ.posSemidef (defectR_posSemidef N Y)))
      (mul_nonneg hu.1 (trace_nonneg hZ.posSemidef (defectR_posSemidef N Yᴴ)))
  change q₀ ≤ c * p
  rcases hq.eq_or_lt with hz | hq'
  · rw [← hz]
    exact mul_nonneg hc.1 hp
  rcases hc.2.eq_or_lt with hc1 | hc1
  · rw [hc1, one_mul]
    have hf : f ≤ q₀ := by simpa only [d, he, sub_nonneg] using hd
    apply le_of_mul_le_mul_left _ hq'
    simpa only [pow_two] using hcsF.trans (mul_le_mul_of_nonneg_right hf hp)
  let k := c / (1-c)
  have hk : 0 ≤ k := div_nonneg hc.1 (sub_pos.mpr hc1).le
  obtain ⟨σ,hσ⟩ := common_positive_state_scalarizer N k hk
    (endpoint_trace_test N c hN hc.1 hc1 hEnd)
  let X := stateCenter σ Y
  let Δ := F - X ⊗ₖ (1 : Matrix a a ℂ)
  have hpairΔ : (Δᴴ * V).trace.re = q₀ := by
    rw [← centered_pair N Y V X hV]
    change (((Y - X ⊗ₖ (1 : Matrix b b ℂ))ᴴ) * U).trace.re = _
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, trace_embed_pair,
      show partialTraceRight U = 0 from (ptr_amp N V).trans hV, Matrix.mul_zero,
      Matrix.trace_zero, sub_zero, hpair]
  obtain ⟨_,hl,hr⟩ := hσ Y
  have hl' := trace_nonneg hZ.posSemidef hl
  have hr' := trace_nonneg hZ.posSemidef hr
  change 0 ≤ (Z * ((k : ℂ) • defectR N Y - Δ * Δᴴ)).trace.re at hl'
  change 0 ≤ (Z * ((k : ℂ) • (PhiR N (Yᴴ * Y) - Fᴴ * F) - Δᴴ * Δ)).trace.re at hr'
  have hright : PhiR N (Yᴴ * Y) - Fᴴ * F = defectR N Yᴴ := by
    simp [defectR, PhiR_star, F]
  rw [hright, trace_sub_gram] at hr'
  rw [trace_sub_gram] at hl'
  have hE : energy Z Δ u ≤ k * d := by
    rw [energy_grams]
    change _ ≤ k * (energy T Y u - energy Z (PhiR N Y) u)
    rw [energy_defects]
    have hL := mul_nonneg (sub_nonneg.mpr hu.2) hl'
    have hR := mul_nonneg hu.1 hr'
    nlinarith only [hL, hR]
  have hcsΔ := weighted_cauchy Z Δ V u hZ hu
  rw [hpairΔ] at hcsΔ
  have hcs' : q₀^2 ≤ (k*d)*p := hcsΔ.trans (mul_le_mul_of_nonneg_right hE hp)
  have hd' : d = q₀ - f := by rw [show d = energy T Y u - f from rfl, he]
  have hdP : d * p ≤ q₀ * p - q₀^2 := by rw [hd']; linarith only [hcsF]
  have hcombine := hcs'.trans (show (k*d)*p ≤ k * (q₀*p - q₀^2) by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hdP hk)
  have hscaled : (1+k)*q₀ ≤ k*p := by
    apply le_of_mul_le_mul_right _ hq'
    nlinarith only [hcombine]
  have hkEq : (1+k)*c = k := by
    dsimp [k]
    field_simp [ne_of_gt (sub_pos.mpr hc1)]
    ring
  apply le_of_mul_le_mul_left _ (show 0 < 1+k by linarith)
  rwa [← mul_assoc, hkEq]

end Local
end D5.S3.Quantum.Divergence.UmegakiKernelContraction
