/- GID: D5/S3/Quantum/Divergence/UmegakiArithmeticBKM
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiArithmeticBKM
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native Hilbert-Schmidt arithmetic inverse and Bochner logarithmic derivative. -/

import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
import D5.S3.Quantum.Lieb.HilbertSchmidtOperatorSpace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Trace

/-! The spectral reciprocal candidate certifies the native arithmetic inverse,
including both endpoints, before it is paired against an arbitrary complex
direction. Finite trace expansions and integrable scalar kernels identify the
result with the actual matrix-valued Bochner logarithmic derivative.
proof_shape: content; admission_basis: escape-witness.
escape_witness: schurInverse_left and affineKernel_eq_pair, consumed by
arithmetic_inverse_pairing_eq_logDeriv. The scalar kernel evaluation and spectral
trace expansion are reused from their original rare-flag declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix MeasureTheory
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open HilbertSchmidtOperatorSpace D5.S3.Divergence.LogDerivTrace

namespace D5.S3.Quantum.Divergence.UmegakiArithmeticBKM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The arithmetic interpolation of native left and right multiplication. -/
def hsArithmeticMap (Z : Matrix ι ι ℂ) (u : ℝ) :
    HSOp (EuclideanSpace ℂ ι) →L[ℂ] HSOp (EuclideanSpace ℂ ι) :=
  (1 - u) • leftMulHS ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) Z) +
    u • rightMulHS ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) Z)

private lemma affine_pos (a b u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 < (1-u)*a + u*b := by
  by_cases h : u = 1
  · subst u; simpa using hb
  · have hp : 0 < 1-u := sub_pos.mpr (lt_of_le_of_ne hu.2 h)
    exact add_pos_of_pos_of_nonneg (mul_pos hp ha) (mul_nonneg hu.1 hb.le)

def matrixHS : Matrix ι ι ℂ ≃ₗ[ℂ] HSOp (EuclideanSpace ℂ ι) :=
  Matrix.toEuclideanLin.trans hsLinearMapEquiv.symm

lemma arithmetic_apply (Z X : Matrix ι ι ℂ) (u : ℝ) :
    hsArithmeticMap Z u (matrixHS X) =
      matrixHS ((1-u) • (Z * X) + u • (X * Z)) := by
  apply hsLinearMapEquiv.injective
  change ((1-u) • (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) Z) *
      ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) X)) +
    u • (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) X) *
      ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) Z))).toLinearMap = _
  simp only [matrixHS, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    ← map_mul, ← Complex.coe_smul, ← map_smul, ← map_add]
  rfl

private def conjugate (U : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  (mulRightLinearMap ι ℂ Uᴴ).comp (mulLeftLinearMap ι ℂ U)

private def entryScale (D : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun X i j := D i j * X i j
  map_add' X Y := by ext i j; simp [mul_add]
  map_smul' c X := by ext i j; simp [mul_left_comm, mul_assoc]

private def schurInverse (Z : Matrix ι ι ℂ) (hZ : Z.PosDef) (u : ℝ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  let U : Matrix ι ι ℂ := hZ.isHermitian.eigenvectorUnitary
  (conjugate U).comp ((entryScale (fun i j =>
    (((1-u)*hZ.isHermitian.eigenvalues i + u*hZ.isHermitian.eigenvalues j : ℝ) : ℂ)⁻¹)).comp
      (conjugate Uᴴ))

private lemma schurInverse_apply (Z X : Matrix ι ι ℂ) (hZ : Z.PosDef) (u : ℝ) :
    schurInverse Z hZ u X =
      let U : Matrix ι ι ℂ := hZ.isHermitian.eigenvectorUnitary
      U * (entryScale (fun i j =>
        (((1-u)*hZ.isHermitian.eigenvalues i + u*hZ.isHermitian.eigenvalues j : ℝ) : ℂ)⁻¹)
          (Uᴴ * X * U)) * Uᴴ := by
  simp [schurInverse, conjugate]

private lemma schurInverse_left (Z X : Matrix ι ι ℂ) (hZ : Z.PosDef) (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1-u) • (Z * schurInverse Z hZ u X) +
      u • (schurInverse Z hZ u X * Z) = X := by
  let U : Matrix ι ι ℂ := hZ.isHermitian.eigenvectorUnitary
  let d : ι → ℂ := fun i => (hZ.isHermitian.eigenvalues i : ℂ)
  let W : Matrix ι ι ℂ := Uᴴ * X * U
  let Y : Matrix ι ι ℂ := entryScale (fun i j =>
    (((1-u)*hZ.isHermitian.eigenvalues i + u*hZ.isHermitian.eigenvalues j : ℝ) : ℂ)⁻¹) W
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hz : Z = U * Matrix.diagonal d * Uᴴ := by
    simpa [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def,
      Matrix.star_eq_conjTranspose] using hZ.isHermitian.spectral_theorem
  have hschur : schurInverse Z hZ u X = U * Y * Uᴴ := schurInverse_apply Z X hZ u
  have hleft : Z * schurInverse Z hZ u X = U * (Matrix.diagonal d * Y) * Uᴴ := by
    rw [hschur, hz]
    calc
      (U * Matrix.diagonal d * Uᴴ) * (U * Y * Uᴴ) =
          U * Matrix.diagonal d * (Uᴴ * U) * Y * Uᴴ := by noncomm_ring
      _ = _ := by rw [hU]; simp [Matrix.mul_assoc]
  have hright : schurInverse Z hZ u X * Z = U * (Y * Matrix.diagonal d) * Uᴴ := by
    rw [hschur, hz]
    calc
      (U * Y * Uᴴ) * (U * Matrix.diagonal d * Uᴴ) =
          U * Y * (Uᴴ * U) * Matrix.diagonal d * Uᴴ := by noncomm_ring
      _ = _ := by rw [hU]; simp [Matrix.mul_assoc]
  rw [hleft, hright]
  have hy : (1-u) • (Matrix.diagonal d * Y) + u • (Y * Matrix.diagonal d) = W := by
    ext i j
    have hn : (((1-u)*hZ.isHermitian.eigenvalues i +
      u*hZ.isHermitian.eigenvalues j : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (affine_pos _ _ _ (hZ.eigenvalues_pos i) (hZ.eigenvalues_pos j) hu).ne'
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    dsimp [d, Y, entryScale]
    change ((1-u : ℝ) : ℂ) * ((hZ.isHermitian.eigenvalues i : ℂ) *
        ((((1-u)*hZ.isHermitian.eigenvalues i + u*hZ.isHermitian.eigenvalues j : ℝ) : ℂ)⁻¹ * W i j)) +
      (u : ℂ) * ((((1-u)*hZ.isHermitian.eigenvalues i + u*hZ.isHermitian.eigenvalues j : ℝ) : ℂ)⁻¹ *
        W i j * (hZ.isHermitian.eigenvalues j : ℂ)) = W i j
    push_cast at hn ⊢
    field_simp [hn]
    <;> ring
  calc
    (1-u) • (U * (Matrix.diagonal d * Y) * Uᴴ) +
        u • (U * (Y * Matrix.diagonal d) * Uᴴ) =
        U * ((1-u) • (Matrix.diagonal d * Y) + u • (Y * Matrix.diagonal d)) * Uᴴ := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = U * W * Uᴴ := by rw [hy]
    _ = (U * Uᴴ) * X * (U * Uᴴ) := by dsimp [W]; noncomm_ring
    _ = X := by rw [hU']; simp

private def inverseCandidate (Z : Matrix ι ι ℂ) (hZ : Z.PosDef) (u : ℝ) :
    HSOp (EuclideanSpace ℂ ι) →L[ℂ] HSOp (EuclideanSpace ℂ ι) :=
  (matrixHS.toLinearMap.comp ((schurInverse Z hZ u).comp
    matrixHS.symm.toLinearMap)).toContinuousLinearMap

private lemma inverseCandidate_left (Z : Matrix ι ι ℂ) (hZ : Z.PosDef) (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (hsArithmeticMap Z u).comp (inverseCandidate Z hZ u) = .id ℂ _ := by
  ext T
  obtain ⟨X, rfl⟩ := matrixHS.surjective T
  change hsArithmeticMap Z u (matrixHS (schurInverse Z hZ u (matrixHS.symm (matrixHS X)))) = _
  rw [matrixHS.symm_apply_apply, arithmetic_apply, schurInverse_left Z X hZ u hu]
  rfl

lemma hsArithmeticMap_isInvertible (Z : Matrix ι ι ℂ) (u : ℝ) (hZ : Z.PosDef)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (hsArithmeticMap Z u).IsInvertible := by
  let M := hsArithmeticMap Z u
  let Q := inverseCandidate Z hZ u
  have hleft : M.comp Q = .id ℂ _ := by
    simpa [M, Q] using inverseCandidate_left Z hZ u hu
  have hsurj : Function.Surjective M := by
    intro y
    refine ⟨Q y, ?_⟩
    have h := congrArg (fun F : HSOp (EuclideanSpace ℂ ι) →L[ℂ]
        HSOp (EuclideanSpace ℂ ι) => F y) hleft
    simpa [ContinuousLinearMap.comp_apply] using h
  have hsurj' : Function.Surjective M.toLinearMap := by
    simpa using hsurj
  have hinj' : Function.Injective M.toLinearMap :=
    (LinearMap.injective_iff_surjective).2 hsurj'
  let e : HSOp (EuclideanSpace ℂ ι) ≃ₗ[ℂ] HSOp (EuclideanSpace ℂ ι) :=
    LinearEquiv.ofBijective M.toLinearMap ⟨hinj', hsurj'⟩
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  ext x
  rfl

private lemma hsArithmeticMap_inverse_apply (Z X : Matrix ι ι ℂ) (u : ℝ) (hZ : Z.PosDef)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (hsArithmeticMap Z u).inverse (matrixHS X) =
      matrixHS (schurInverse Z hZ u X) := by
  let M := hsArithmeticMap Z u
  let Q := inverseCandidate Z hZ u
  have hM : M.IsInvertible := by
    simpa [M] using hsArithmeticMap_isInvertible Z u hZ hu
  apply (hM.inverse_apply_eq).2
  have hleft : M.comp Q = .id ℂ _ := by
    simpa [M, Q] using inverseCandidate_left Z hZ u hu
  have h := congrArg (fun F : HSOp (EuclideanSpace ℂ ι) →L[ℂ]
      HSOp (EuclideanSpace ℂ ι) => F (matrixHS X)) hleft
  simpa [M, Q, inverseCandidate, ContinuousLinearMap.comp_apply] using h.symm

private lemma affineKernel_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => ((1-u)*a+u*b)⁻¹) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simp only [Set.uIcc_of_le zero_le_one]
  exact (by fun_prop : ContinuousOn (fun u : ℝ => (1-u)*a+u*b) (Set.Icc 0 1)).inv₀
    (fun u hu => (affine_pos a b u ha hb hu).ne')

private lemma affineKernel_eq_pair (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ u in (0 : ℝ)..1, ((1-u)*a+u*b)⁻¹) =
      ∫ t in Set.Ioi (0 : ℝ), 1 / ((a+t)*(b+t)) := by
  rw [UmegakiRareFlagBKM.pair_kernel_eval a b ha hb]
  by_cases hab : a = b
  · subst b
    simp only [if_pos rfl]
    have hf : (fun u : ℝ => ((1-u)*a+u*a)⁻¹) = fun _ => a⁻¹ := by
      funext u
      congr 1
      ring
    rw [hf]
    simp [one_div]
  · rw [if_neg hab]
    have hf : (fun u : ℝ => ((1-u)*a+u*b)⁻¹) = fun u => ((b-a)*u+a)⁻¹ := by
      funext u
      congr 1
      ring
    rw [hf, intervalIntegral.integral_comp_mul_add
      (fun x : ℝ => x⁻¹) (sub_ne_zero.mpr (Ne.symm hab)) a]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    rw [integral_inv_of_pos ha hb, Real.log_div hb.ne' ha.ne']
    simp only [smul_eq_mul]
    field_simp
    ring

lemma hsInner_matrix (X Y : Matrix ι ι ℂ) :
    inner ℂ (ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) X))
      (matrixHS Y) = (Xᴴ * Y).trace := by
  change inner ℂ (ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) X))
      (ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) Y)) = _
  rw [hsInner_eq_trace]
  have htrace (A : Matrix ι ι ℂ) :
      LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).toLinearMap) = A.trace := by
    change LinearMap.trace ℂ _ (Matrix.toEuclideanLin A) = _
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
  rw [← map_star, ← map_mul]
  change LinearMap.trace ℂ _
      ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Xᴴ * Y)).toLinearMap) = _
  exact htrace (Xᴴ * Y)

private lemma trace_hadjoint_resolvent (Z H : Matrix ι ι ℂ) (hZ : Z.PosDef)
    (t : ℝ) (ht : 0 ≤ t) :
    (Hᴴ * (Z + t • 1)⁻¹ * H * (Z + t • 1)⁻¹).trace =
      ∑ i, ∑ j,
        ((Complex.normSq (((hZ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * H *
          (hZ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) i j) *
          ((hZ.isHermitian.eigenvalues i + t)⁻¹ *
            (hZ.isHermitian.eigenvalues j + t)⁻¹) : ℝ) : ℂ) := by
  let U : Matrix ι ι ℂ := hZ.isHermitian.eigenvectorUnitary
  let R : Matrix ι ι ℂ := U * Matrix.diagonal
    (fun i => ((hZ.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) * Uᴴ
  have hres : (Z + t • 1)⁻¹ = R := by
    rw [resolvent_eq_spectral Z hZ t ht]
    rfl
  rw [hres]
  have h := UmegakiRareFlagBKM.trace_cross_spectral H U U
    (fun i => ((hZ.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹)
    (fun j => ((hZ.isHermitian.eigenvalues j + t : ℝ) : ℂ)⁻¹)
  have hcyc : (Hᴴ * R * H * R).trace = (H * R * Hᴴ * R).trace := by
    calc
      (Hᴴ * R * H * R).trace = ((Hᴴ * R) * (H * R)).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((H * R) * (Hᴴ * R)).trace := Matrix.trace_mul_comm _ _
      _ = (H * R * Hᴴ * R).trace := by simp only [Matrix.mul_assoc]
  rw [hcyc]
  simpa [R, U, one_div, _root_.mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using h

private lemma hs_pair_spectral (Z H : Matrix ι ι ℂ) (hZ : Z.PosDef) (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    Complex.re (inner ℂ
      (ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H))
      ((hsArithmeticMap Z u).inverse
        (ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H)))) =
      ∑ i, ∑ j,
        Complex.normSq (((hZ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * H *
          (hZ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) i j) *
          ((1-u) * hZ.isHermitian.eigenvalues i +
            u * hZ.isHermitian.eigenvalues j)⁻¹ := by
  change Complex.re (inner ℂ
      (ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H))
      ((hsArithmeticMap Z u).inverse (matrixHS H))) = _
  rw [hsArithmeticMap_inverse_apply Z H u hZ hu]
  rw [hsInner_matrix]
  rw [schurInverse_apply]
  let U : Matrix ι ι ℂ := hZ.isHermitian.eigenvectorUnitary
  let Y : Matrix ι ι ℂ := Uᴴ * H * U
  let D : Matrix ι ι ℂ := fun i j =>
    (((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j : ℝ) : ℂ)⁻¹
  let S : Matrix ι ι ℂ := entryScale D Y
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have htrace : (Hᴴ * (U * S * Uᴴ)).trace = (Yᴴ * S).trace := by
    calc
      (Hᴴ * (U * S * Uᴴ)).trace =
          ((Hᴴ * U * S) * Uᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = (Uᴴ * (Hᴴ * U * S)).trace := Matrix.trace_mul_comm _ _
      _ = ((Uᴴ * Hᴴ * U) * S).trace := by simp only [Matrix.mul_assoc]
      _ = (Yᴴ * S).trace := by
        congr 1
        simp [Y, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [htrace]
  change (Yᴴ * entryScale D Y).trace.re =
    ∑ i, ∑ j, Complex.normSq (Y i j) *
      ((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j)⁻¹
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [entryScale, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_apply]
  change Complex.re (star (Y i j) *
      ((((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j : ℝ) : ℂ)⁻¹ *
        Y i j)) = _
  have he : star (Y i j) * (D i j * Y i j) =
      ((Complex.normSq (Y i j) *
        ((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j)⁻¹ : ℝ) : ℂ) := by
    calc
      star (Y i j) * (D i j * Y i j) = (Y i j * star (Y i j)) * D i j := by ring
      _ = (Complex.normSq (Y i j) : ℂ) * D i j := by
        exact congrArg (fun x : ℂ => x * D i j)
          (by simpa only [starRingEnd_apply] using Complex.mul_conj (Y i j))
      _ = _ := by dsimp [D]; push_cast; rfl
  exact congrArg Complex.re he

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- The Bochner logarithmic derivative paired with an arbitrary complex direction
is the integral of the earned native Hilbert-Schmidt arithmetic inverse. -/
theorem arithmetic_inverse_pairing_eq_logDeriv (Z H : Matrix ι ι ℂ) (hZ : Z.PosDef) :
    (Hᴴ * logDeriv Z H).trace.re =
      ∫ u in (0 : ℝ)..1, Complex.re (inner ℂ
        (ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H))
        ((hsArithmeticMap Z u).inverse
          (ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H)))) := by
  let U : Matrix ι ι ℂ := hZ.isHermitian.eigenvectorUnitary
  let W : Matrix ι ι ℂ := Uᴴ * H * U
  let f : ℝ → Matrix ι ι ℂ := fun t => (Z + t • 1)⁻¹ * H * (Z + t • 1)⁻¹
  let T : Matrix ι ι ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp ((Matrix.traceLinearMap ι ℝ ℂ).toContinuousLinearMap.comp
      (mulLeftLinearMap ι ℝ Hᴴ).toContinuousLinearMap)
  have hf : Integrable f (volume.restrict (Set.Ioi (0 : ℝ))) :=
    logDeriv_integrable Z H hZ
  have hi (i j : ι) : Integrable (fun t : ℝ => Complex.normSq (W i j) *
      ((hZ.isHermitian.eigenvalues i + t)⁻¹ *
        (hZ.isHermitian.eigenvalues j + t)⁻¹))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hh := (pairKernel_integrable _ _ (hZ.eigenvalues_pos i)
      (hZ.eigenvalues_pos j)).const_mul (Complex.normSq (W i j))
    apply hh.congr
    filter_upwards [] with t
    simp only [one_div, mul_inv]
  have hj (i j : ι) : IntervalIntegrable (fun u : ℝ => Complex.normSq (W i j) *
      ((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j)⁻¹)
      volume 0 1 :=
    (affineKernel_integrable _ _ (hZ.eigenvalues_pos i) (hZ.eigenvalues_pos j)).const_mul _
  have hleft : (Hᴴ * logDeriv Z H).trace.re =
      ∑ i, ∑ j, Complex.normSq (W i j) *
        ∫ t in Set.Ioi (0 : ℝ), 1 / ((hZ.isHermitian.eigenvalues i + t) *
          (hZ.isHermitian.eigenvalues j + t)) := by
    calc
      (Hᴴ * logDeriv Z H).trace.re = ∫ t in Set.Ioi (0 : ℝ), T (f t) := by
        exact (T.integral_comp_comm hf).symm
      _ = ∫ t in Set.Ioi (0 : ℝ), ∑ i, ∑ j, Complex.normSq (W i j) *
          ((hZ.isHermitian.eigenvalues i + t)⁻¹ *
            (hZ.isHermitian.eigenvalues j + t)⁻¹) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have h := congrArg Complex.re (trace_hadjoint_resolvent Z H hZ t ht.le)
        simpa only [T, f, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
          mulLeftLinearMap_apply, Matrix.traceLinearMap_apply, Complex.reCLM_apply,
          Complex.re_sum, Complex.ofReal_re, Matrix.mul_assoc, W, U] using h
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hi i j))]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul]
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        simp [one_div, _root_.mul_inv_rev, mul_comm]
  rw [hleft]
  calc
    (∑ i, ∑ j, Complex.normSq (W i j) *
      ∫ t in Set.Ioi (0 : ℝ), 1 / ((hZ.isHermitian.eigenvalues i + t) *
        (hZ.isHermitian.eigenvalues j + t))) =
      ∑ i, ∑ j, Complex.normSq (W i j) *
        ∫ u in (0 : ℝ)..1, ((1-u) * hZ.isHermitian.eigenvalues i +
          u * hZ.isHermitian.eigenvalues j)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [affineKernel_eq_pair _ _ (hZ.eigenvalues_pos i) (hZ.eigenvalues_pos j)]
    _ = ∫ u in (0 : ℝ)..1, ∑ i, ∑ j, Complex.normSq (W i j) *
        ((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j)⁻¹ := by
      symm
      rw [intervalIntegral.integral_finsetSum
        (f := fun i u => ∑ j, Complex.normSq (W i j) *
          ((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j)⁻¹)
        (fun i _ => by
          convert IntervalIntegrable.sum Finset.univ (fun j _ => hj i j) using 1
          ext u
          simp only [Finset.sum_apply])]
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finsetSum (fun j _ => hj i j)]
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact (hs_pair_spectral Z H hZ u
        (by simpa only [Set.uIcc_of_le zero_le_one] using hu)).symm

end D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
