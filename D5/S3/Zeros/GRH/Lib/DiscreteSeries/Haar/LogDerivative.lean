/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/LogDerivative
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/LogDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Haar.LogDerivative. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Haar/LogDerivative.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar.SkewCoordinates
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of measure and integration (textbook or folklore).

Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth (known
result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: Logarithmic derivative on U(J), determinant of congruence, measure-preserving
isometries. -/


open Matrix MeasureTheory Module Real Complex LinearMap Fintype Norms.L2Operator IsHermInvolution
  MatMul
variable {n} [Fintype.{0} n] {J : Matrix n n ℂ} {V W} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : V → U J) (p)

/-- The condition that a map Φ from a real normed space to U(J), viewed as matrix-valued, is
real differentiable at the point p. -/
abbrev DifferentiableAtU := DifferentiableAt ℝ (Φ · |>.1.1) p

/-- For Φ: V → U(J), the real linear map v ↦ Φ(p)*J dΦ_p(v), that is the form Jg⁻¹dg pulled back
by Φ at p. -/
noncomputable def logDerivU := mulLeft ℝ ((Φ p).1.1ᴴ * J) ∘ₗ (fderiv ℝ (Φ · |>.1.1) p).1

variable {Φ p} [FiniteDimensional ℝ W]

lemma conjTranspose_logDerivU [IsHermInvolution J] (h : DifferentiableAtU Φ p) v :
  (logDerivU Φ p v)ᴴ = -logDerivU Φ p v := by
  have := congr($(((h.hasFDerivAt.star.mul_const' J).fun_mul' h.hasFDerivAt).fderiv) v)
  simp_all [logDerivU, isHermitian.eq, star, mem_U.1]; grind

lemma logDerivU_mul {Ψ} (h : DifferentiableAtU Φ p) (h' : DifferentiableAtU Ψ p) v :
  logDerivU (fun p ↦ Φ p * Ψ p) p v = (Ψ p).1.1ᴴ * logDerivU Φ p v * (Ψ p).1.1 + logDerivU Ψ p
  v := by simp_all [logDerivU, fderiv_fun_mul']; grind [mem_U]

/-- For a complex n×n matrix C, the congruence S ↦ CᴴSC on skew-hermitian matrices, written in
the real coordinates of `skewOfReal` and `skewCoords`, has determinant of absolute value |det
C|^{2n}. -/
lemma abs_det_skew_congruence (e : _ ≃ₗ[ℝ] V) C L : |(e.1 ∘ₗ skewCoords ∘ₗ mulLeftRight ℝ (Cᴴ, C) ∘ₗ
    @skewOfReal n ∘ₗ L).det| = ‖C.det‖ ^ (2 * card n) * |(e ∘ₗ L).det| := by rw [(?_ : _ ∘ₗ
            _ = _ * e ∘ₗ L), map_mul, abs_mul,
  (skewCoords ∘ₗ mulLeftRight ℝ (Cᴴ, C) ∘ₗ skewOfReal).det_conj e, ← sqrt_mul_self_eq_abs,
  ← det_prodMap, (((skewOfReal.coprod (I • skewOfReal)).linearEquivOfInjective (by
  simp [Function.Injective, skewOfReal, ↓← ext_iff, Complex.ext_iff]; grind) (by simp +arith [
                    finrank_matrix])).eq_toLinearMap_symm_comp (prodMap ..) _).2,
  LinearMap.det_conj, det_mulLeft_mulRight_real Cᴴ C] <;> simp [DFunLike.ext_iff]

/-- Block triangular determinant: if an endomorphism T of V × W (finite-dimensional, real) has
first component (v,w) ↦ Av and its W-to-W block has determinant d, then det T = det A · d. -/
lemma Haar.det_eq_mul_of_block_triangular [FiniteDimensional ℝ V]
    {T : End ℝ (V × W)} (A : End ℝ V) (h : ∀ v, (T v).1 =
  A v.1) {B} (h' : B = snd .. ∘ₗ T ∘ₗ inr .. := by rfl) : T.det = A.det * B.det := by
  simp_rw [← det_toMatrix ((finBasis ℝ V).prod (finBasis ℝ W)), ← det_toMatrix (finBasis ..)]
  convert det_fromBlocks_zero₁₂' ..; simp_all [← ext_iff, toMatrix_apply]; tauto

variable [IsHermInvolution J] [FiniteDimensional ℝ V]

variable [MeasureSpace V] [BorelSpace V] [(@volume V _).IsAddHaarMeasure] [MeasureSpace W]
  [BorelSpace W] [(@volume W _).IsAddHaarMeasure] {a b q q'} [h : @HasGaussianIntegral V _ a q]

instance : (@volume (V × W) _).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure ..

instance {m} [Fintype m] : @HasGaussianIntegral (Matrix m n V) _ (a * card n * card m)
    fun x ↦ ∑ a, ∑ b, q (x a b) := h.pi.pi

/-- For real t, the scalar matrix e^{it}·1 as an element of U(J). -/
noncomputable def circleScalar (t : ℝ) : U J :=
  U.of isUnit ((t * I).exp • 1) (by simp [smul_smul, mul_conj'])

include h

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V]
  [(@volume V _).IsAddHaarMeasure] in
lemma lintegral_gaussian_eq_one : ∫⁻ x, ‖rexp (-π * q x)‖ₑ = 1 := by
  simp [-neg_mul, h.1 pi_pos, ← ofReal_integral_norm_eq_lintegral_enorm (.of_integral_ne_zero _)]

/-- If the Haar volumes on finite-dimensional real spaces V, W satisfy the Gaussian
normalisation `HasGaussianIntegral` for q, q', then a linear isomorphism e: V → W with q'(e x) =
q(x) for all x is measure preserving. -/
lemma HasGaussianIntegral.measurePreserving (e : V ≃ₗ[ℝ] W) [k : HasGaussianIntegral b q'] (he :
  ∀ x, q' (e x) = q x) : MeasurePreserving e := have m := isClosedEmbedding_of_injective e.ker
  ⟨m.measurable, addHaar_eq_of_integral_eq_one (by simpa using integral_exp_eq pi_pos)
    ((m.integral_map _).trans (by simpa [he] using integral_exp_eq pi_pos))⟩

/-- Let the volume on V satisfy `HasGaussianIntegral` for q and dim V = n². A linear map f from real
n×n matrices to V with q(f y) = Σ y_ab² is the inverse of a measure preserving linear
isomorphism from V to real matrices. -/
lemma HasGaussianIntegral.exists_measurePreserving_equiv (f : Matrix n n ℝ →ₗ[ℝ] V) (hf : ∀ y,
  q (f y) = ∑ a, ∑ b, y a b ^ 2)
  (hd : finrank ℝ (Matrix n n ℝ) = finrank ℝ V) : ∃ e : V ≃ₗ[ℝ] _, MeasurePreserving e ∧
  ⇑e.symm = f := let e := f.linearEquivOfInjective (.of_ker _ fun _ z ↦ ext (by
    simpa [← z, hf, Finset.sum_eq_zero_iff_of_nonneg, Finset.sum_nonneg, sq_nonneg] using hf 0)) hd
  ⟨e.symm, measurePreserving _ (hf _ ▸ congr(q $(e.4 ·))), rfl⟩
