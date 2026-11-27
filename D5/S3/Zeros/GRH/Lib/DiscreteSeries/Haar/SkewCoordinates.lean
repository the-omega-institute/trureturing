/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/SkewCoordinates
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/SkewCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Haar.SkewCoordinates. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Haar/SkewCoordinates.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar.UnitaryNorm
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth
(known result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: Real determinant of two-sided multiplication; basic API for U(J) and skew coordinates. -/


open Matrix LinearMap Algebra Fintype IsHermInvolution Topology
variable {n} [Fintype n] {J x : Matrix n n ℂ} [IsHermInvolution J] (y : Matrix n n ℝ)

/-- For complex square matrices P of size m and Q of size n, the real-linear map X ↦ PXQ on
complex m×n matrices has determinant |det P|^(2n)·|det Q|^(2m). -/
lemma det_mulLeft_mulRight_real {m} [Fintype m] P Q : (mulRightLinearMap m ℝ Q ∘ₗ mulLeftLinearMap n
  ℝ P).det = ‖det P‖ ^ (2 * card n) * ‖(det Q : ℂ)‖ ^ (2 * card m) := by erw [(mulRightLinearMap m
  ℂ Q ∘ₗ mulLeftLinearMap ..).det_restrictScalars, ← det_toMatrix (stdBasis ℂ ..), congrArg det _,
  det_kronecker' P Qᵀ] <;> simp [← ext_iff, toMatrix_apply, stdBasis, mul_apply, ite_apply,
  norm_complex_eq, pow_mul, Complex.sq_norm]

lemma exists_U_coe_eq : xᴴ * J * x = J → ∃ g : U J, g = x := (⟨U.of isUnit x ·, rfl⟩)

lemma isClosedEmbedding_U : IsClosedEmbedding (·.1.1 : U J → _) := U.isClosedEmbedding_mat isUnit

lemma continuous_U_iff_matrix {X} [TopologicalSpace X] {f : X → U J} : Continuous f ↔
  Continuous (f · |>.1.1) := isClosedEmbedding_U.continuous_iff

section

omit [Fintype n]

@[simp] lemma skewCoords_skewOfReal : skewCoords (skewOfReal y) = y :=
  ext (by simp [skewCoords, skewOfReal]; grind)

@[simp] lemma conjTranspose_skewOfReal : (skewOfReal y)ᴴ = -skewOfReal y :=
  ext (by simp [skewOfReal]; grind)

@[simp] lemma skewOfReal_skewCoords : xᴴ = -x → skewOfReal (skewCoords x) =
  x := by simp [skewCoords, skewOfReal, Complex.ext_iff, ← ext_iff]; grind

end
