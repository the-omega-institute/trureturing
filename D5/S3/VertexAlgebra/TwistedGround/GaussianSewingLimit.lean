/- GID: D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine coordinate and ordered resolvent limits for Gaussian sewing. -/

import D5.S3.VertexAlgebra.TwistedGround.CountableGaussianCutoff
import D5.S3.VertexAlgebra.TwistedGround.GaussianExternalBlock
import D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
import Mathlib.Analysis.Normed.Ring.Units

/-! Actual Hilbert-Schmidt compressions give ordered inverse and mixed-coordinate limits. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace lp ENNReal Ring Matrix.Norms.L2Operator
open Filter Topology
namespace D5.S3.VertexAlgebra.TwistedGround.GaussianSewingLimit
open InfiniteGaussianFock CountableGaussianCutoff GaussianExternalBlock
universe u v
variable {I : Type u} [DecidableEq I]

private theorem norm_le_hsSize (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ))
    (hT : Summable (fun ij : I × I => ‖T (lp.single 2 ij.2 1) ij.1‖ ^ 2)) :
    ‖T‖ ≤ hsSize T := by
  let b := coordinateBasis I
  let c := TraceClassFiniteBlocks.setBasis b
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  have hv : Summable (fun i : Set.range b => ‖T (c i)‖ ^ 2) := by
    apply e.summable_iff.mp
    simpa only [Function.comp_def, c, TraceClassFiniteBlocks.setBasis_apply,
      Equiv.ofInjective_apply, e, b, coordinateBasis_apply] using
      (matrix_columns T hT).1
  obtain ⟨U,hU,_,_,hnorm⟩ :=
    HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns c (fun i => T (c i)) hv
  have hUT : U = T := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro j
    apply ContinuousLinearMap.ext
    intro z
    have hj : U (lp.single 2 j 1) = T (lp.single 2 j 1) := by
      simpa only [c, TraceClassFiniteBlocks.setBasis_apply, Equiv.ofInjective_apply,
        e, b, coordinateBasis_apply] using
        hU (e j)
    have hz : lp.single 2 j z = z • (lp.single 2 j (1 : ℂ) : ℓ²(I, ℂ)) := by
      simp [← lp.single_smul]
    simp [ContinuousLinearMap.comp_apply, hz, hj]
  rw [hUT] at hnorm
  change ‖T‖ ≤ Real.sqrt
    (∑' i, ‖T (TraceClassFiniteBlocks.setBasis (coordinateBasis I) i)‖ ^ 2) at hnorm
  simpa only [hs_basis_square T hT, hsSize] using hnorm

/-- HS compression convergence supplies operator-norm convergence by the
existing square-summable-column synthesis theorem. -/
theorem compressed_tendsto (D : Data I) :
    Tendsto (compressed D) atTop (𝓝 D.oneParticle) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := hs_compression_tendsto D
  apply squeeze_zero (fun _ => norm_nonneg _) _ h
  intro F
  rw [norm_sub_rev]
  exact norm_le_hsSize _ (error_summable D F)

/-- Each actual l2 vector loses only its own square-summable coordinate tail.
No operator-norm limit of the coordinate projections is asserted. -/
theorem projection_vector_tendsto (z : ℓ²(I, ℂ)) :
    Tendsto (fun F : Finset I => coordinateProjection F z) atTop (𝓝 z) := by
  have h := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z
  change Tendsto (fun F : Finset I => ∑ i ∈ F, lp.single 2 i (z i : ℂ)) atTop (𝓝 z) at h
  convert h using 1
  funext F
  ext i
  simp [projection_apply, lp.coeFn_sum, lp.single_apply, Pi.single_apply,
    Finset.sum_apply, Finset.sum_ite_eq', eq_comm]

/-- The ordered inverse retains BA. Its continuity is applied at the genuine
unit 1-BA, with the strict bound derived from the two given contractions. -/
theorem resolvent_tendsto (A B : Data I) :
    Tendsto (fun F => (1 - compressed B F * compressed A F)⁻¹ʳ) atTop
      (𝓝 ((1 - B.oneParticle * A.oneParticle)⁻¹ʳ)) := by
  have hnA := A.opNorm_le.trans_lt A.q_lt_one
  have hnB := B.opNorm_le.trans_lt B.q_lt_one
  have hn : ‖B.oneParticle * A.oneParticle‖ < 1 :=
    (norm_mul_le _ _).trans_lt
      ((mul_le_of_le_one_left (norm_nonneg _) hnB.le).trans_lt hnA)
  obtain ⟨u,hu⟩ := isUnit_one_sub_of_norm_lt_one hn
  have hi : ContinuousAt Ring.inverse (1 - B.oneParticle * A.oneParticle) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact hi.tendsto.comp (tendsto_const_nhds.sub
    ((compressed_tendsto B).mul (compressed_tendsto A)))

/-- The correction on the omitted coordinates vanishes for every actual
mixed column. This does not replace the finite complement by zero. -/
theorem mixed_complement_tendsto (r s : ℓ²(I, ℂ)) :
    Tendsto (fun F : Finset I => bilinear r ((1 - coordinateProjection F) s)) atTop (𝓝 0) := by
  have hz : Tendsto (fun F : Finset I => s - coordinateProjection F s) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : Finset I => s) atTop (𝓝 s)).sub
      (projection_vector_tendsto s)
  have h := (bilinear r).continuous.tendsto 0 |>.comp hz
  change Tendsto (fun F : Finset I => bilinear r (s - coordinateProjection F s))
    atTop (𝓝 (bilinear r 0)) at h
  simpa only [map_zero, map_sub, sub_apply, one_apply_eq_self] using h

/-- Every ordered effective entry converges, including the exact finite
mixed-block complement subtraction. -/
theorem ordered_entries_tendsto (A B : Data I) (r s : ℓ²(I, ℂ)) :
    Tendsto (fun F => bilinear r
      (((1 - compressed B F * compressed A F)⁻¹ʳ * compressed B F) s)) atTop
      (𝓝 (bilinear r (((1 - B.oneParticle * A.oneParticle)⁻¹ʳ * B.oneParticle) s))) ∧
    Tendsto (fun F => bilinear r ((1 - compressed B F * compressed A F)⁻¹ʳ s) -
      bilinear r ((1 - coordinateProjection F) s)) atTop
      (𝓝 (bilinear r ((1 - B.oneParticle * A.oneParticle)⁻¹ʳ s))) := by
  have hev : Continuous (fun T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ) => T s) :=
    continuous_id.clm_apply continuous_const
  constructor
  · exact ((bilinear r).continuous.tendsto _).comp
      (hev.tendsto _ |>.comp
        ((resolvent_tendsto A B).mul (compressed_tendsto B)))
  · simpa using (((bilinear r).continuous.tendsto _).comp
      (hev.tendsto _ |>.comp (resolvent_tendsto A B))).sub
        (mixed_complement_tendsto r s)

private theorem embedded_one (F : Finset I) :
    embedded F 1 = coordinateProjection F := by
  ext z i
  simp [embedded, coordinateProjection, one_apply_eq_self]

private theorem embedded_sub (F : Finset I) (M N : Matrix F F ℂ) :
    embedded F (M - N) = embedded F M - embedded F N := by
  simp [embedded, map_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]

private theorem embedded_left (F : Finset I) (M : Matrix F F ℂ) :
    coordinateProjection F * embedded F M = embedded F M := by
  rw [← embedded_one, ← embedded_mul, one_mul]

private theorem embedded_right (F : Finset I) (M : Matrix F F ℂ) :
    embedded F M * coordinateProjection F = embedded F M := by
  rw [← embedded_one, ← embedded_mul, mul_one]

/-- The exact padded inverse keeps the identity on the omitted coordinates. -/
theorem padded_inverse (A B : Data I) (F : Finset I) :
    (1 - compressed B F * compressed A F)⁻¹ʳ =
      1 - coordinateProjection F + embedded F ((1 - B.block F * A.block F)⁻¹ʳ) := by
  let W := compressed B F * compressed A F
  let N := embedded F ((1 - B.block F * A.block F)⁻¹ʳ)
  have hm : ‖B.block F * A.block F‖ < 1 :=
    (norm_mul_le _ _).trans_lt
      ((mul_le_of_le_one_left (norm_nonneg _)
        ((B.block_opNorm_le F).trans_lt B.q_lt_one).le).trans_lt
          ((A.block_opNorm_le F).trans_lt A.q_lt_one))
  have hu : IsUnit (1 - W) := by
    apply isUnit_one_sub_of_norm_lt_one
    exact (norm_mul_le _ _).trans_lt
      ((mul_le_of_le_one_left (norm_nonneg _)
        ((compressed_norm_le B F).trans_lt B.q_lt_one).le).trans_lt
          ((compressed_norm_le A F).trans_lt A.q_lt_one))
  have hN : N - W * N = coordinateProjection F := by
    have hh := congrArg (embedded F)
      (Ring.mul_inverse_cancel (1 - B.block F * A.block F)
        (isUnit_one_sub_of_norm_lt_one hm))
    simpa only [embedded_mul, embedded_sub, embedded_one, sub_mul,
      embedded_left, ← compressed_embedded, W, N] using hh
  have hWP : W * coordinateProjection F = W := by
    dsimp [W]
    rw [mul_assoc, compressed_embedded A F, embedded_right]
  have hz : (1 - W) * (1 - coordinateProjection F + N) = 1 := by
    calc
      _ = 1 - coordinateProjection F - (W - W * coordinateProjection F) +
          (N - W * N) := by noncomm_ring
      _ = 1 := by rw [hWP, hN]; noncomm_ring
  change (1 - W)⁻¹ʳ = 1 - coordinateProjection F + N
  calc
    _ = (1 - W)⁻¹ʳ * ((1 - W) * (1 - coordinateProjection F + N)) := by rw [hz, mul_one]
    _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

/-- Multiplication by the compressed internal block kills the complement. -/
theorem padded_inverse_mul (A B : Data I) (F : Finset I) :
    (1 - compressed B F * compressed A F)⁻¹ʳ * compressed B F =
      embedded F ((1 - B.block F * A.block F)⁻¹ʳ * B.block F) := by
  rw [padded_inverse, add_mul, sub_mul, one_mul, compressed_embedded B F,
    embedded_left, sub_self, zero_add, ← embedded_mul]

private theorem bilinear_finiteInclusion (F : Finset I) (r : ℓ²(I, ℂ))
    (z : EuclideanSpace ℂ F) :
    bilinear r (Data.finiteInclusion F z) = ∑ i : F, r i.val * z i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun F ℂ).sum_repr z]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, Data.finiteInclusion_single, mul_comm]

/-- Finite bilinear matrix multiplication equals the actual padded operator
entry paired against the original mixed l2 row and column. -/
theorem bilinear_embedded (F : Finset I) (M : Matrix F F ℂ) (r s : ℓ²(I, ℂ)) :
    bilinear r (embedded F M s) = ∑ i : F, ∑ j : F, r i.val * M i j * s j.val := by
  change bilinear r (Data.finiteInclusion F
    (Matrix.toEuclideanCLM (𝕜 := ℂ) M
      (ContinuousLinearMap.adjoint (Data.finiteInclusion F).toContinuousLinearMap s))) = _
  rw [bilinear_finiteInclusion]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct,
    Data.finiteInclusion_adjoint_apply, Finset.mul_sum, mul_assoc]

end D5.S3.VertexAlgebra.TwistedGround.GaussianSewingLimit
