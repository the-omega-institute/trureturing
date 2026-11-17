/- GID: D5/S3/Geometry/EllipsoidShape
   generality: G
   mirror-B: D5/B/S3/Geometry/EllipsoidShape
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The entire affine ellipsoid determines its positive shape operator. -/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.LocallyConvex.Separation
import D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance

/-! Positive shapes and inverse-shape metrics of entire finite ellipsoids. -/



noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace
namespace D5.S3.Geometry.EllipsoidShape
variable {E F H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

private theorem adjoint_norm_le_of_ball_subset (A : E →L[ℝ] H) (B : F →L[ℝ] H)
    (h : A '' closedBall 0 1 ⊆ B '' closedBall 0 1) (y : H) :
    ‖A.adjoint y‖ ≤ ‖B.adjoint y‖ := by
  by_cases hz : A.adjoint y = 0
  · simp [hz]
  have hn : 0 < ‖A.adjoint y‖ := norm_pos_iff.mpr hz
  let x := ‖A.adjoint y‖⁻¹ • A.adjoint y
  have hx : ‖x‖ = 1 := by simp [x, norm_smul, hn.ne']
  obtain ⟨z, hzball, hzeq⟩ := h ⟨x, mem_closedBall_zero_iff.mpr hx.le, rfl⟩
  have hi : ⟪A.adjoint y, x⟫_ℝ = ‖A.adjoint y‖ := by
    simp only [x, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hzi : ⟪B.adjoint y, z⟫_ℝ = ‖A.adjoint y‖ := by
    rw [ContinuousLinearMap.adjoint_inner_left, hzeq,
      ← ContinuousLinearMap.adjoint_inner_left, hi]
  have hh := real_inner_le_norm (B.adjoint y) z
  rw [hzi] at hh
  exact hh.trans (mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp hzball))

theorem gram_eq_of_ball_image_eq (A : E →L[ℝ] H) (B : F →L[ℝ] H)
    (h : A '' closedBall 0 1 = B '' closedBall 0 1) :
    A.comp A.adjoint = B.comp B.adjoint := by
  have hn (y : H) : ‖A.adjoint y‖ = ‖B.adjoint y‖ :=
    le_antisymm (adjoint_norm_le_of_ball_subset A B h.subset y)
      (adjoint_norm_le_of_ball_subset B A h.symm.subset y)
  have hi (x y : H) : ⟪A.adjoint x, A.adjoint y⟫_ℝ =
      ⟪B.adjoint x, B.adjoint y⟫_ℝ := by
    simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      ← map_add, hn]
  ext y
  apply ext_inner_left ℝ
  intro x
  simpa only [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left] using hi x y


open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse

/-- The actual inverse-shape metric pulls back to the Euclidean source metric. -/
theorem metric_pullback (A : E →L[ℝ] H) (hA : Function.Injective A) (x y : E) :
    ⟪A x, moorePenroseInverse (A.comp A.adjoint).toLinearMap (A y)⟫_ℝ = ⟪x, y⟫_ℝ := by
  have hr : A.toLinearMap.adjoint.range = ⊤ := by
    rw [← LinearMap.orthogonal_ker, LinearMap.ker_eq_bot.mpr hA,
      Submodule.bot_orthogonal_eq_top]
  obtain ⟨z, hz⟩ := (LinearMap.range_eq_top.mp hr) y
  have hp := congrArg (fun L : H →ₗ[ℝ] H => L z)
    (comp_moorePenroseInverse_comp (A.comp A.adjoint).toLinearMap)
  have hz' : A.adjoint z = y := by
    change A.adjoint.toLinearMap z = y
    rw [← ContinuousLinearMap.adjoint_toLinearMap]
    exact hz
  have hnorm : A.adjoint
      (moorePenroseInverse (A.comp A.adjoint).toLinearMap (A y)) = y := by
    apply hA
    change A (A.adjoint (moorePenroseInverse (A.comp A.adjoint).toLinearMap (A y))) = A y
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, ← LinearMap.adjoint_toContinuousLinearMap,
      LinearMap.coe_toContinuousLinearMap, hz'] using hp
  rw [← A.adjoint_inner_right, hnorm]

/-- The inverse-shape disc is restricted to the actual image, including its boundary sphere. -/
theorem metric_ball_image (A : E →L[ℝ] H) (hA : Function.Injective A) (v : H) :
    (v ∈ A '' closedBall 0 1 ↔
      v ∈ (A.comp A.adjoint).range ∧
        ⟪v, moorePenroseInverse (A.comp A.adjoint).toLinearMap v⟫_ℝ ≤ 1) ∧
    (v ∈ A '' sphere 0 1 ↔
      v ∈ (A.comp A.adjoint).range ∧
        ⟪v, moorePenroseInverse (A.comp A.adjoint).toLinearMap v⟫_ℝ = 1) := by
  have hr : (A.comp A.adjoint).range = A.range := by
    simpa only [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.adjoint_toLinearMap] using
      (LinearMap.range_self_comp_adjoint A.toLinearMap)
  have he (x : E) :
      ⟪A x, moorePenroseInverse (A.comp A.adjoint).toLinearMap (A x)⟫_ℝ = ‖x‖ ^ 2 := by
    rw [metric_pullback A hA, real_inner_self_eq_norm_sq]
  constructor
  · constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hr.symm ▸ ⟨x, rfl⟩, ?_⟩
      rw [he]
      have hx' := mem_closedBall_zero_iff.mp hx
      nlinarith [norm_nonneg x]
    · rintro ⟨hv, hq⟩
      obtain ⟨x, rfl⟩ := hr ▸ hv
      refine ⟨x, mem_closedBall_zero_iff.mpr ?_, rfl⟩
      have hx' : ‖x‖ ^ 2 ≤ 1 := (he x) ▸ hq
      nlinarith [norm_nonneg x]
  · constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hr.symm ▸ ⟨x, rfl⟩, ?_⟩
      rw [he, mem_sphere_zero_iff_norm.mp hx]
      norm_num
    · rintro ⟨hv, hq⟩
      obtain ⟨x, rfl⟩ := hr ▸ hv
      refine ⟨x, mem_sphere_zero_iff_norm.mpr ?_, rfl⟩
      have hh : ‖x‖ ^ 2 = 1 := (he x) ▸ hq
      nlinarith [norm_nonneg x]

/-- The Penrose range projection is the auxiliary orthogonal projection onto the actual range. -/
theorem comp_dagger_eq_projection (Q : H →L[ℝ] H) :
    Q.comp (moorePenroseInverse Q.toLinearMap).toContinuousLinearMap = Q.range.starProjection := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨moorePenroseInverse Q.toLinearMap x, rfl⟩
  · rintro _ ⟨z, rfl⟩
    have hf : Q (moorePenroseInverse Q.toLinearMap (Q z)) = Q z :=
      congrArg (fun L : H →ₗ[ℝ] H => L z) (comp_moorePenroseInverse_comp Q.toLinearMap)
    have hs := isSymmetric_comp_moorePenroseInverse Q.toLinearMap
    change ⟪x - Q (moorePenroseInverse Q.toLinearMap x), Q z⟫_ℝ = 0
    have hh : ⟪Q (moorePenroseInverse Q.toLinearMap x), Q z⟫_ℝ =
        ⟪x, Q (moorePenroseInverse Q.toLinearMap (Q z))⟫_ℝ := hs _ _
    rw [hf] at hh
    rw [inner_sub_left, hh, sub_self]

private theorem dagger_mem_range (Q : H →L[ℝ] H) (hQ : Q.IsSymmetric) (x : H) :
    moorePenroseInverse Q.toLinearMap x ∈ Q.range := by
  have hadj : Q.toLinearMap.adjoint = Q.toLinearMap := hQ.adjoint_eq
  have he : Q.toLinearMap.kerᗮ = Q.range := by
    rw [LinearMap.orthogonal_ker, hadj]
  rw [← he]
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro z hz
  have hf : moorePenroseInverse Q.toLinearMap (Q (moorePenroseInverse Q.toLinearMap x)) =
      moorePenroseInverse Q.toLinearMap x :=
    congrArg (fun L : H →ₗ[ℝ] H => L x) (moorePenroseInverse_comp_comp Q.toLinearMap)
  have hs := isSymmetric_moorePenroseInverse_comp Q.toLinearMap
  calc ⟪moorePenroseInverse Q.toLinearMap x, z⟫_ℝ =
        ⟪moorePenroseInverse Q.toLinearMap (Q (moorePenroseInverse Q.toLinearMap x)), z⟫_ℝ := by rw [hf]
    _ = ⟪moorePenroseInverse Q.toLinearMap x, moorePenroseInverse Q.toLinearMap (Q z)⟫_ℝ := hs _ _
    _ = 0 := by rw [show Q z = 0 from hz, map_zero, inner_zero_right]

set_option maxHeartbeats 1200000 in
/-- A lower bound on every source direction bounds the actual inverse on the whole ambient space. -/
theorem gram_dagger_norm_bound (A : E →L[ℝ] H) {η : ℝ} (hη : 0 < η)
    (hA : ∀ x, η * ‖x‖ ≤ ‖A x‖) :
    ‖(moorePenroseInverse (A.comp A.adjoint).toLinearMap).toContinuousLinearMap‖ ≤ (η ^ 2)⁻¹ := by
  let Q := A.comp A.adjoint
  have hr : Q.range = A.range := by
    simpa only [Q, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.adjoint_toLinearMap] using LinearMap.range_self_comp_adjoint A.toLinearMap
  have hcoerce (z : E) : η ^ 2 * ‖A z‖ ≤ ‖Q (A z)‖ := by
    by_cases hz : z = 0
    · simp [hz]
    have hnz := norm_pos_iff.mpr hz
    have hh : ‖A z‖ ^ 2 ≤ ‖z‖ * ‖A.adjoint (A z)‖ := by
      rw [← real_inner_self_eq_norm_sq, ← A.adjoint_inner_right]
      exact real_inner_le_norm _ _
    have hg : η * ‖A z‖ ≤ ‖A.adjoint (A z)‖ := by
      nlinarith [mul_le_mul_of_nonneg_right (hA z) (norm_nonneg (A z))]
    have hg' := hA (A.adjoint (A z))
    change η ^ 2 * ‖A z‖ ≤ ‖A (A.adjoint (A z))‖
    nlinarith [mul_le_mul_of_nonneg_left hg hη.le]
  apply ((moorePenroseInverse Q.toLinearMap).toContinuousLinearMap).opNorm_le_bound (by positivity)
  intro x
  have hm := dagger_mem_range Q (ContinuousLinearMap.isPositive_self_comp_adjoint A).isSymmetric x
  obtain ⟨z, hz⟩ := hr ▸ hm
  change A z = moorePenroseInverse Q.toLinearMap x at hz
  have hb : ‖Q (moorePenroseInverse Q.toLinearMap x)‖ ≤ ‖x‖ := by
    have hp := congrArg (fun L : H →L[ℝ] H => L x) (comp_dagger_eq_projection Q)
    change Q (moorePenroseInverse Q.toLinearMap x) = Q.range.starProjection x at hp
    rw [hp]
    exact Q.range.norm_starProjection_apply_le x
  have hl := hcoerce z
  rw [hz] at hl
  change ‖moorePenroseInverse Q.toLinearMap x‖ ≤ (η ^ 2)⁻¹ * ‖x‖
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sq_pos_of_pos hη)).mpr (by nlinarith)

/-- On a uniformly bounded inverse family, the four Penrose laws pass to limits. -/
theorem continuous_dagger_of_bound {X : Type*} [PseudoMetricSpace X]
    (Q : X → (H →L[ℝ] H)) (hQ : Continuous Q)
    (M : ℝ) (hM : ∀ x, ‖(moorePenroseInverse (Q x).toLinearMap).toContinuousLinearMap‖ ≤ M) :
    Continuous (fun x => (moorePenroseInverse (Q x).toLinearMap).toContinuousLinearMap) := by
  classical
  let B (x : X) := (moorePenroseInverse (Q x).toLinearMap).toContinuousLinearMap
  apply continuous_iff_seqContinuous.mpr
  intro xn x hx
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨L, hL, ms, hms, ht⟩ :=
    (isCompact_closedBall (0 : H →L[ℝ] H) M).tendsto_subseq
      (fun n => mem_closedBall_zero_iff.mpr (hM (xn (ns n))))
  have hQt := (hQ.tendsto x).comp (hx.comp (hns.comp hms.tendsto_atTop))
  have hpair := hQt.prodMk_nhds ht
  have h1n (z : X) : (Q z).comp ((B z).comp (Q z)) = Q z := by
    ext v
    exact congrArg (fun T : H →ₗ[ℝ] H => T v)
      (comp_moorePenroseInverse_comp (Q z).toLinearMap)
  have h2n (z : X) : (B z).comp ((Q z).comp (B z)) = B z := by
    ext v
    exact congrArg (fun T : H →ₗ[ℝ] H => T v)
      (moorePenroseInverse_comp_comp (Q z).toLinearMap)
  have h1 : (Q x).comp (L.comp (Q x)) = Q x := by
    have hc : Continuous (fun z : (H →L[ℝ] H) × (H →L[ℝ] H) =>
        z.1.comp (z.2.comp z.1)) := by fun_prop
    exact tendsto_nhds_unique ((hc.tendsto (Q x, L)).comp hpair)
      (by
        change Tendsto (fun n => (Q (xn (ns (ms n)))).comp
          ((B (xn (ns (ms n)))).comp (Q (xn (ns (ms n)))))) atTop (𝓝 (Q x))
        simpa only [h1n, Function.comp_def] using hQt)
  have h2 : L.comp ((Q x).comp L) = L := by
    have hc : Continuous (fun z : (H →L[ℝ] H) × (H →L[ℝ] H) =>
        z.2.comp (z.1.comp z.2)) := by fun_prop
    exact tendsto_nhds_unique ((hc.tendsto (Q x, L)).comp hpair)
      (by
        change Tendsto (fun n => (B (xn (ns (ms n)))).comp
          ((Q (xn (ns (ms n)))).comp (B (xn (ns (ms n)))))) atTop (𝓝 L)
        simpa only [h2n, Function.comp_def, B] using ht)
  have h3 : ((Q x).toLinearMap.comp L.toLinearMap).IsSymmetric := by
    intro v w
    have hc : IsClosed {z : (H →L[ℝ] H) × (H →L[ℝ] H) |
        ⟪z.1 (z.2 v), w⟫_ℝ = ⟪v, z.1 (z.2 w)⟫_ℝ} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact hc.mem_of_tendsto hpair (Eventually.of_forall fun n =>
      isSymmetric_comp_moorePenroseInverse (Q (xn (ns (ms n)))).toLinearMap v w)
  have h4 : (L.toLinearMap.comp (Q x).toLinearMap).IsSymmetric := by
    intro v w
    have hc : IsClosed {z : (H →L[ℝ] H) × (H →L[ℝ] H) |
        ⟪z.2 (z.1 v), w⟫_ℝ = ⟪v, z.2 (z.1 w)⟫_ℝ} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact hc.mem_of_tendsto hpair (Eventually.of_forall fun n =>
      isSymmetric_moorePenroseInverse_comp (Q (xn (ns (ms n)))).toLinearMap v w)
  have hi : L.toLinearMap = moorePenroseInverse (Q x).toLinearMap :=
    eq_moorePenroseInverse_of_isMoorePenroseInverse
      ⟨congrArg ContinuousLinearMap.toLinearMap h1,
        congrArg ContinuousLinearMap.toLinearMap h2, h3, h4⟩
  have heq : L = B x := by ext v; exact LinearMap.congr_fun hi v
  exact ⟨ms, by simpa only [heq, Function.comp_def, B] using ht⟩

private def matrixModel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] : (H →L[ℝ] H) ≃⋆ₐ[ℝ] Matrix (Fin (Module.finrank ℝ H))
      (Fin (Module.finrank ℝ H)) ℝ :=
  let e : (H →ₗ[ℝ] H) ≃⋆ₐ[ℝ] (H →L[ℝ] H) :=
    { Module.End.toContinuousLinearMap (𝕜 := ℝ) H with
      map_smul' := fun r x => by ext v; rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap }
  e.symm.trans (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℝ H))

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- The positive square root is constructed on the full ambient Euclidean space. -/
def positiveSqrt (Q : H →L[ℝ] H) : H →L[ℝ] H :=
  (matrixModel H).symm (CFC.sqrt (matrixModel H Q))

private theorem matrixModel_positive (Q : H →L[ℝ] H) :
    (matrixModel H Q).PosSemidef ↔ Q.IsPositive := by
  exact LinearMap.posSemidef_toMatrix_iff (stdOrthonormalBasis ℝ H)

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- Existence and uniqueness of the actual positive square root. -/
theorem positiveSqrt_spec (Q : H →L[ℝ] H) (hQ : Q.IsPositive) :
    (positiveSqrt Q).IsPositive ∧ (positiveSqrt Q).comp (positiveSqrt Q) = Q ∧
      ∀ S : H →L[ℝ] H, S.IsPositive → S.comp S = Q → S = positiveSqrt Q := by
  have hM : 0 ≤ matrixModel H Q := (matrixModel_positive Q).mpr hQ |>.nonneg
  have hs : matrixModel H (positiveSqrt Q) = CFC.sqrt (matrixModel H Q) :=
    (matrixModel H).apply_symm_apply _
  refine ⟨(matrixModel_positive _).mp ?_, ?_, ?_⟩
  · rw [hs]
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  · apply (matrixModel H).injective
    change matrixModel H (positiveSqrt Q * positiveSqrt Q) = matrixModel H Q
    rw [map_mul, hs, CFC.sqrt_mul_sqrt_self _ hM]
  · intro S hS hSq
    apply (matrixModel H).injective
    change matrixModel H S = matrixModel H (positiveSqrt Q)
    rw [hs]
    symm
    apply CFC.sqrt_unique
    · rw [← map_mul]
      exact congrArg (matrixModel H) hSq
    · exact (matrixModel_positive _).mpr hS |>.nonneg

private theorem support_maximum (A : E →L[ℝ] H) (y : H) :
    ∃ x ∈ closedBall (0 : E) 1, ⟪y, A x⟫_ℝ = ‖A.adjoint y‖ := by
  by_cases hz : A.adjoint y = 0
  · refine ⟨0, by simp, ?_⟩
    simp [hz]
  have hn := norm_pos_iff.mpr hz
  refine ⟨‖A.adjoint y‖⁻¹ • A.adjoint y, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    simp [norm_smul, hz]
  · rw [← A.adjoint_inner_left, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp

private theorem ball_image_subset_of_adjoint_norm_le (A : E →L[ℝ] H) (B : F →L[ℝ] H)
    (hn : ∀ y, ‖A.adjoint y‖ ≤ ‖B.adjoint y‖) :
    A '' closedBall 0 1 ⊆ B '' closedBall 0 1 := by
  rintro _ ⟨x, hx, rfl⟩
  by_contra hnot
  have hconv : Convex ℝ (B '' closedBall 0 1) :=
    (convex_closedBall (0 : F) (1 : ℝ)).linear_image B.toLinearMap
  have hclosed : IsClosed (B '' closedBall 0 1) :=
    ((isCompact_closedBall (0 : F) 1).image B.continuous).isClosed
  obtain ⟨f, r, hfr, hfx⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
  let y := (InnerProductSpace.toDual ℝ H).symm f
  have hf (v : H) : ⟪y, v⟫_ℝ = f v := InnerProductSpace.toDual_symm_apply
  obtain ⟨z, hz, hmax⟩ := support_maximum B y
  have hb : f (A x) ≤ ‖A.adjoint y‖ := by
    rw [← hf, ← A.adjoint_inner_left]
    exact (real_inner_le_norm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp hx))
  have hb' : ‖B.adjoint y‖ < r := by
    rw [← hmax, hf]
    exact hfr _ ⟨z, hz, rfl⟩
  exact (hb.trans (hn y)).not_gt (hb'.trans hfx)

/-- Equal positive shape operators give equal entire closed ball images, including ambient kernels. -/
theorem ball_image_eq_of_gram_eq (A : E →L[ℝ] H) (B : F →L[ℝ] H)
    (h : A.comp A.adjoint = B.comp B.adjoint) :
    A '' closedBall 0 1 = B '' closedBall 0 1 := by
  have hn (y : H) : ‖A.adjoint y‖ = ‖B.adjoint y‖ := by
    have he := congrArg (fun Q : H →L[ℝ] H => ⟪y, Q y⟫_ℝ) h
    change ⟪y, A (A.adjoint y)⟫_ℝ = ⟪y, B (B.adjoint y)⟫_ℝ at he
    rw [← A.adjoint_inner_left, ← B.adjoint_inner_left,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
    nlinarith [norm_nonneg (A.adjoint y), norm_nonneg (B.adjoint y)]
  exact Subset.antisymm (ball_image_subset_of_adjoint_norm_le A B (fun y => (hn y).le))
    (ball_image_subset_of_adjoint_norm_le B A (fun y => (hn y).ge))

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- Positive square roots vary continuously for a continuous positive family. -/
theorem continuous_positiveSqrt {X : Type*} [TopologicalSpace X]
    (Q : X → (H →L[ℝ] H)) (hQ : Continuous Q) (hp : ∀ x, (Q x).IsPositive) :
    Continuous (fun x => positiveSqrt (Q x)) := by
  have hm : Continuous (matrixModel H) := (matrixModel H).toAlgEquiv.toLinearEquiv.continuous_of_finiteDimensional
  have hmi : Continuous (matrixModel H).symm :=
    (matrixModel H).symm.toAlgEquiv.toLinearEquiv.continuous_of_finiteDimensional
  exact hmi.comp (CFC.continuousOn_sqrt.comp_continuous (hm.comp hQ)
    (fun x => (matrixModel_positive _).mpr (hp x) |>.nonneg))

/-- The entire ambient square-root ball, including null directions, is the original ellipsoid. -/
theorem positiveSqrt_ball_image (A : E →L[ℝ] H) :
    positiveSqrt (A.comp A.adjoint) '' closedBall 0 1 = A '' closedBall 0 1 := by
  let Q := A.comp A.adjoint
  obtain ⟨hp, hsq, _⟩ := positiveSqrt_spec Q (ContinuousLinearMap.isPositive_self_comp_adjoint A)
  apply ball_image_eq_of_gram_eq
  rw [hp.isSymmetric.clm_adjoint_eq]
  exact hsq

/-- The actual inverse of a positive shape is itself positive, including its nullspace. -/
theorem dagger_positive (Q : H →L[ℝ] H) (hQ : Q.IsPositive) :
    ((moorePenroseInverse Q.toLinearMap).toContinuousLinearMap).IsPositive := by
  let B := moorePenroseInverse Q.toLinearMap
  have hq : Q.toLinearMap.adjoint = Q.toLinearMap := hQ.isSymmetric.adjoint_eq
  have h1 := comp_moorePenroseInverse_comp Q.toLinearMap
  have h2 := moorePenroseInverse_comp_comp Q.toLinearMap
  have h3 := isSymmetric_comp_moorePenroseInverse Q.toLinearMap
  have h4 := isSymmetric_moorePenroseInverse_comp Q.toLinearMap
  have hb : B.adjoint = B := by
    apply eq_moorePenroseInverse_of_isMoorePenroseInverse
    constructor
    · have h := congrArg LinearMap.adjoint h1
      simpa only [LinearMap.adjoint_comp, hq, LinearMap.comp_assoc, B] using h
    · have h := congrArg LinearMap.adjoint h2
      simpa only [LinearMap.adjoint_comp, hq, LinearMap.comp_assoc, B] using h
    · have he : Q.toLinearMap.comp B.adjoint = B.comp Q.toLinearMap := by
        simpa only [LinearMap.adjoint_comp, hq, LinearMap.comp_assoc, B] using h4.adjoint_eq
      rw [he]
      exact h4
    · have he : B.adjoint.comp Q.toLinearMap = Q.toLinearMap.comp B := by
        simpa only [LinearMap.adjoint_comp, hq, LinearMap.comp_assoc, B] using h3.adjoint_eq
      rw [he]
      exact h3
  have hs : B.IsSymmetric := by
    intro x y
    rw [← LinearMap.adjoint_inner_left, hb]
  constructor
  · exact hs
  · intro x
    have he : B (Q (B x)) = B x := congrArg (fun T : H →ₗ[ℝ] H => T x) h2
    have hh : ⟪B x, x⟫_ℝ = ⟪Q (B x), B x⟫_ℝ := by
      calc
        ⟪B x, x⟫_ℝ = ⟪B (Q (B x)), x⟫_ℝ := by rw [he]
        _ = ⟪Q (B x), B x⟫_ℝ := hs _ _
    change 0 ≤ ⟪B x, x⟫_ℝ
    rw [hh]
    exact hQ.re_inner_nonneg_left (B x)

end D5.S3.Geometry.EllipsoidShape
