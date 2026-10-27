/- GID: D5/S3/Geometry/ProjectionRange/SimplexFrames
   generality: G
   mirror-B: D5/B/S3/Geometry/ProjectionRange/SimplexFrames
   mirror-E: none(waiver:pure-structural-proof)
   anchors: []
   utility: none
   digest: Continuous ambient range frames and coordinate reconstruction over genuine singular simplices. -/
import D5.S3.Geometry.ProjectionRange.Prebundle
import D5.S3.Geometry.ProjectionRange.UniformTransport
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Convexity ProjectionRange
open scoped Simplicial Matrix ComplexOrder Matrix.Norms.Elementwise

universe u

/-- Actual ambient frames and continuous ambient linear coordinates for the range
of a continuous Hermitian constant-rank projection pulled back to an original
singular simplex. The contraction and the uniform transport are constructed here.
The proof works in every dimension; the original k <= 3 telescope is retained. -/
theorem range_projection_simplex_frames
    {B : Type u} [TopologicalSpace B] {n r k : ℕ}
    (P : B → Matrix (Fin n) (Fin n) ℂ)
    (hP : Continuous P) (hstar : ∀ x, (P x)ᴴ = P x)
    (hidem : ∀ x, P x * P x = P x)
    (hrank : ∀ x, (P x).rank = r) (hk : k ≤ 3)
    (σ : C((SimplexCategory.toTop.obj ⦋k⦌), B)) :
    ∃ (s : Fin r → C((SimplexCategory.toTop.obj ⦋k⦌), V n))
      (a : C((SimplexCategory.toTop.obj ⦋k⦌), V n →L[ℂ] V r)),
      (∀ x i, s i x ∈ rangeSubmodule P (σ x)) ∧
      (∀ x i, a x (s i x) = EuclideanSpace.single i (1 : ℂ)) ∧
      (∀ x (v : Fiber P (σ x)),
        ∑ i, ((a x (v : V n)) i) • s i x = (v : V n)) := by
  classical
  let X := SimplexCategory.toTop.obj ⦋k⦌
  letI : CompactSpace X := inferInstanceAs
    (CompactSpace (ULift (StdSimplex ℝ (Fin (k + 1)))))
  let v₀ : X := ULift.up (StdSimplex.single (0 : Fin (k + 1)))
  let H : unitInterval × X → X := fun z => ULift.up
    (convexCombPair (R := ℝ) (X := StdSimplex ℝ (Fin (k + 1)))
      (unitInterval.symm z.1) z.1
      (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) v₀.down z.2.down)
  have hH : Continuous H := by
    apply continuous_uliftUp.comp
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (k + 1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    simp only [Function.comp_def, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, unitInterval.coe_symm_eq]
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      continuous_const).add
        ((continuous_subtype_val.comp continuous_fst).mul
          ((StdSimplex.continuous_weights_apply ℝ i).comp
            (continuous_uliftDown.comp continuous_snd)))
  have hH₀ (x : X) : H (0, x) = v₀ := by
    apply ULift.ext
    apply StdSimplex.ext
    simp [H, StdSimplex.weights_convexCombPair]
  have hH₁ (x : X) : H (1, x) = x := by
    apply ULift.ext
    apply StdSimplex.ext
    simp [H, StdSimplex.weights_convexCombPair]
  let E := V n →L[ℂ] V n
  let Q : C(unitInterval × X, E) :=
    ⟨fun z => matrixCLE n n (P (σ (H z))),
      (matrixCLE n n).continuous.comp (hP.comp (σ.continuous.comp hH))⟩
  let F : C(unitInterval, C(X, E)) := Q.curry
  have hF (t : unitInterval) : F t * F t = F t := by
    apply ContinuousMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    change ((Matrix.toEuclideanLin (P (σ (H (t, x))))).comp
      (Matrix.toEuclideanLin (P (σ (H (t, x)))))) v =
        Matrix.toEuclideanLin (P (σ (H (t, x)))) v
    rw [← Matrix.toLpLin_mul_same, hidem]
  obtain ⟨u, hu⟩ := UniformTransport.connected_idempotents_intertwiner
    (fun t => F t) F.continuous hF (0 : unitInterval) 1
  let U : C(X, E) := (u : C(X, E))
  let W : C(X, E) := (↑u⁻¹ : C(X, E))
  have hU (x : X) : matrixCLE n n (P (σ x)) * U x =
      U x * matrixCLE n n (P (σ v₀)) := by
    have h := congrArg (fun f : C(X, E) => f x) hu
    simpa [F, Q, U, hH₀, hH₁] using h
  have hUW (x : X) (v : V n) : U x (W x v) = v := by
    change (((u : C(X, E)) * (↑u⁻¹ : C(X, E))) x) v = v
    simp
  have hWU (x : X) (v : V n) : W x (U x v) = v := by
    change (((↑u⁻¹ : C(X, E)) * (u : C(X, E))) x) v = v
    simp
  have hUinj (x : X) : Function.Injective (U x) := by
    intro v w h
    have h' := congrArg (W x) h
    simpa only [hWU] using h'
  let b₀ := σ v₀
  let c := chartAt hP hstar hidem hrank b₀
  have hc : b₀ ∈ c.U := mem_chartAt hP hstar hidem hrank b₀
  let A₀ : V r →L[ℂ] V n := matrixCLE n r (columns P c.J b₀)
  let C₀ : V n →L[ℂ] V r := matrixCLE r n (leftMatrix P c.J b₀)
  have hA₀ (z : V r) : A₀ z ∈ rangeSubmodule P b₀ :=
    (c.intoRange hidem b₀ z).property
  have hCA₀ (z : V r) : C₀ (A₀ z) = z :=
    c.coordinates_intoRange hidem hc z
  have hAC₀ (v : V n) (hv : v ∈ rangeSubmodule P b₀) : A₀ (C₀ v) = v :=
    congrArg Subtype.val (c.intoRange_coordinates hidem hc ⟨v, hv⟩)

  have hpre (x : X) (v : V n) (hv : v ∈ rangeSubmodule P (σ x)) :
      W x v ∈ rangeSubmodule P b₀ := by
    apply (mem_fiber_iff_fixed hidem b₀ (W x v)).mpr
    apply hUinj x
    have h := congrArg (fun f : E => f (W x v)) (hU x)
    change matrixCLE n n (P (σ x)) (U x (W x v)) =
      U x (matrixCLE n n (P b₀) (W x v)) at h
    have hfix : matrixCLE n n (P (σ x)) v = v :=
      (mem_fiber_iff_fixed hidem (σ x) v).mp hv
    rw [hUW, hfix] at h
    change U x (matrixCLE n n (P b₀) (W x v)) = U x (W x v)
    rw [hUW]
    exact h.symm
  let s : Fin r → C(X, V n) := fun i =>
    ⟨fun x => U x (A₀ (EuclideanSpace.single i 1)),
      U.continuous.clm_apply continuous_const⟩
  let a : C(X, V n →L[ℂ] V r) :=
    ⟨fun x => C₀.comp (W x), continuous_const.clm_comp W.continuous⟩
  have hsum (z : V r) : ∑ i, z i • EuclideanSpace.single i (1 : ℂ) = z := by
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin r) ℂ).sum_repr z
  refine ⟨s, a, ?_, ?_, ?_⟩
  · intro x i
    apply (mem_fiber_iff_fixed hidem (σ x) (s i x)).mpr
    have h := congrArg (fun f : E => f (A₀ (EuclideanSpace.single i 1))) (hU x)
    change matrixCLE n n (P (σ x)) (U x (A₀ (EuclideanSpace.single i 1))) =
      U x (matrixCLE n n (P b₀) (A₀ (EuclideanSpace.single i 1))) at h
    have hfix : matrixCLE n n (P b₀) (A₀ (EuclideanSpace.single i 1)) =
        A₀ (EuclideanSpace.single i 1) :=
      (mem_fiber_iff_fixed hidem b₀ _).mp (hA₀ _)
    rw [hfix] at h
    exact h
  · intro x i
    change C₀ (W x (U x (A₀ (EuclideanSpace.single i 1)))) = _
    rw [hWU, hCA₀]
  · intro x v
    change ∑ i, (C₀ (W x (v : V n))) i •
      U x (A₀ (EuclideanSpace.single i 1)) = (v : V n)
    calc
      _ = U x (A₀ (∑ i, (C₀ (W x (v : V n))) i •
          EuclideanSpace.single i (1 : ℂ))) := by simp only [map_sum, map_smul]
      _ = U x (A₀ (C₀ (W x (v : V n)))) := by rw [hsum]
      _ = U x (W x (v : V n)) := by rw [hAC₀ _ (hpre x v v.property)]
      _ = (v : V n) := hUW x v
