/- GID: D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/FiniteSynthesisGramDistance
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: Finite synthesis has the singular Gram projection and infimum-distance formulas. -/

import D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance

open scoped InnerProductSpace
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- The finite Gram operator; the ambient Hilbert space need not be finite-dimensional. -/
def gram (V : E →L[𝕜] H) : E →ₗ[𝕜] E :=
  (V.adjoint.comp V).toLinearMap

private theorem gram_symmetric (V : E →L[𝕜] H) : (gram V).IsSymmetric := by
  intro x y
  change inner 𝕜 (V.adjoint (V x)) y = inner 𝕜 x (V.adjoint (V y))
  rw [V.adjoint_inner_left, V.adjoint_inner_right]

private theorem adjoint_mem_range_gram (V : E →L[𝕜] H) (x : H) :
    V.adjoint x ∈ (gram V).range := by
  rw [← (gram_symmetric V).adjoint_eq, ← LinearMap.orthogonal_ker]
  intro y hy
  have hyV : V y = 0 := by
    have hk := V.ker_adjoint_comp_self
    have hmem : y ∈ V.ker := (show (gram V).ker = V.ker from hk) ▸ hy
    exact hmem
  rw [V.adjoint_inner_right, hyV, inner_zero_left]

private theorem gram_inverse_normal (V : E →L[𝕜] H) (x : H) :
    gram V (moorePenroseInverse (gram V) (V.adjoint x)) = V.adjoint x := by
  obtain ⟨c, hc⟩ := adjoint_mem_range_gram V x
  rw [← hc]
  exact congrArg (fun A : E →ₗ[𝕜] E => A c)
    (comp_moorePenroseInverse_comp (gram V))

/-- The Gram inverse yields the orthogonal projection as an equality of operators. -/
theorem finite_synthesis_gram_projection (V : E →L[𝕜] H) :
    V.range.starProjection =
      V.comp ((moorePenroseInverse (gram V)).toContinuousLinearMap.comp V.adjoint) := by
  ext x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨moorePenroseInverse (gram V) (V.adjoint x), rfl⟩
  · rintro _ ⟨c, rfl⟩
    change inner 𝕜 (x - V (moorePenroseInverse (gram V) (V.adjoint x))) (V c) = 0
    rw [← V.adjoint_inner_left, map_sub]
    change inner 𝕜 (V.adjoint x - gram V
      (moorePenroseInverse (gram V) (V.adjoint x))) c = 0
    rw [gram_inverse_normal, sub_self, inner_zero_left]

/-- The squared distance is an actual infimum over the synthesis range. -/
theorem finite_synthesis_gram_distance (V : E →L[𝕜] H) (x : H) :
    Metric.infDist x (V.range : Set H) ^ 2 = ‖x‖ ^ 2 -
      RCLike.re (inner 𝕜 (V.adjoint x)
        (moorePenroseInverse (gram V) (V.adjoint x))) := by
  have hp := finite_synthesis_gram_projection V
  have hd : Metric.infDist x (V.range : Set H) = ‖x - V.range.starProjection x‖ := by
    rw [Metric.infDist_eq_iInf]
    simp_rw [dist_eq_norm]
    exact (Submodule.starProjection_minimal (U := V.range) x).symm
  have hinner : inner 𝕜 x (V.range.starProjection x) =
      inner 𝕜 (V.adjoint x) (moorePenroseInverse (gram V) (V.adjoint x)) := by
    rw [hp]
    exact (V.adjoint_inner_left _ x).symm
  rw [hd, norm_sub_sq (𝕜 := 𝕜), hinner]
  have he := V.range.re_inner_starProjection_eq_normSq x
  have he' : RCLike.re (inner 𝕜 (V.adjoint x)
      (moorePenroseInverse (gram V) (V.adjoint x))) =
      ‖V.range.starProjection x‖ ^ 2 := by
    rw [← hinner, inner_re_symm]
    exact he
  rw [he']
  ring

/-- The quadratic Gram expression is real, even over the complex field. -/
theorem finite_synthesis_gram_quadratic (V : E →L[𝕜] H) (x : H) :
    inner 𝕜 (V.adjoint x) (moorePenroseInverse (gram V) (V.adjoint x)) =
      (‖V.range.starProjection x‖ ^ 2 : ℝ) := by
  rw [V.adjoint_inner_left]
  change inner 𝕜 x
    ((V.comp ((moorePenroseInverse (gram V)).toContinuousLinearMap.comp V.adjoint)) x) = _
  rw [← finite_synthesis_gram_projection]
  have ho := V.range.starProjection_inner_eq_zero x
    (V.range.starProjection x) (Submodule.starProjection_apply_mem _ _)
  rw [inner_sub_left] at ho
  rw [sub_eq_zero.mp ho, inner_self_eq_norm_sq_to_K]
  exact (RCLike.ofReal_pow _ _).symm

/-- Under invertibility alone the Moore-Penrose inverse is the ordinary inverse. -/
theorem moore_penrose_eq_inverse (A : E ≃ₗ[𝕜] E) :
    moorePenroseInverse A.toLinearMap = A.symm.toLinearMap := by
  symm
  apply eq_moorePenroseInverse_of_isMoorePenroseInverse
  constructor
  · ext x; simp
  · ext x; simp
  · intro x y; simp
  · intro x y; simp

/-- The ordinary-inverse specialization, with its sole additional hypothesis explicit. -/
theorem finite_synthesis_gram_distance_inverse (V : E →L[𝕜] H) (x : H)
    (G : E ≃ₗ[𝕜] E) (hG : G.toLinearMap = gram V) :
    Metric.infDist x (V.range : Set H) ^ 2 = ‖x‖ ^ 2 -
      RCLike.re (inner 𝕜 (V.adjoint x) (G.symm (V.adjoint x))) := by
  rw [finite_synthesis_gram_distance, ← hG, moore_penrose_eq_inverse]
  rfl

#print axioms finite_synthesis_gram_projection
#print axioms finite_synthesis_gram_distance
#print axioms finite_synthesis_gram_distance_inverse

end D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance
