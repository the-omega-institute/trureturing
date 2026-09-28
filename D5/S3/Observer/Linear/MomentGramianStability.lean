/- GID: D5/S3/Observer/Linear/MomentGramianStability
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/MomentGramianStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct finite orthogonal moment maps and prove exact residual-Gramian identities with quadratic compression error. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
Observation maps are actual bounded operators into a Hilbert trajectory space.
The compression is the orthogonal projection constructed by Mathlib, followed
by coordinates in an actual finite orthonormal basis. Gramian identities and
noise contraction are proved from those maps, not assumed as certificates.

For normalized polynomial moments, the subspace must still be instantiated
with the actual L2 polynomial space and its Legendre basis. The general
exponential-trajectory anisotropic remainder and spectral asymptotics are not
claimed by the Hilbert-space estimates in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.Linear.MomentGramianStability

open ContinuousLinearMap
open scoped RealInnerProductSpace InnerProduct

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual observation Gramian, using the Hilbert-space adjoint. -/
def gram (F : E →L[ℝ] H) : E →L[ℝ] E := F.adjoint.comp F

@[simp] theorem gram_inner (F : E →L[ℝ] H) (x y : E) :
    ⟪x, gram F y⟫_ℝ = ⟪F x, F y⟫_ℝ := by
  exact F.adjoint_inner_right x (F y)

@[simp] theorem gram_norm (F : E →L[ℝ] H) : ‖gram F‖ = ‖F‖^2 := by
  simpa only [gram, pow_two] using F.norm_adjoint_comp_self

/-- First-order Gramian perturbation is derived by an exact operator telescoping. -/
theorem gram_perturbation (F G : E →L[ℝ] H) :
    ‖gram F - gram G‖ ≤ (‖F‖ + ‖G‖) * ‖F - G‖ := by
  have he : gram F - gram G =
      F.adjoint.comp (F - G) + (F.adjoint - G.adjoint).comp G := by
    ext x
    simp only [gram, comp_apply, sub_apply, add_apply, map_sub]
    abel
  rw [he]
  calc
    ‖F.adjoint.comp (F - G) + (F.adjoint - G.adjoint).comp G‖ ≤
        ‖F.adjoint.comp (F - G)‖ + ‖(F.adjoint - G.adjoint).comp G‖ := norm_add_le _ _
    _ ≤ ‖F.adjoint‖ * ‖F - G‖ + ‖F.adjoint - G.adjoint‖ * ‖G‖ :=
      add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ = (‖F‖ + ‖G‖) * ‖F - G‖ := by
      rw [← map_sub, adjoint.norm_map, adjoint.norm_map]
      ring

variable (K : Submodule ℝ H) [CompleteSpace K]

/-- Retained trajectory data in the actual closed subspace. -/
def compressed (F : E →L[ℝ] H) : E →L[ℝ] K := K.orthogonalProjectionOnto.comp F

/-- The discarded trajectory, still represented in the original Hilbert space. -/
def residual (F : E →L[ℝ] H) : E →L[ℝ] H := Kᗮ.starProjection.comp F

/-- Gramian loss is exactly the positive Gramian of the discarded trajectory. -/
theorem gram_projection_residual (F : E →L[ℝ] H) :
    gram F - gram (compressed K F) = gram (residual K F) := by
  have hsym : Kᗮ.starProjection.adjoint = Kᗮ.starProjection :=
    Kᗮ.starProjection_isSymmetric.clm_adjoint_eq
  have hidem : Kᗮ.starProjection.comp Kᗮ.starProjection = Kᗮ.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (show Kᗮ ≤ Kᗮ from le_rfl)
  have hsum : ContinuousLinearMap.id ℝ H = K.starProjection + Kᗮ.starProjection :=
    Submodule.id_eq_sum_starProjection_self_orthogonalComplement (K := K)
  have hres : gram (residual K F) = F.adjoint.comp (Kᗮ.starProjection.comp F) := by
    unfold gram residual
    rw [adjoint_comp, hsym]
    simp only [comp_assoc, ← comp_assoc Kᗮ.starProjection Kᗮ.starProjection F, hidem]
  have hcomp : gram (compressed K F) = F.adjoint.comp (K.starProjection.comp F) := by
    unfold gram compressed
    rw [adjoint_comp, K.adjoint_orthogonalProjectionOnto]
    rfl
  rw [hres, hcomp]
  ext x
  have hx := congrArg (fun T : H →L[ℝ] H => T (F x)) hsum
  simp only [id_apply, add_apply] at hx
  simp only [gram, comp_apply, sub_apply]
  rw [← map_sub]
  congr 1
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hx)

/-- The discarded map vanishes on every comparison trajectory in K. -/
theorem residual_eq_difference (F G : E →L[ℝ] H) (hG : ∀ x, G x ∈ K) :
    residual K F = Kᗮ.starProjection.comp (F - G) := by
  ext x
  simp only [residual, comp_apply, sub_apply, map_sub,
    Submodule.starProjection_orthogonal_apply_eq_zero (hG x), sub_zero]

/-- The actual residual projection is contractive. -/
theorem residual_norm_le (F G : E →L[ℝ] H) (hG : ∀ x, G x ∈ K) :
    ‖residual K F‖ ≤ ‖F - G‖ := by
  rw [residual_eq_difference K F G hG]
  calc
    ‖Kᗮ.starProjection.comp (F - G)‖ ≤ ‖Kᗮ.starProjection‖ * ‖F - G‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖F - G‖ := mul_le_mul_of_nonneg_right Kᗮ.starProjection_norm_le (norm_nonneg _)
    _ = _ := one_mul _

/-- Compression loses only the square of the approximation residual.
The comparison map can vary with the time window; it is not assumed exact. -/
theorem moment_gramian_error (F G : E →L[ℝ] H) (hG : ∀ x, G x ∈ K) :
    ‖gram F - gram (compressed K F)‖ ≤ ‖F - G‖^2 := by
  rw [gram_projection_residual, gram_norm]
  have h := residual_norm_le K F G hG
  nlinarith [norm_nonneg (residual K F), norm_nonneg (F - G)]

/-- Quantitative second-order window compression error from a first-order
trajectory residual; this does not supply the missing Taylor bound itself. -/
theorem moment_gramian_quadratic_bound (F G : E →L[ℝ] H)
    (hG : ∀ x, G x ∈ K) (c t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (herr : ‖F - G‖ ≤ c * t) :
    ‖gram F - gram (compressed K F)‖ ≤ c^2 * t^2 := by
  have h := moment_gramian_error K F G hG
  have hnon : 0 ≤ c * t := mul_nonneg hc ht
  nlinarith [norm_nonneg (F - G)]

section FiniteMoments
variable {ι : Type*} [Fintype ι]

/-- Actual finite moment coordinates of the projected trajectory. -/
def moments (b : OrthonormalBasis ι ℝ K) : H →L[ℝ] EuclideanSpace ℝ ι :=
  b.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp K.orthogonalProjectionOnto

def momentObservation (b : OrthonormalBasis ι ℝ K) (F : E →L[ℝ] H) :
    E →L[ℝ] EuclideanSpace ℝ ι := (moments K b).comp F

/-- Coordinate extraction preserves the projected Gramian exactly. -/
theorem momentObservation_gram (b : OrthonormalBasis ι ℝ K) (F : E →L[ℝ] H) :
    gram (momentObservation K b F) = gram (compressed K F) := by
  ext x
  apply ext_inner_left ℝ
  intro y
  rw [gram_inner, gram_inner]
  exact b.repr.inner_map_map (K.orthogonalProjectionOnto (F y))
    (K.orthogonalProjectionOnto (F x))

/-- The finite moment coordinate map does not amplify L2 trajectory noise. -/
theorem moments_noise_contraction (b : OrthonormalBasis ι ℝ K) (x y : H) :
    ‖moments K b x - moments K b y‖ ≤ ‖x - y‖ := by
  rw [← map_sub]
  change ‖b.repr (K.orthogonalProjectionOnto (x - y))‖ ≤ ‖x - y‖
  rw [b.repr.norm_map]
  calc
    ‖K.orthogonalProjectionOnto (x - y)‖ ≤ ‖K.orthogonalProjectionOnto‖ * ‖x - y‖ :=
      K.orthogonalProjectionOnto.le_opNorm _
    _ ≤ 1 * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right K.orthogonalProjectionOnto_norm_le (norm_nonneg _)
    _ = _ := one_mul _

/-- The finite data matrix has the same quadratic compression bound. -/
theorem finite_moment_gramian_error (b : OrthonormalBasis ι ℝ K)
    (F G : E →L[ℝ] H) (hG : ∀ x, G x ∈ K) :
    ‖gram F - gram (momentObservation K b F)‖ ≤ ‖F - G‖^2 := by
  rw [momentObservation_gram]
  exact moment_gramian_error K F G hG

end FiniteMoments

#print axioms gram_perturbation
#print axioms gram_projection_residual
#print axioms moment_gramian_error
#print axioms moments_noise_contraction
#print axioms finite_moment_gramian_error
end D5.S3.Observer.Linear.MomentGramianStability
