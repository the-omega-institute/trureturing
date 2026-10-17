import D5.S3.Analytic.Convexity.CFMPTransientFullPotentialExact
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Separate, unexecuted source sanity applications. These invoke the final consumer;
they do not supply independently constructed inverse fields or primitives.
All declarations are temporary and carry no validation/admission claim.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace CFMP147Transient.Sanity

/-- Arbitrary ambient F on the empty original domain; no basepoint is chosen. -/
theorem empty_domain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : E → E) :
    ∃ P : E → ℝ,
      (∀ x ∈ (∅ : Set E), HasFDerivAt P (innerSL ℝ (F x)) x) ∧
      ConvexOn ℝ (∅ : Set E) P := by
  apply CFMP147Transient.exists_full_potential (D := ∅) (U := ∅) (F := F)
    isOpen_empty convex_empty (continuousOn_empty F)
  · intro x hx
    exact False.elim hx
  · intro x hx
    exact False.elim hx
  · simp

/-- A genuinely zero-dimensional ambient space and the nonempty domain univ.
F is arbitrary and U is empty. Finite exceptional image is proved directly;
neither a point of the domain nor an inverse nor a primitive is an input. -/
theorem dimension_zero
    (F : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0 ∧
    ∃ P : EuclideanSpace ℝ (Fin 0) → ℝ,
      (∀ x ∈ (univ : Set (EuclideanSpace ℝ (Fin 0))),
        HasFDerivAt P (innerSL ℝ (F x)) x) ∧
      ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin 0))) P := by
  have hFzero : F = fun _ => 0 := by
    funext x
    exact PiLp.ext (fun i => Fin.elim0 i)
  refine ⟨finrank_euclideanSpace_fin, ?_⟩
  apply CFMP147Transient.exists_full_potential
    (D := univ) (U := ∅) (F := F) isOpen_univ convex_univ
  · rw [hFzero]
    exact continuous_const.continuousOn
  · intro x hx y hy
    rw [congrFun hFzero x, congrFun hFzero y]
    simp
  · intro x hx
    exact False.elim hx
  · apply (Set.finite_singleton (0 : EuclideanSpace ℝ (Fin 0))).subset
    rintro z ⟨x, hx, rfl⟩
    exact Set.mem_singleton_iff.mpr (congrFun hFzero x)

/-- Only the concrete sanity field, not an additional mathematical supplier. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- ReLU has an actual corner at zero, an exactly singleton exceptional image,
and nevertheless the final consumer supplies its convex differentiable potential
on all of the original domain. In particular, zero is included in the conclusion. -/
theorem relu_application :
    (¬ DifferentiableAt ℝ relu 0) ∧
    relu '' ((univ : Set ℝ) \ {x : ℝ | x ≠ 0}) = {0} ∧
    ∃ P : ℝ → ℝ,
      (∀ x ∈ (univ : Set ℝ), HasFDerivAt P (innerSL ℝ (relu x)) x) ∧
      ConvexOn ℝ (univ : Set ℝ) P := by
  have hOrder : Monotone relu := by
    intro x y hxy
    exact max_le_max le_rfl hxy
  have hMono : ∀ x ∈ (univ : Set ℝ), ∀ y ∈ (univ : Set ℝ),
      0 ≤ inner ℝ (relu x - relu y) (x - y) := by
    intro x hx y hy
    rw [Real.inner_apply]
    rcases le_total y x with hle | hle
    · exact mul_nonneg (sub_nonneg.mpr (hOrder hle)) (sub_nonneg.mpr hle)
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hOrder hle)) (sub_nonpos.mpr hle)
  have hDeriv : ∀ x ∈ {x : ℝ | x ≠ 0}, ∃ A : ℝ →L[ℝ] ℝ,
      HasFDerivAt relu A x ∧ ∀ u v, inner ℝ (A u) v = inner ℝ u (A v) := by
    intro x hx
    change x ≠ 0 at hx
    rcases hx.lt_or_gt with hneg | hpos
    · refine ⟨0, ?_, ?_⟩
      · apply (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds hneg] with y hy
        exact max_eq_left hy.le
      · intro u v
        simp
    · refine ⟨ContinuousLinearMap.id ℝ ℝ, ?_, ?_⟩
      · apply (hasFDerivAt_id x).congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hpos] with y hy
        exact max_eq_right hy.le
      · intro u v
        rfl
  have hExceptional : relu '' ((univ : Set ℝ) \ {x : ℝ | x ≠ 0}) = {0} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x = 0 := by simpa only [mem_setOf_eq, not_not] using hx.2
      simp [hx0, relu]
    · intro hz
      have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
      subst z
      refine ⟨0, ⟨Set.mem_univ _, ?_⟩, ?_⟩ <;> simp [relu]
  have hNotDiff : ¬ DifferentiableAt ℝ relu 0 := by
    intro hd
    have hAbs : (fun x : ℝ => 2 * relu x - x) = (abs : ℝ → ℝ) := by
      funext x
      rcases le_total 0 x with hx | hx
      · simp only [relu, max_eq_right hx, abs_of_nonneg hx]
        ring
      · simp only [relu, max_eq_left hx, abs_of_nonpos hx]
        ring
    have hdAbs : DifferentiableAt ℝ (fun x : ℝ => 2 * relu x - x) 0 :=
      (hd.const_mul 2).sub differentiableAt_id
    rw [hAbs] at hdAbs
    exact not_differentiableAt_abs_zero hdAbs
  refine ⟨hNotDiff, hExceptional, ?_⟩
  apply CFMP147Transient.exists_full_potential
    (D := univ) (U := {x : ℝ | x ≠ 0}) (F := relu)
    isOpen_univ convex_univ
  · exact (continuous_const.max continuous_id).continuousOn
  · exact hMono
  · exact hDeriv
  · rw [hExceptional]
    exact Set.finite_singleton 0

end CFMP147Transient.Sanity

end
