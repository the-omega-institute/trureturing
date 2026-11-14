/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeQuantumConsumer
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeQuantumConsumer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original arbitrary unit retains full compact effects and attained whole-cone confirmation. -/

import D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness

noncomputable section
open Set
open D5.S3.Quantum.Foundation
open CircuitBalancedConfirmation ContinuousFrameSum ExclusionWidthCompactness
namespace D5.S3.Geometry.AlgebraicBoundary.ConeQuantumConsumer

open private comparison_attained
  from D5.S3.Quantum.Foundation.ExclusionWidthCompactness

private theorem original_quantum_consumer {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : ProperCone ℝ E) (hfull : (interior (C : Set E)).Nonempty)
    (u : E →L[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x) :
    IsCompact (base C.toPointedCone u.toLinearMap) ∧
    IsCompact (effects C.toPointedCone u.toLinearMap) ∧
    (∀ p : pure C.toPointedCone u.toLinearMap,
      IsCompact (confirmingEffects C.toPointedCone u.toLinearMap p) ∧
      (confirmingEffects C.toPointedCone u.toLinearMap p).Nonempty) ∧
    ∀ (p : pure C.toPointedCone u.toLinearMap) (x : E), x ∈ C →
      ∃ f : E →L[ℝ] ℝ, f ∈ confirmingEffects C.toPointedCone u.toLinearMap p ∧
        comparison C.toPointedCone u.toLinearMap p x = f x ∧
        ∀ g : E →L[ℝ] ℝ, g ∈ confirmingEffects C.toPointedCone u.toLinearMap p →
          f x ≤ g x := by
  have hg : Submodule.span ℝ (C : Set E) = ⊤ := by
    have ha := C.convex.interior_nonempty_iff_affineSpan_eq_top.mp hfull
    apply top_unique
    intro x hx
    have hx' : x ∈ affineSpan ℝ (C : Set E) := by rw [ha]; trivial
    have hspan : affineSpan ℝ (C : Set E) =
        (Submodule.span ℝ (C : Set E) : AffineSubspace ℝ E) :=
      affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ (C : Set E) C.toPointedCone.zero_mem)
    rw [hspan] at hx'
    exact hx'
  have he := effects_compact hu hg
  refine ⟨base_compact C.isClosed hu, he, ?_, ?_⟩
  · intro p
    refine ⟨he.inter_right (isClosed_eq (by fun_prop) continuous_const), ?_⟩
    refine ⟨u, ?_, (pure_mem p).2⟩
    intro x hx
    refine ⟨?_, le_rfl⟩
    by_cases hz : x = 0
    · simp [hz]
    · exact (hu x hx hz).le
  · intro p x hx
    obtain ⟨f, hf, hfx⟩ := comparison_attained hu hg p x
    refine ⟨f, hf, hfx, ?_⟩
    intro g hg
    have hb : BddBelow {r | ∃ f, confirms C.toPointedCone u.toLinearMap p f ∧ f x = r} :=
      ⟨0, fun r ⟨a, ha, har⟩ => har ▸ (ha.1 x hx).1⟩
    rw [← hfx]
    exact csInf_le hb ⟨g.toLinearMap, hg, rfl⟩

end D5.S3.Geometry.AlgebraicBoundary.ConeQuantumConsumer
