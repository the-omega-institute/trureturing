/- GID: D5/S3/Quantum/Foundation/OriginalComparisonTopology
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalComparisonTopology
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Uniform mixed-input continuity and pure joint continuity on the original carrier. -/

import D5.S3.Quantum.Foundation.OriginalBallScale

/-! The pure reciprocity law is used only to exchange pure endpoints. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalComparisonTopology
open CircuitBalancedConfirmation ContinuousFrameSum ExclusionWidthCompactness
open FacetZeroGluing ExclusionBallFaces OriginalFacePolarity OriginalBallScale

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem comparison_le_confirmer
    {p : pure C u} {x : V} (hx : x ∈ base C u)
    {f : V →L[ℝ] ℝ} (hf : f ∈ confirmingEffects C u p) :
    comparison C u p x ≤ f x :=
  csInf_le ⟨0, by rintro r ⟨g, hg, rfl⟩; exact (hg.1 x hx.1).1⟩
    ⟨f.toLinearMap, hf, rfl⟩

/-- One finite positive Lipschitz bound covers every pure row and every pair
of mixed inputs in the whole original normalized base. -/
theorem original_uniform_comparison
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ L : ℝ, 0 < L ∧ ∀ p : pure C u, ∀ x ∈ base C u, ∀ y ∈ base C u,
      |comparison C u p x - comparison C u p y| ≤ L * ‖x - y‖ := by
  obtain ⟨R, hR⟩ := (effects_compact hs hg).isBounded.exists_norm_le
  let L := |R| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hbound (f : V →L[ℝ] ℝ) (hf : f ∈ effects C u) (x y : V) :
      f x - f y ≤ L * ‖x-y‖ := by
    calc
      f x - f y = f (x-y) := (map_sub f x y).symm
      _ ≤ ‖f (x-y)‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖x-y‖ := f.le_opNorm _
      _ ≤ L * ‖x-y‖ := mul_le_mul_of_nonneg_right
        ((hR f hf).trans (by dsimp [L]; linarith [le_abs_self R])) (norm_nonneg _)
  have hdiff (p : pure C u) (x : V) (hx : x ∈ base C u)
      (y : V) (_hy : y ∈ base C u) :
      comparison C u p x - comparison C u p y ≤ L * ‖x-y‖ := by
    obtain ⟨f, hf, he⟩ := comparison_attained hs hg p y
    rw [he]
    exact (sub_le_sub_right (comparison_le_confirmer hx hf) _).trans (hbound f hf.1 x y)
  refine ⟨L, hL, ?_⟩
  intro p x hx y hy
  exact abs_le.mpr ⟨by
    have hh := hdiff p y hy x hx
    rw [norm_sub_rev] at hh
    linarith, hdiff p x hx y hy⟩

/-- Original pure reciprocity gives joint continuity on all pure labels,
without a mixed-state reciprocity law or a closed-pure-carrier premise. -/
theorem original_joint_pure_comparison
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    ∃ L : ℝ, 0 < L ∧ ∀ p q s t : pure C u,
      |comparison C u p s - comparison C u q t| ≤
        L * (‖(p : V) - q‖ + ‖(s : V) - t‖) := by
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  refine ⟨L, hL, ?_⟩
  intro p q s t
  have hfirst := hbound s p (pure_mem p) q (pure_mem q)
  rw [← hPR p s, ← hPR q s] at hfirst
  have hsecond := hbound q s (pure_mem s) t (pure_mem t)
  calc
    _ ≤ |comparison C u p s - comparison C u q s| +
        |comparison C u q s - comparison C u q t| := abs_sub_le _ _ _
    _ ≤ L * ‖(p : V) - q‖ + L * ‖(s : V) - t‖ := add_le_add hfirst hsecond
    _ = _ := by ring

#print axioms original_uniform_comparison
#print axioms original_joint_pure_comparison

end D5.S3.Quantum.Foundation.OriginalComparisonTopology
