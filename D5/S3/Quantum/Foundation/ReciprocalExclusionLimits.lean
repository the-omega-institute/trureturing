/- GID: D5/S3/Quantum/Foundation/ReciprocalExclusionLimits
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ReciprocalExclusionLimits
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Pure reciprocity restricts whole exclusion limits to the old ball or a pure singleton. -/

import D5.S3.Quantum.Foundation.ReciprocalPureCompactness
import D5.S3.Quantum.Foundation.ExclusionIncidence
import D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse
import D5.S3.Quantum.Foundation.FixedZeroObstruction
import D5.S3.Geometry.AffineBallRigidity

/-! Whole three-ball limits in the original carrier. -/
noncomputable section
open Set Filter Topology TopologicalSpace

namespace D5.S3.Quantum.Foundation.ReciprocalExclusionLimits
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ExclusionIncidence ContinuousFrameSum OriginalFacePolarity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- EB3 concerns each entire original exclusion, without fixing the ambient dimension. -/
def threeBallExclusions (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p : pure C u, ∃ f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] V,
    Function.Injective f ∧ f '' Metric.closedBall 0 1 = exclusion C u p

/-- Every actual compact whole-exclusion limit is the old complete ball or
one original pure point of that ball. Rank collapse is retained. -/
theorem exclusion_limit_dichotomy {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    {p : pure C u} {an : ℕ → pure C u} (ha : Tendsto an atTop (𝓝 p))
    (F : ℕ → NonemptyCompacts V) (Q : NonemptyCompacts V)
    (hF : ∀ n, (F n : Set V) = exclusion C u (an n))
    (ht : Tendsto F atTop (𝓝 Q)) :
    (Q : Set V) = exclusion C u p ∨
      ∃ q : pure C u, (q : V) ∈ exclusion C u p ∧ (Q : Set V) = {(q : V)} := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  have hB : exclusionBalls C u := by
    intro q
    obtain ⟨f, hf, hw⟩ := h3 q
    exact ⟨⟨3, by norm_num, f, hf, hw⟩⟩
  choose f hfi hfw using fun n => h3 (an n)
  let c : ℕ → V := fun n => f n 0
  let L : ℕ → E →L[ℝ] V := fun n => (f n).linear.toContinuousLinearMap
  have hrepr (n : ℕ) (x : E) : c n + L n x = f n x := by
    simpa [c, L, add_comm] using (congrFun (f n).decomp x).symm
  have hball (n : ℕ) : ballImage (c n) (L n) = F n := by
    apply NonemptyCompacts.ext
    change (fun x => c n + L n x) '' _ = _
    simp_rw [hrepr]
    exact (hfw n).trans (hF n).symm
  obtain ⟨z, φ, hφ, hz, hzQ⟩ := parameter_subsequence c L Q
    (by simpa only [hball] using ht)
  have hsub : (Q : Set V) ⊆ exclusion C u p := by
    intro y hy
    obtain ⟨yn, hyn, hylim⟩ := FixedZeroObstruction.recover_limit F Q ht hy
    exact exclusion_upper_limit hc hs hg ha hylim (fun n => hF n ▸ hyn n)
  have hsphere (x : E) (hx : ‖x‖ = 1) : z.1 + z.2 x ∈ pure C u := by
    have hpure (n : ℕ) : c n + L n x ∈ pure C u := by
      rw [hrepr]
      let b : ExclusionChart C u (an n) := ⟨3, by norm_num, f n, hfi n, hfw n⟩
      have hb := chart_boundary hc hs hg hB (an n) b
      exact (hb.symm ▸ (show f n x ∈ b.param '' Metric.sphere 0 1 from
        ⟨x, mem_sphere_zero_iff_norm.mpr hx, rfl⟩)).2
    have heval : Continuous (fun t : V × (E →L[ℝ] V) => t.1 + t.2 x) := by fun_prop
    exact (ReciprocalPureCompactness.reciprocal_pure_compact hc hs hg hPR).isClosed.mem_of_tendsto
      ((heval.tendsto z).comp hz) (Eventually.of_forall fun n => hpure (φ n))
  rcases ExclusionUniformNoncollapse.sphere_extreme_injective_or_zero
      (base C u) z.1 z.2 hsphere with hinj | hzero
  · left
    obtain ⟨b, hbi, hbw⟩ := h3 p
    have hbexpr (x : E) : b 0 + b.linear.toContinuousLinearMap x = b x := by
      simpa [add_comm] using (congrFun b.decomp x).symm
    have heq := D5.S3.Geometry.AffineBallRigidity.eq_of_subset_of_extreme_sphere
      (base C u) z.1 (b 0) z.2 b.linear.toContinuousLinearMap hinj
      (b.linear_injective_iff.mpr hbi)
      (by
        change (ballImage z.1 z.2 : Set V) ⊆ _
        rw [hzQ]
        simp_rw [hbexpr]
        rw [hbw]
        exact hsub)
      (by
        simp_rw [hbexpr]
        rw [hbw]
        exact fun x hx => hx.1)
      hsphere
    change (Q : Set V) = exclusion C u p
    rw [← hzQ]
    change (fun x => z.1 + z.2 x) '' _ = _
    rw [heq]
    simp_rw [hbexpr]
    exact hbw
  · right
    obtain ⟨v, hv'⟩ := (NormedSpace.sphere_nonempty (E := E)).mpr (show (0:ℝ) ≤ 1 by norm_num)
    have hv : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv'
    have hzp : z.1 ∈ pure C u := by simpa [hzero] using hsphere v hv
    have heq : (Q : Set V) = {z.1} := by
      rw [← hzQ]
      change (fun x => z.1 + z.2 x) '' Metric.closedBall 0 1 = _
      simp [hzero]
    exact ⟨⟨z.1, hzp⟩, hsub (heq ▸ mem_singleton z.1), heq⟩

end D5.S3.Quantum.Foundation.ReciprocalExclusionLimits
