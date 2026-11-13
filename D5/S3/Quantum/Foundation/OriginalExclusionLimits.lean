/- GID: D5/S3/Quantum/Foundation/OriginalExclusionLimits
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalExclusionLimits
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Actual original ball-parameter limits have full rank or are pure singleton exclusions. -/

import D5.S3.Quantum.Foundation.OriginalPureCompactness
import D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse

/-! Parameter limits retain every mixed point and the entire original sphere. -/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.OriginalExclusionLimits
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces OriginalFacePolarity
open ExclusionIncidence OriginalPureCompactness ExclusionUniformNoncollapse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- An actual original parameter limit is either injective in all three
directions or has zero linear part and is a pure point of the entire D(p).
Every mixed limit point remains in the actual full D(p). -/
theorem original_parameter_limit_rank
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (p : pure C u) (pn : ℕ → pure C u) (hp : Tendsto pn atTop (𝓝 p))
    (b : ℕ → EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] V)
    (hi : ∀ n, Function.Injective (b n))
    (hw : ∀ n, b n '' Metric.closedBall 0 1 = exclusion C u (pn n))
    (c : V) (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] V)
    (ht : Tendsto (fun n => (b n 0, (b n).linear.toContinuousLinearMap))
      atTop (𝓝 (c,A))) :
    (∀ z, ‖z‖ ≤ 1 → c + A z ∈ exclusion C u p) ∧
    (Function.Injective A ∨ A = 0 ∧ c ∈ pure C u ∧ c ∈ exclusion C u p) := by
  have hval (z : EuclideanSpace ℝ (Fin 3)) :
      Tendsto (fun n => b n z) atTop (𝓝 (c + A z)) := by
    have he (n : ℕ) : b n z = b n 0 + (b n).linear.toContinuousLinearMap z := by
      have hh := congrFun (b n).decomp z
      change b n z = (b n).linear z + b n 0 at hh
      exact hh.trans (add_comm _ _)
    simp_rw [he]
    exact ((continuous_fst.add (continuous_snd.clm_apply continuous_const)).tendsto (c,A)).comp ht
  have hsub : ∀ z, ‖z‖ ≤ 1 → c + A z ∈ exclusion C u p := by
    intro z hz
    exact exclusion_upper_limit hc hs hg hp (hval z)
      (fun n => hw n ▸ mem_image_of_mem (b n) (by simpa using hz))
  have hP := (original_pr_pure_compact hc hs hg hB hPR).isClosed
  have hsphere (z : EuclideanSpace ℝ (Fin 3)) (hz : ‖z‖ = 1) : c + A z ∈ pure C u := by
    apply hP.mem_of_tendsto (hval z)
    apply Eventually.of_forall
    intro n
    let a : ExclusionChart C u (pn n) := ⟨3, by norm_num, b n, hi n, hw n⟩
    exact ((chart_boundary hc hs hg hB (pn n) a).symm ▸
      (show b n z ∈ a.param '' Metric.sphere 0 1 from ⟨z, by simpa using hz, rfl⟩)).2
  refine ⟨hsub, ?_⟩
  rcases sphere_extreme_injective_or_zero (base C u) c A hsphere with h | h
  · exact Or.inl h
  · right
    have hzero : c ∈ exclusion C u p := by simpa using hsub 0 (by simp)
    have hpure : c ∈ pure C u := by
      have hh := hsphere (EuclideanSpace.single (0 : Fin 3) 1) (by simp [EuclideanSpace.single])
      simpa [h] using hh
    exact ⟨h, hpure, hzero⟩

#print axioms original_parameter_limit_rank

end D5.S3.Quantum.Foundation.OriginalExclusionLimits
