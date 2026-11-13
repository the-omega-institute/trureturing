/- GID: D5/S3/Quantum/Foundation/CommonSourceLiftObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/CommonSourceLiftObstruction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Local singleton labels control entire moving original exclusion fibers. -/

import D5.S3.Quantum.Foundation.UniqueConfirmationDensity
import D5.S3.Quantum.Foundation.ExclusionIncidence
import D5.S3.Quantum.Foundation.FixedZeroObstruction

/-! The state body, effects, pure labels and norms are the original ones. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.CommonSourceLiftObstruction

open Set Filter Topology
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ContinuousFrameSum SingleLabelNormalBody ExclusionIncidence
open UniqueConfirmationDensity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- A mixed limit in the relative interior of a single-label ball forces every
convergent choice from the entire moving exclusions to limit to that label. -/
theorem single_label_mixed_upper_limit
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (r : ℕ → pure C u) (hr : Tendsto (fun n => (r n : V)) atTop (𝓝 y))
    {x : V} {xn : ℕ → V} (hxn : ∀ n, xn n ∈ exclusion C u (r n))
    (hx : Tendsto xn atTop (𝓝 x)) : x = (p : V) := by
  classical
  have hall := (exclusion_ball_faces hc hs hg hB).1
  choose e he hz using fun n => (hall (r n)).2.2.2.2.2.2
  let ec (n : ℕ) : V →L[ℝ] ℝ := (e n).toContinuousLinearMap
  obtain ⟨f, hf, φ, hφ, hfe⟩ :=
    (effects_compact hs hg).tendsto_subseq
      (fun n => show ec n ∈ effects C u from (he n).1)
  have heval : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have hfy : f y = 1 := by
    have ht := (heval.tendsto (f, y)).comp
      (hfe.prodMk_nhds (hr.comp hφ.tendsto_atTop))
    have heq : (fun n => (e (φ n)) (r (φ n))) = fun _ : ℕ => (1 : ℝ) :=
      funext fun n => (he (φ n)).2
    change Tendsto (fun n => (e (φ n)) (r (φ n))) atTop (𝓝 (f y)) at ht
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hfx : f x = 0 := by
    have ht := (heval.tendsto (f, x)).comp
      (hfe.prodMk_nhds (hx.comp hφ.tendsto_atTop))
    have heq : (fun n => (e (φ n)) (xn (φ n))) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact (show xn (φ n) ∈ {z | z ∈ base C u ∧ e (φ n) z = 0}
        from hz _ ▸ hxn _).2
    change Tendsto (fun n => (e (φ n)) (xn (φ n))) atTop (𝓝 (f x)) at ht
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hone (z : V) (hzF : z ∈ exclusion C u p) : f z = 1 := by
    have hh := zero_on_exclusion_of_zero_interior hB p (u - f.toLinearMap)
      (fun z hzC => sub_nonneg.mpr (hf z hzC).2) hy
      (by change u y - f y = 0; rw [(intrinsicInterior_subset hy).1.2, hfy]; ring) z hzF
    change u z - f z = 0 at hh
    rw [hzF.1.2] at hh
    linarith
  have hxK : x ∈ base C u := (base_compact hc hs).isClosed.mem_of_tendsto hx
    (Eventually.of_forall fun n => (hxn n).1)
  have hxD (a : pure C u) (ha : (a : V) ∈ exclusion C u p) :
      x ∈ exclusion C u a := ⟨hxK, f.toLinearMap, ⟨hf, hone a ha⟩, hfx⟩
  obtain ⟨a, b, ha, hb, hab⟩ := pure_pair_in_ball hc hs hg hB p
  by_contra hxp
  have heq : exclusion C u a = exclusion C u b :=
    equal_of_two_points hc hs hg hB a b hxp
      ⟨hxD a ha, hxD b hb⟩
      ⟨(exclusion_symmetric p a).mp ha, (exclusion_symmetric p b).mp hb⟩
  exact hab ((single_label_neighbor hc hs hg hB p a hp ha) b heq.symm).symm

/-- Uniform shrinking of each entire original exclusion, without global
injectivity or any common ball dimension. -/
theorem single_label_mixed_shrinking
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (r : ℕ → pure C u) (hr : Tendsto (fun n => (r n : V)) atTop (𝓝 y))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ exclusion C u (r n), ‖x - (p : V)‖ < ε := by
  classical
  by_contra h
  have hb : ∃ᶠ n in atTop, ∃ x ∈ exclusion C u (r n), ε ≤ ‖x - (p : V)‖ := by
    apply (not_eventually.mp h).mono
    intro n hn
    push Not at hn
    exact hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hb
  choose x hx hfar using hbad
  obtain ⟨z, _, ψ, hψ, hxz⟩ :=
    (base_compact hc hs).tendsto_subseq (fun n => (hx n).1)
  have hzp : z = (p : V) := single_label_mixed_upper_limit hc hs hg hB p hp hy
    (fun n => r (φ (ψ n))) (hr.comp (hφ.comp hψ).tendsto_atTop)
    (fun n => hx (ψ n)) hxz
  have hnear : ∀ᶠ n in atTop, dist (x (ψ n)) (p : V) < ε :=
    (Metric.tendsto_nhds.mp (hzp ▸ hxz)) ε hε
  obtain ⟨n, hn⟩ := hnear.exists
  exact (hfar (ψ n)).not_gt (by simpa [dist_eq_norm] using hn)

end D5.S3.Quantum.Foundation.CommonSourceLiftObstruction
