/- GID: D5/S3/Quantum/Foundation/FixedZeroObstruction/LocalPureLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FixedZeroObstruction/LocalPureLimit
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Local single-label mixed limits collapse entire original exclusions. -/

import D5.S3.Quantum.Foundation.FixedZeroObstruction
import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.UniqueConfirmationDensity

/-! Original mixed interior limits under uniqueness of just the fixed label. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.FixedZeroObstruction

open Set Filter Topology TopologicalSpace
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ContinuousFrameSum ExclusionIncidence OriginalFacePolarity SingleLabelNormalBody

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Maximum distance of the entire original exclusion from one ambient point. -/
def exclusionRadius (p : V) (r : pure C u) : ℝ :=
  sSup ((fun x : V => ‖x - p‖) '' exclusion C u r)

private theorem local_return_limit
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p) {y : V}
    (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (rn : ℕ → pure C u) (hr : Tendsto (fun n => (rn n : V)) atTop (𝓝 y))
    {xn : ℕ → V} {x : V} (hx : Tendsto xn atTop (𝓝 x))
    (hxn : ∀ n, xn n ∈ exclusion C u (rn n)) : x = p := by
  have all := (exclusion_ball_faces hc hs hg hB).1
  choose e he hz using fun n => (all (rn n)).2.2.2.2.2.2
  obtain ⟨b, hb, φ, hφ, heb⟩ := (effects_compact hs hg).tendsto_subseq
    (fun n => (show (e n).toContinuousLinearMap ∈ effects C u from (he n).1))
  have ev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have hby : b y = 1 := by
    apply tendsto_nhds_unique ((ev.tendsto (b, y)).comp
      (heb.prodMk_nhds (hr.comp hφ.tendsto_atTop)))
    change Tendsto (fun n => e (φ n) (rn (φ n))) atTop (𝓝 1)
    simpa only [(he _).2] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hbx : b x = 0 := by
    apply tendsto_nhds_unique ((ev.tendsto (b, x)).comp
      (heb.prodMk_nhds (hx.comp hφ.tendsto_atTop)))
    have hzero (n : ℕ) : e (φ n) (xn (φ n)) = 0 := (hz (φ n) ▸ hxn (φ n)).2
    change Tendsto (fun n => e (φ n) (xn (φ n))) atTop (𝓝 0)
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hxK := (base_compact hc hs).isClosed.mem_of_tendsto hx
    (Eventually.of_forall fun n => (hxn n).1)
  have hz := UniqueConfirmationDensity.zero_on_exclusion_of_zero_interior hB p
    (u - b.toLinearMap) (fun z hz => sub_nonneg.mpr (hb z hz).2) hy
    (by simp [LinearMap.sub_apply, (intrinsicInterior_subset hy).1.2, hby])
  have hone (z : V) (hzF : z ∈ exclusion C u p) : b z = 1 := by
    have h := hz z hzF
    simp only [LinearMap.sub_apply, ContinuousLinearMap.coe_coe, hzF.1.2] at h
    linarith
  obtain ⟨a, a', ha, ha', hne⟩ := pure_pair_in_ball hc hs hg hB p
  have hxa : x ∈ exclusion C u a := ⟨hxK, b.toLinearMap, ⟨hb, hone a ha⟩, hbx⟩
  have hxa' : x ∈ exclusion C u a' := ⟨hxK, b.toLinearMap, ⟨hb, hone a' ha'⟩, hbx⟩
  by_contra hxp
  have heq := equal_of_two_points hc hs hg hB a a' hxp ⟨hxa, hxa'⟩
    ⟨(exclusion_symmetric p a).mp ha, (exclusion_symmetric p a').mp ha'⟩
  exact hne ((single_label_neighbor hc hs hg hB p a hp ha) a' heq.symm).symm

/-- Local uniqueness at the fixed source ball suffices at a mixed interior limit;
the maximum ranges over the whole moving exclusion and all ball dimensions. -/
theorem local_single_label_collapse
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p) {y : V}
    (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (rn : ℕ → pure C u) (hr : Tendsto (fun n => (rn n : V)) atTop (𝓝 y)) :
    Tendsto (fun n => exclusionRadius (p : V) (rn n)) atTop (𝓝 0) := by
  have all := (exclusion_ball_faces hc hs hg hB).1
  choose xn hxn heq using fun n => (all (rn n)).2.1.exists_sSup_image_eq
    (all (rn n)).1.nonempty (by fun_prop : ContinuousOn (fun x : V => ‖x - (p : V)‖) _)
  have hxt : Tendsto xn atTop (𝓝 (p : V)) := by
    apply (base_compact hc hs).tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun n => (hxn n).1)
    intro x _ hcluster
    obtain ⟨φ, hφ, hφx⟩ := hcluster.tendsto_subseq
    exact local_return_limit hc hs hg hB p hp hy (fun n => rn (φ n))
      (hr.comp hφ.tendsto_atTop) hφx (fun n => hxn (φ n))
  have hnorm := (hxt.sub_const (p : V)).norm
  simpa only [sub_self, norm_zero, exclusionRadius, heq] using hnorm

end D5.S3.Quantum.Foundation.FixedZeroObstruction
