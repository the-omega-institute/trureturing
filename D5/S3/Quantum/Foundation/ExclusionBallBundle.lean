/- GID: D5/S3/Quantum/Foundation/ExclusionBallBundle
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionBallBundle
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original saturated three-ball exclusions vary continuously as whole compact sets. -/

import D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse
import D5.S3.Quantum.Foundation.ExclusionIncidence
import D5.S3.Geometry.AffineBallRigidity

/-! The original-domain continuity step for the entire Q1 exclusion family. -/

noncomputable section
open Set Metric Filter Topology TopologicalSpace

namespace D5.S3.Quantum.Foundation.ExclusionBallBundle

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ExclusionWidthCompactness ExclusionIncidence

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]
  {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The entire original exclusion as a nonempty compact subset of the original carrier. -/
def wholeExclusion (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : NonemptyCompacts V :=
  ⟨⟨exclusion C u p, ((exclusion_ball_faces hc hs hg hB).1 p).2.1⟩,
    ((exclusion_ball_faces hc hs hg hB).1 p).1.nonempty⟩

omit [FiniteDimensional ℝ V] [Nontrivial V] in
private theorem three_chart_data
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) :
    ∃ f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] V,
      Function.Injective f ∧ f '' closedBall 0 1 = exclusion C u p := by
  obtain ⟨⟨d, hd, f, hfi, hfw⟩, he⟩ := hEB3 p
  dsimp only at he
  subst d
  exact ⟨f, hfi, hfw⟩

/-- Q1 gives Hausdorff continuity of the entire original mixed-point exclusions.
There is no edge-lifting, continuous-chart-choice or pure-closedness premise. -/
theorem whole_exclusion_continuous
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1) :
    Continuous (wholeExclusion hc hs hg (fun p => ⟨(hEB3 p).choose⟩)) := by
  classical
  let hB : exclusionBalls C u := fun p => ⟨(hEB3 p).choose⟩
  have hP : IsClosed (pure C u) := by
    have he : {x | x ∈ pure C u ∧ width C u (exclusion C u x) = 1} = pure C u := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, hW1 ⟨x, h⟩⟩⟩
    rw [← he]
    exact (saturated_labels_compact hc hs hg hB).isClosed
  obtain ⟨η, hη, hlower⟩ :=
    ExclusionUniformNoncollapse.all_label_uniform_noncollapse hc hs hg hEB3 hW1
  choose f hfi hfw using three_chart_data hEB3
  let A (p : pure C u) : EuclideanSpace ℝ (Fin 3) →L[ℝ] V :=
    (f p).linear.toContinuousLinearMap
  let c (p : pure C u) : V := f p 0
  have hf (p : pure C u) (x : EuclideanSpace ℝ (Fin 3)) :
      f p x = c p + A p x := by
    simpa [c, A, add_comm] using congrFun (f p).decomp x
  have hball (p : pure C u) : ballImage (c p) (A p) = wholeExclusion hc hs hg hB p := by
    apply NonemptyCompacts.ext
    change (fun x => c p + A p x) '' closedBall 0 1 = exclusion C u p
    simpa only [← hf] using hfw p
  have hb (p : pure C u) (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 1) :
      c p + A p x ∈ base C u := by
    rw [← hf]
    exact (hfw p ▸ mem_image_of_mem (f p) (mem_closedBall_zero_iff.mpr hx)).1
  have hsp (p : pure C u) (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
      c p + A p x ∈ pure C u := by
    let ha : ExclusionChart C u p := ⟨3, by decide, f p, hfi p, hfw p⟩
    have he := OriginalFacePolarity.chart_boundary hc hs hg hB p ha
    have hh : f p x ∈ ha.param '' sphere 0 1 := ⟨x, by simpa using hx, rfl⟩
    rw [← he] at hh
    simpa [hf] using hh.2
  have hl (p : pure C u) (x : EuclideanSpace ℝ (Fin 3)) :
      η * ‖x‖ ≤ ‖A p x‖ :=
    hlower p ⟨3, by decide, f p, hfi p, hfw p⟩ rfl x
  obtain ⟨R, hR, hKR⟩ := (base_compact hc hs).isBounded.exists_pos_norm_le
  have hparam (p : pure C u) :
      (c p, A p) ∈ closedBall (0 : V × (EuclideanSpace ℝ (Fin 3) →L[ℝ] V)) (2 * R) := by
    have hcc : ‖c p‖ ≤ R := by simpa using hKR _ (hb p 0 (by simp))
    have hAA : ‖A p‖ ≤ 2 * R := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
      intro x hx
      have hh := norm_sub_le (c p + A p x) (c p)
      rw [add_sub_cancel_left] at hh
      exact hh.trans (by linarith [hKR _ (hb p x hx.le)])
    simpa only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using
      And.intro (hcc.trans (by linarith)) hAA
  apply continuous_iff_seqContinuous.mpr
  intro pn p hp
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨t, ht, ms, hms, htm⟩ :=
    (isCompact_closedBall (0 : V × (EuclideanSpace ℝ (Fin 3) →L[ℝ] V)) (2 * R)).tendsto_subseq
      (fun n => hparam (pn (ns n)))
  have hct := (continuous_fst.tendsto t).comp htm
  have hAt := (continuous_snd.tendsto t).comp htm
  have heval (x : EuclideanSpace ℝ (Fin 3)) :
      Tendsto (fun n => c (pn (ns (ms n))) + A (pn (ns (ms n))) x) atTop
        (𝓝 (t.1 + t.2 x)) := by
    exact hct.add ((show Continuous (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] V => L x)
      by fun_prop).tendsto _ |>.comp hAt)
  have hlt (x : EuclideanSpace ℝ (Fin 3)) : η * ‖x‖ ≤ ‖t.2 x‖ :=
    ge_of_tendsto (continuous_norm.tendsto _ |>.comp
      ((show Continuous (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] V => L x)
        by fun_prop).tendsto _ |>.comp hAt))
      (Eventually.of_forall fun n => hl (pn (ns (ms n))) x)
  have hinj : Function.Injective t.2 := by
    apply (injective_iff_map_eq_zero t.2).mpr
    intro x hx
    have hh := hlt x
    rw [hx, norm_zero] at hh
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
  have hlimit (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 1) :
      t.1 + t.2 x ∈ exclusion C u p := by
    apply exclusion_upper_limit hc hs hg
      (hp.comp (hns.comp hms.tendsto_atTop)) (heval x)
    intro n
    rw [← hf]
    exact hfw _ ▸ mem_image_of_mem (f _) (mem_closedBall_zero_iff.mpr hx)
  have hspt (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
      t.1 + t.2 x ∈ (base C u).extremePoints ℝ :=
    hP.mem_of_tendsto (heval x) (Eventually.of_forall fun n => hsp _ x hx)
  have heq : ballImage t.1 t.2 = wholeExclusion hc hs hg hB p := by
    apply NonemptyCompacts.ext
    change (fun x => t.1 + t.2 x) '' closedBall 0 1 = exclusion C u p
    rw [← hfw p]
    have hApi : Function.Injective (A p) := by
      intro x y h
      apply hfi p
      rw [hf, hf, h]
    have hgeom := D5.S3.Geometry.AffineBallRigidity.eq_of_subset_of_extreme_sphere
      (base C u) t.1 (c p) t.2 (A p) hinj hApi
      (by
        rintro y ⟨x, hx, rfl⟩
        have hh : t.1 + t.2 x ∈ f p '' closedBall 0 1 :=
          (hfw p).symm ▸ hlimit x (mem_closedBall_zero_iff.mp hx)
        simpa only [hf] using hh)
      (by rintro y ⟨x, hx, rfl⟩; exact hb p x (mem_closedBall_zero_iff.mp hx)) hspt
    simpa only [hf] using hgeom
  refine ⟨ms, ?_⟩
  have hcont : Continuous (fun z : V × (EuclideanSpace ℝ (Fin 3) →L[ℝ] V) =>
      ballImage z.1 z.2) :=
    Continuous.nonemptyCompacts_map' continuous_const (by fun_prop)
  have hconv := (hcont.tendsto t).comp htm
  simpa only [hball, heq, Function.comp_def] using hconv

#print axioms whole_exclusion_continuous

/-- The center remains a point of the original normalized affine carrier. -/
def chartCenter
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) : V := (hEB3 p).choose.param 0

/-- The intrinsic centers of the entire original balls are continuous, lie in K,
and agree with the centers of every entire affine ball chart. -/
theorem original_center_continuous
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1) :
    Continuous (chartCenter hEB3) ∧
      ∀ p : pure C u, chartCenter hEB3 p ∈ base C u ∧
        ∀ a : ExclusionChart C u p, a.param 0 = chartCenter hEB3 p := by
  classical
  let hB : exclusionBalls C u := fun p => ⟨(hEB3 p).choose⟩
  have hdecomp (p : V) (a : ExclusionChart C u p) (x) :
      a.param x = a.param 0 + a.param.linear.toContinuousLinearMap x := by
    simpa [add_comm] using congrFun a.param.decomp x
  have hcen (p : pure C u) (a : ExclusionChart C u p) :
      a.param 0 = chartCenter hEB3 p := by
    apply D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq
      (a.param 0) ((hEB3 p).choose.param 0)
      a.param.linear.toContinuousLinearMap (hEB3 p).choose.param.linear.toContinuousLinearMap
    simpa only [← hdecomp] using a.whole.trans (hEB3 p).choose.whole.symm
  refine ⟨?_, fun p => ⟨?_, hcen p⟩⟩
  · choose f hfi hfw using three_chart_data hEB3
    let c (p : pure C u) := f p 0
    let A (p : pure C u) := (f p).linear.toContinuousLinearMap
    have hf (p : pure C u) (x : EuclideanSpace ℝ (Fin 3)) :
        f p x = c p + A p x := by
      simpa [c, A, add_comm] using congrFun (f p).decomp x
    have hball (p : pure C u) : ballImage (c p) (A p) = wholeExclusion hc hs hg hB p := by
      apply NonemptyCompacts.ext
      change (fun x => c p + A p x) '' closedBall 0 1 = exclusion C u p
      simpa only [← hf] using hfw p
    have hcc (p : pure C u) : c p = chartCenter hEB3 p :=
      hcen p ⟨3, by decide, f p, hfi p, hfw p⟩
    apply continuous_iff_seqContinuous.mpr
    intro pn p hp
    apply tendsto_of_subseq_tendsto
    intro ns hns
    have ht : Tendsto (fun n => ballImage (c (pn (ns n))) (A (pn (ns n)))) atTop
        (𝓝 (ballImage (c p) (A p))) := by
      simpa only [hball, Function.comp_def] using
        ((whole_exclusion_continuous hc hs hg hEB3 hW1).tendsto p).comp (hp.comp hns)
    obtain ⟨t, ms, hms, htm, heq⟩ := parameter_subsequence
      (fun n => c (pn (ns n))) (fun n => A (pn (ns n))) (ballImage (c p) (A p)) ht
    have htc : t.1 = c p :=
      D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq _ _ _ _
        (congrArg (fun S : NonemptyCompacts V => (S : Set V)) heq)
    refine ⟨ms, ?_⟩
    have hh := (continuous_fst.tendsto t).comp htm
    simpa only [Function.comp_def, htc, hcc] using hh
  · let a := (hEB3 p).choose
    have hx : a.param 0 ∈ a.param '' closedBall 0 1 := ⟨0, by simp, rfl⟩
    rw [a.whole] at hx
    exact hx.1

#print axioms original_center_continuous

end D5.S3.Quantum.Foundation.ExclusionBallBundle
