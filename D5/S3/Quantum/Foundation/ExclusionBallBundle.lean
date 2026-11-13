/- GID: D5/S3/Quantum/Foundation/ExclusionBallBundle
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionBallBundle
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Q1 gives unique continuous affine ellipsoids and their actual metric range bundles. -/

import D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse
import D5.S3.Quantum.Foundation.ExclusionIncidence
import D5.S3.Geometry.AffineBallRigidity
import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Geometry.EllipsoidShape
import D5.S3.Geometry.ContinuousRangeBundle
import D5.S3.Geometry.MetricRangeChart

/-! The entire original Q1 exclusion family as unique continuous affine ellipsoids and metric range bundles. -/



noncomputable section
open Set Metric Filter Topology TopologicalSpace
open scoped InnerProductSpace

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


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

def kernelInclusion (e : u.ker ≃ₗ[ℝ] H) : H →L[ℝ] V :=
  u.ker.subtypeL.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap

def auxiliaryLinear (e : u.ker ≃ₗ[ℝ] H) {p : V} (a : ExclusionChart C u p) :
    EuclideanSpace ℝ (Fin a.dim) →L[ℝ] H :=
  (e.toLinearMap.comp (a.param.linear.codRestrict u.ker
    (fun x =>
      _root_.D5.S3.Quantum.Foundation.SingleLabelNormalBody.chart_unit_linear a x))).toContinuousLinearMap

private theorem inclusion_auxiliaryLinear (e : u.ker ≃ₗ[ℝ] H) {p : V}
    (a : ExclusionChart C u p) (x) :
    kernelInclusion e (auxiliaryLinear e a x) = a.param.linear x := by
  simp [kernelInclusion, auxiliaryLinear]
  rfl

theorem auxiliary_metric_uniform_charts
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1)
    (e : u.ker ≃ₗ[ℝ] H) :
    Continuous e ∧ Continuous e.symm ∧
    Continuous (chartCenter hEB3) ∧
    ∃ η R : ℝ, 0 < η ∧ η ≤ R ∧ 0 < R ∧
      ∀ (p : pure C u) (a : ExclusionChart C u p), a.dim = 3 →
      a.param 0 = chartCenter hEB3 p ∧ u (chartCenter hEB3 p) = 1 ∧
      (∀ x, η * ‖x‖ ≤ ‖auxiliaryLinear e a x‖ ∧
        ‖auxiliaryLinear e a x‖ ≤ R * ‖x‖) ∧
      (fun x => chartCenter hEB3 p + kernelInclusion e (auxiliaryLinear e a x)) ''
        closedBall 0 1 = exclusion C u p ∧
      ∀ i : Fin a.dim, η ≤ (auxiliaryLinear e a).toLinearMap.singularValues i ∧
        (auxiliaryLinear e a).toLinearMap.singularValues i ≤ R := by
  obtain ⟨hcc, hcen⟩ := original_center_continuous hc hs hg hEB3 hW1
  refine ⟨e.toContinuousLinearEquiv.continuous,
    e.symm.toContinuousLinearEquiv.continuous, hcc, ?_⟩
  obtain ⟨η₀, hη₀, hlow⟩ :=
    ExclusionUniformNoncollapse.all_label_uniform_noncollapse hc hs hg hEB3 hW1
  obtain ⟨R₀, hR₀, hb⟩ := (base_compact hc hs).isBounded.exists_pos_norm_le
  let L := e.toContinuousLinearEquiv.toContinuousLinearMap
  let η := min (η₀ / (‖kernelInclusion e‖ + 1)) 1
  let R := (‖L‖ + 1) * (2 * R₀) + 1
  have hη : 0 < η := lt_min (div_pos hη₀ (by positivity)) zero_lt_one
  have hR : 1 ≤ R := by dsimp [R]; nlinarith [norm_nonneg L]
  refine ⟨η, R, hη, (min_le_right _ _).trans hR, (zero_lt_one.trans_le hR), ?_⟩
  intro p a ha
  have hca := (hcen p).2 a
  have hbounds : ∀ x, η * ‖x‖ ≤ ‖auxiliaryLinear e a x‖ ∧
      ‖auxiliaryLinear e a x‖ ≤ R * ‖x‖ := by
    intro x
    constructor
    · have hh := (kernelInclusion e).le_opNorm (auxiliaryLinear e a x)
      rw [inclusion_auxiliaryLinear] at hh
      have hl := hlow p a ha x
      calc η * ‖x‖ ≤ (η₀ / (‖kernelInclusion e‖ + 1)) * ‖x‖ :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg x)
        _ = (η₀ * ‖x‖) / (‖kernelInclusion e‖ + 1) := by ring
        _ ≤ ‖auxiliaryLinear e a x‖ :=
              (div_le_iff₀ (by positivity)).mpr (by nlinarith [norm_nonneg (auxiliaryLinear e a x)])
    · have hA : ‖a.param.linear.toContinuousLinearMap‖ ≤ 2 * R₀ := by
        apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
        intro z hz
        have hzK : a.param z ∈ base C u :=
          (a.whole ▸ mem_image_of_mem a.param (by simpa using hz.le)).1
        have h0K : a.param 0 ∈ base C u :=
          (a.whole ▸ mem_image_of_mem a.param (by simp)).1
        have hd : a.param z - a.param 0 = a.param.linear z := by
          rw [show a.param z = a.param.linear z + a.param 0 from congrFun a.param.decomp z]
          simp
        have hn := norm_sub_le (a.param z) (a.param 0)
        rw [hd] at hn
        exact hn.trans (by linarith [hb _ hzK, hb _ h0K])
      have he : ‖auxiliaryLinear e a x‖ ≤ ‖L‖ * ‖a.param.linear x‖ := L.le_opNorm _
      have hn := a.param.linear.toContinuousLinearMap.le_opNorm x
      have hbig : ‖L‖ * (2 * R₀) ≤ R := by dsimp [R]; nlinarith
      calc ‖auxiliaryLinear e a x‖ ≤ ‖L‖ * (2 * R₀ * ‖x‖) :=
            he.trans (mul_le_mul_of_nonneg_left
              (hn.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg x))) (norm_nonneg L))
        _ ≤ R * ‖x‖ := by nlinarith [norm_nonneg x]
  refine ⟨hca, (hcen p).1.2, hbounds, ?_, ?_⟩
  · have hd (x) : chartCenter hEB3 p + kernelInclusion e (auxiliaryLinear e a x) =
        a.param x := by
      rw [inclusion_auxiliaryLinear, ← hca]
      simpa [add_comm] using (congrFun a.param.decomp x).symm
    simpa only [hd] using a.whole


  · intro i
    let A := auxiliaryLinear e a
    let j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin a.dim))) :=
      ⟨i, by simpa using i.isLt⟩
    let v := D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.rightSingularBasis A.toLinearMap j
    have hv : ‖v‖ = 1 :=
      (D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.rightSingularBasis A.toLinearMap).norm_eq_one j
    have he := D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.inner_apply_rightSingularBasis
      A.toLinearMap j j
    change ⟪A v, A v⟫_ℝ = A.toLinearMap.singularValues i ^ 2 * ⟪v, v⟫_ℝ at he
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv] at he
    have hsigma : ‖A v‖ = A.toLinearMap.singularValues i := by
      nlinarith [norm_nonneg (A v), A.toLinearMap.singularValues_nonneg i]
    have hb := hbounds v
    rw [hv, mul_one, mul_one] at hb
    change η ≤ ‖A v‖ ∧ ‖A v‖ ≤ R at hb
    rwa [hsigma] at hb


private def fixedThreeChart
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) : ExclusionChart C u p :=
  let h := three_chart_data hEB3 p
  ⟨3, by decide, h.choose, h.choose_spec.1, h.choose_spec.2⟩

/-- The positive shape in an arbitrary Euclidean realization of the actual kernel. -/
def shapeOperator (e : u.ker ≃ₗ[ℝ] H)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) : H →L[ℝ] H :=
  let A := auxiliaryLinear e (fixedThreeChart hEB3 p)
  A.comp A.adjoint

/-- The same operator as an endomorphism of the actual kernel, with its metric pulled back by e. -/
def actualKernelShape (e : u.ker ≃ₗ[ℝ] H)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) : u.ker →ₗ[ℝ] u.ker :=
  e.symm.toLinearMap.comp ((shapeOperator e hEB3 p).toLinearMap.comp e.toLinearMap)

private theorem kernelInclusion_injective (e : u.ker ≃ₗ[ℝ] H) :
    Function.Injective (kernelInclusion e) := by
  intro x y h
  apply e.symm.injective
  exact Subtype.ext h

private theorem auxiliaryLinear_injective (e : u.ker ≃ₗ[ℝ] H) {p : V}
    (a : ExclusionChart C u p) : Function.Injective (auxiliaryLinear e a) := by
  intro x y h
  apply a.param.linear_injective_iff.mpr a.injective
  simpa only [inclusion_auxiliaryLinear] using congrArg (kernelInclusion e) h

private theorem linear_ball_eq (e : u.ker ≃ₗ[ℝ] H) (c : V)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] H) (B : F →L[ℝ] H)
    (h : (fun x => c + kernelInclusion e (A x)) '' closedBall 0 1 =
      (fun x => c + kernelInclusion e (B x)) '' closedBall 0 1) :
    A '' closedBall 0 1 = B '' closedBall 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, he⟩ := h ▸ (mem_image_of_mem
      (fun x => c + kernelInclusion e (A x)) hx)
    exact ⟨z, hz, kernelInclusion_injective e (add_left_cancel he)⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, he⟩ := h.symm ▸ (mem_image_of_mem
      (fun x => c + kernelInclusion e (B x)) hx)
    exact ⟨z, hz, kernelInclusion_injective e (add_left_cancel he)⟩

set_option maxHeartbeats 1200000 in
/-- Whole Q1 continuity determines a continuous, chart-independent positive rank-three shape. -/
theorem original_shape_continuous
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1)
    (e : u.ker ≃ₗ[ℝ] H) :
    Continuous (shapeOperator e hEB3) ∧
      ∀ p : pure C u, (shapeOperator e hEB3 p).IsPositive ∧
        Module.finrank ℝ (shapeOperator e hEB3 p).range = 3 ∧
        ∀ a : ExclusionChart C u p,
          shapeOperator e hEB3 p = (auxiliaryLinear e a).comp (auxiliaryLinear e a).adjoint := by
  classical
  obtain ⟨he, hei, hcc, η, R, hη, hηR, hR, hdata⟩ :=
    auxiliary_metric_uniform_charts hc hs hg hEB3 hW1 e
  let A (p : pure C u) : EuclideanSpace ℝ (Fin 3) →L[ℝ] H :=
    auxiliaryLinear e (fixedThreeChart hEB3 p)
  have hball (p : pure C u) :
      ballImage (chartCenter hEB3 p) ((kernelInclusion e).comp (A p)) =
        wholeExclusion hc hs hg (fun p => ⟨(hEB3 p).choose⟩) p := by
    apply NonemptyCompacts.ext
    exact (hdata p (fixedThreeChart hEB3 p) rfl).2.2.2.1
  have hbound (p : pure C u) : A p ∈ closedBall 0 R := by
    rw [mem_closedBall_zero_iff]
    apply (A p).opNorm_le_bound hR.le
    intro x
    exact ((hdata p (fixedThreeChart hEB3 p) rfl).2.2.1 x).2
  have hind (p : pure C u) (a : ExclusionChart C u p) :
      shapeOperator e hEB3 p = (auxiliaryLinear e a).comp (auxiliaryLinear e a).adjoint := by
    apply D5.S3.Geometry.EllipsoidShape.gram_eq_of_ball_image_eq
    apply linear_ball_eq e (chartCenter hEB3 p)
    have hcena := (original_center_continuous hc hs hg hEB3 hW1).2 p |>.2 a
    have hda (x) : chartCenter hEB3 p + kernelInclusion e (auxiliaryLinear e a x) = a.param x := by
      rw [inclusion_auxiliaryLinear, ← hcena]
      simpa [add_comm] using (congrFun a.param.decomp x).symm
    rw [(hdata p (fixedThreeChart hEB3 p) rfl).2.2.2.1]
    simpa only [hda] using a.whole.symm
  refine ⟨?_, fun p => ⟨ContinuousLinearMap.isPositive_self_comp_adjoint (A p), ?_, hind p⟩⟩
  · apply continuous_iff_seqContinuous.mpr
    intro pn p hp
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨B, hB, ms, hms, ht⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] H) R).tendsto_subseq
        (fun n => hbound (pn (ns n)))
    have hcseq := (hcc.tendsto p).comp (hp.comp (hns.comp hms.tendsto_atTop))
    have hcont : Continuous (fun z : V × (EuclideanSpace ℝ (Fin 3) →L[ℝ] H) =>
        ballImage z.1 ((kernelInclusion e).comp z.2)) :=
      Continuous.nonemptyCompacts_map' continuous_const (by fun_prop)
    have hlim := (hcont.tendsto (chartCenter hEB3 p, B)).comp (hcseq.prodMk_nhds ht)
    have hwhole := ((whole_exclusion_continuous hc hs hg hEB3 hW1).tendsto p).comp
      (hp.comp (hns.comp hms.tendsto_atTop))
    have hBeq : ballImage (chartCenter hEB3 p) ((kernelInclusion e).comp B) =
        ballImage (chartCenter hEB3 p) ((kernelInclusion e).comp (A p)) := by
      rw [hball]
      exact tendsto_nhds_unique (by simpa only [hball, Function.comp_def] using hlim) hwhole
    have hgram : B.comp B.adjoint = shapeOperator e hEB3 p := by
      apply D5.S3.Geometry.EllipsoidShape.gram_eq_of_ball_image_eq
      apply linear_ball_eq e (chartCenter hEB3 p)
      exact congrArg (fun K : NonemptyCompacts V => (K : Set V)) hBeq
    have hgramcont : Continuous (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ] H =>
        B.comp B.adjoint) := by fun_prop
    refine ⟨ms, ?_⟩
    change Tendsto (fun n => (A (pn (ns (ms n)))).comp (A (pn (ns (ms n)))).adjoint)
      atTop (𝓝 (shapeOperator e hEB3 p))
    simpa only [Function.comp_def, hgram] using (hgramcont.tendsto B).comp ht
  · change Module.finrank ℝ ((A p).comp (A p).adjoint).range = 3
    have hr := LinearMap.range_self_comp_adjoint (A p).toLinearMap
    have hi : Function.Injective (A p) := auxiliaryLinear_injective e (fixedThreeChart hEB3 p)
    rw [show ((A p).comp (A p).adjoint).range = (A p).range by
      simpa only [ContinuousLinearMap.toLinearMap_comp,
        ContinuousLinearMap.adjoint_toLinearMap] using hr,
      LinearMap.finrank_range_of_inj hi]
    simp


open scoped InnerProductSpace
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse

/-- The actual Moore-Penrose inverse of the chosen-metric shape. -/
def shapeDagger (e : u.ker ≃ₗ[ℝ] H)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) : H →L[ℝ] H :=
  (moorePenroseInverse (shapeOperator e hEB3 p).toLinearMap).toContinuousLinearMap

/-- The actual inverse-shape form; positive definiteness is restricted to the actual range. -/
def fiberMetric (e : u.ker ≃ₗ[ℝ] H)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) (v w : H) : ℝ := ⟪v, shapeDagger e hEB3 p w⟫_ℝ

/-- Q1 supplies the actual continuous inverse and orthogonal range projection. -/
theorem original_inverse_continuous
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1)
    (e : u.ker ≃ₗ[ℝ] H) :
    Continuous (shapeDagger e hEB3) ∧
      Continuous (fun p => (shapeOperator e hEB3 p).range.starProjection) ∧
      Continuous (fun z : pure C u × H × H => fiberMetric e hEB3 z.1 z.2.1 z.2.2) := by
  obtain ⟨he, hei, hcc, η, R, hη, hηR, hR, hdata⟩ :=
    auxiliary_metric_uniform_charts hc hs hg hEB3 hW1 e
  have hshape := (original_shape_continuous hc hs hg hEB3 hW1 e).1
  have hd : Continuous (shapeDagger e hEB3) := by
    apply D5.S3.Geometry.EllipsoidShape.continuous_dagger_of_bound
      (shapeOperator e hEB3) hshape ((η ^ 2)⁻¹)
    intro p
    exact D5.S3.Geometry.EllipsoidShape.gram_dagger_norm_bound
      (auxiliaryLinear e (fixedThreeChart hEB3 p)) hη
      (fun x => ((hdata p (fixedThreeChart hEB3 p) rfl).2.2.1 x).1)
  refine ⟨hd, ?_, ?_⟩
  · have hproj : (fun p => (shapeOperator e hEB3 p).range.starProjection) =
        (fun p => (shapeOperator e hEB3 p).comp (shapeDagger e hEB3 p)) := by
      funext p
      exact (D5.S3.Geometry.EllipsoidShape.comp_dagger_eq_projection _).symm
    rw [hproj]
    exact hshape.clm_comp hd
  · unfold fiberMetric
    exact continuous_snd.fst.inner ((hd.comp continuous_fst).clm_apply continuous_snd.snd)

/-- The metric's actual range disc and sphere are exactly the original ball and relative boundary. -/
theorem original_metric_disc
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1)
    (e : u.ker ≃ₗ[ℝ] H) (p : pure C u) :
    (∀ v ∈ (shapeOperator e hEB3 p).range, v ≠ 0 → 0 < fiberMetric e hEB3 p v v) ∧
      (∀ v, chartCenter hEB3 p + kernelInclusion e v ∈ exclusion C u p ↔
        v ∈ (shapeOperator e hEB3 p).range ∧ fiberMetric e hEB3 p v v ≤ 1) ∧
      (∀ v, chartCenter hEB3 p + kernelInclusion e v ∈ intrinsicFrontier ℝ (exclusion C u p) ↔
        v ∈ (shapeOperator e hEB3 p).range ∧ fiberMetric e hEB3 p v v = 1) := by
  let a := fixedThreeChart hEB3 p
  let A := auxiliaryLinear e a
  have hi : Function.Injective A := auxiliaryLinear_injective e a
  have hcen : a.param 0 = chartCenter hEB3 p :=
    (original_center_continuous hc hs hg hEB3 hW1).2 p |>.2 a
  have hdecomp (x) : a.param x = chartCenter hEB3 p + kernelInclusion e (A x) := by
    rw [inclusion_auxiliaryLinear, ← hcen]
    simpa [add_comm] using congrFun a.param.decomp x
  have hr : (shapeOperator e hEB3 p).range = A.range := by
    simpa only [shapeOperator, A, a, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.adjoint_toLinearMap] using LinearMap.range_self_comp_adjoint A.toLinearMap
  have hm (x y) : fiberMetric e hEB3 p (A x) (A y) = ⟪x, y⟫_ℝ :=
    D5.S3.Geometry.EllipsoidShape.metric_pullback A hi x y
  refine ⟨?_, ?_, ?_⟩
  · intro v hv hne
    obtain ⟨x, rfl⟩ := hr ▸ hv
    change 0 < fiberMetric e hEB3 p (A x) (A x)
    rw [hm, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (fun hx => hne (by simp [hx])))
  · intro v
    change _ ↔ v ∈ (A.comp A.adjoint).range ∧
      ⟪v, moorePenroseInverse (A.comp A.adjoint).toLinearMap v⟫_ℝ ≤ 1
    rw [← (D5.S3.Geometry.EllipsoidShape.metric_ball_image A hi v).1]
    constructor
    · intro hv
      obtain ⟨x, hx, he⟩ := a.whole.symm ▸ hv
      rw [hdecomp] at he
      exact ⟨x, hx, kernelInclusion_injective e (add_left_cancel he)⟩
    · rintro ⟨x, hx, rfl⟩
      rw [← hdecomp]
      exact a.whole ▸ mem_image_of_mem a.param hx
  · intro v
    change _ ↔ v ∈ (A.comp A.adjoint).range ∧
      ⟪v, moorePenroseInverse (A.comp A.adjoint).toLinearMap v⟫_ℝ = 1
    rw [← (D5.S3.Geometry.EllipsoidShape.metric_ball_image A hi v).2]
    have hf : intrinsicFrontier ℝ (exclusion C u p) = a.param '' sphere 0 1 := by
      rw [← a.whole, intrinsic_image a.param a.injective, intrinsic_ball]
    rw [hf]
    constructor
    · rintro ⟨x, hx, he⟩
      rw [hdecomp] at he
      exact ⟨x, hx, kernelInclusion_injective e (add_left_cancel he)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hdecomp x⟩


/-- The full ambient positive square root of the Q1 shape, in the chosen metric. -/
def shapeSqrt (e : u.ker ≃ₗ[ℝ] H)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) : H →L[ℝ] H :=
  D5.S3.Geometry.EllipsoidShape.positiveSqrt (shapeOperator e hEB3 p)

/-- The entire original exclusion uniquely determines its actual affine center and positive shape. -/
theorem original_ellipsoid_unique
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1)
    (e : u.ker ≃ₗ[ℝ] H) :
    Continuous (shapeSqrt e hEB3) ∧
      ∀ p : pure C u,
        u (chartCenter hEB3 p) = 1 ∧
        (shapeOperator e hEB3 p).IsPositive ∧
        Module.finrank ℝ (shapeOperator e hEB3 p).range = 3 ∧
        (fun x : H => chartCenter hEB3 p + kernelInclusion e (shapeSqrt e hEB3 p x)) ''
          closedBall 0 1 = exclusion C u p ∧
        ∀ (c : V) (Q : H →L[ℝ] H), Q.IsPositive →
          (fun x : H => c + kernelInclusion e
            (D5.S3.Geometry.EllipsoidShape.positiveSqrt Q x)) '' closedBall 0 1 =
              exclusion C u p → c = chartCenter hEB3 p ∧ Q = shapeOperator e hEB3 p := by
  have hshape := original_shape_continuous hc hs hg hEB3 hW1 e
  refine ⟨D5.S3.Geometry.EllipsoidShape.continuous_positiveSqrt _ hshape.1
    (fun p => (hshape.2 p).1), ?_⟩
  intro p
  let a := fixedThreeChart hEB3 p
  let A := auxiliaryLinear e a
  have hcena : a.param 0 = chartCenter hEB3 p :=
    (original_center_continuous hc hs hg hEB3 hW1).2 p |>.2 a
  have hdecomp (x) : a.param x = chartCenter hEB3 p + kernelInclusion e (A x) := by
    rw [inclusion_auxiliaryLinear, ← hcena]
    simpa [add_comm] using congrFun a.param.decomp x
  have hball : (fun x : H => chartCenter hEB3 p + kernelInclusion e
      (shapeSqrt e hEB3 p x)) '' closedBall 0 1 = exclusion C u p := by
    have he := D5.S3.Geometry.EllipsoidShape.positiveSqrt_ball_image A
    have himage := congrArg (fun S : Set H => (fun y => chartCenter hEB3 p + kernelInclusion e y) '' S) he
    have hb : (fun x : H => chartCenter hEB3 p + kernelInclusion e
        (shapeSqrt e hEB3 p x)) '' closedBall 0 1 =
        (fun x => chartCenter hEB3 p + kernelInclusion e (A x)) '' closedBall 0 1 := by
      simpa only [image_image, Function.comp_def, shapeSqrt, shapeOperator, A, a] using himage
    exact hb.trans (by simpa only [← hdecomp] using a.whole)
  refine ⟨(original_center_continuous hc hs hg hEB3 hW1).2 p |>.1.2,
    (hshape.2 p).1, (hshape.2 p).2.1, hball, ?_⟩
  intro c Q hQ hrep
  have hcq : c = chartCenter hEB3 p :=
    D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq c (chartCenter hEB3 p)
      ((kernelInclusion e).comp (D5.S3.Geometry.EllipsoidShape.positiveSqrt Q))
      ((kernelInclusion e).comp (shapeSqrt e hEB3 p)) (hrep.trans hball.symm)
  refine ⟨hcq, ?_⟩
  have he := linear_ball_eq e (chartCenter hEB3 p)
    (D5.S3.Geometry.EllipsoidShape.positiveSqrt Q) (shapeSqrt e hEB3 p)
    (by simpa only [hcq] using hrep.trans hball.symm)
  have hg := D5.S3.Geometry.EllipsoidShape.gram_eq_of_ball_image_eq _ _ he
  have hq := D5.S3.Geometry.EllipsoidShape.positiveSqrt_spec Q hQ
  have hp := D5.S3.Geometry.EllipsoidShape.positiveSqrt_spec
    (shapeOperator e hEB3 p) (hshape.2 p).1
  dsimp only [shapeSqrt] at hg
  rw [hq.1.isSymmetric.clm_adjoint_eq, hp.1.isSymmetric.clm_adjoint_eq,
    hq.2.1, hp.2.1] at hg
  exact hg

private def actualRangeEquiv (e : u.ker ≃ₗ[ℝ] H)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (p : pure C u) : (actualKernelShape e hEB3 p).range ≃ₗ[ℝ]
      (shapeOperator e hEB3 p).range where
  toFun v := ⟨e v, by
    obtain ⟨x, hx⟩ := v.property
    refine ⟨e x, ?_⟩
    simpa only [actualKernelShape, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_coe] using congrArg e hx⟩
  invFun v := ⟨e.symm v, by
    obtain ⟨x, hx⟩ := v.property
    refine ⟨e.symm x, ?_⟩
    change e.symm (shapeOperator e hEB3 p (e (e.symm x))) = e.symm v
    rw [e.apply_symm_apply]
    change shapeOperator e hEB3 p x = (v : H) at hx
    rw [hx]⟩
  left_inv v := by apply Subtype.ext; exact e.symm_apply_apply v
  right_inv v := by apply Subtype.ext; exact e.apply_symm_apply v
  map_add' v w := by apply Subtype.ext; exact e.map_add v w
  map_smul' r v := by apply Subtype.ext; exact e.map_smul r v

private def actualRangeGraphHomeomorph (e : u.ker ≃ₗ[ℝ] H)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3) :
    {z : pure C u × u.ker // z.2 ∈ (actualKernelShape e hEB3 z.1).range} ≃ₜ
      {z : pure C u × H // z.2 ∈ (shapeOperator e hEB3 z.1).range} where
  toFun z := ⟨(z.1.1, e z.1.2), (actualRangeEquiv e hEB3 z.1.1 ⟨z.1.2, z.2⟩).property⟩
  invFun z := ⟨(z.1.1, e.symm z.1.2), ((actualRangeEquiv e hEB3 z.1.1).symm ⟨z.1.2, z.2⟩).property⟩
  left_inv z := by apply Subtype.ext; exact Prod.ext rfl (e.symm_apply_apply _)
  right_inv z := by apply Subtype.ext; exact Prod.ext rfl (e.apply_symm_apply _)
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    (e.toContinuousLinearEquiv.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    (e.symm.toContinuousLinearEquiv.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- Q1 constructs the real rank-three bundle on the actual ranges, with precisely their graph topology. -/
theorem original_range_bundle
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1)
    (e : u.ker ≃ₗ[ℝ] H) :
    ∃ a : VectorPrebundle ℝ (EuclideanSpace ℝ (Fin 3))
        (fun p : pure C u => ↥(shapeOperator e hEB3 p).range),
      (∀ p, Module.finrank ℝ (shapeOperator e hEB3 p).range = 3) ∧
      (letI := a.totalSpaceTopology
       letI := a.toFiberBundle
       VectorBundle ℝ (EuclideanSpace ℝ (Fin 3))
         (fun p : pure C u => ↥(shapeOperator e hEB3 p).range)) ∧
      a.totalSpaceTopology = TopologicalSpace.induced
        (D5.S3.Geometry.ContinuousRangeBundle.ambient
          (E := EuclideanSpace ℝ (Fin 3)) (fun p => (shapeOperator e hEB3 p).range))
        inferInstance ∧
      Continuous (fun p => (actualKernelShape e hEB3 p).toContinuousLinearMap) ∧
      (∀ p : pure C u,
        Module.finrank ℝ (actualKernelShape e hEB3 p).range = 3 ∧
        (∀ x : u.ker, e (actualKernelShape e hEB3 p x) = shapeOperator e hEB3 p (e x)) ∧
        (∀ x y : u.ker, ⟪e (actualKernelShape e hEB3 p x), e y⟫_ℝ =
          ⟪e x, e (actualKernelShape e hEB3 p y)⟫_ℝ) ∧
        (∀ x : u.ker, 0 ≤ ⟪e (actualKernelShape e hEB3 p x), e x⟫_ℝ)) ∧
      Nonempty ({z : pure C u × u.ker // z.2 ∈ (actualKernelShape e hEB3 z.1).range} ≃ₜ
        {z : pure C u × H // z.2 ∈ (shapeOperator e hEB3 z.1).range}) := by
  have hp := (original_inverse_continuous hc hs hg hEB3 hW1 e).2.1
  have hr : ∀ p : pure C u, Module.finrank ℝ (shapeOperator e hEB3 p).range =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    intro p
    simpa using (original_shape_continuous hc hs hg hEB3 hW1 e).2 p |>.2.1
  let a := D5.S3.Geometry.ContinuousRangeBundle.prebundle hp hr
  refine ⟨a, fun p => (original_shape_continuous hc hs hg hEB3 hW1 e).2 p |>.2.1,
    a.toVectorBundle, ?_, ?_, ?_, ⟨actualRangeGraphHomeomorph e hEB3⟩⟩
  · exact D5.S3.Geometry.ContinuousRangeBundle.topology_eq_induced hp hr
  · change Continuous (fun p => e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((shapeOperator e hEB3 p).comp e.toContinuousLinearEquiv.toContinuousLinearMap))
    exact continuous_const.clm_comp
      ((original_shape_continuous hc hs hg hEB3 hW1 e).1.clm_comp continuous_const)
  · intro p
    have hq := (original_shape_continuous hc hs hg hEB3 hW1 e).2 p
    have he (x : u.ker) : e (actualKernelShape e hEB3 p x) = shapeOperator e hEB3 p (e x) := by
      simp [actualKernelShape]
    refine ⟨(actualRangeEquiv e hEB3 p).finrank_eq.trans hq.2.1, he, ?_, ?_⟩
    · intro x y
      rw [he, he]
      exact hq.1.isSymmetric (e x) (e y)
    · intro x
      rw [he]
      exact hq.1.re_inner_nonneg_left (e x)

/-- Actual local linear charts normalize the original whole disc and its actual boundary sphere. -/
theorem original_normalized_local_products
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1)
    (e : u.ker ≃ₗ[ℝ] H) (p₀ : pure C u) :
    ∃ a : D5.S3.Geometry.ContinuousRangeBundle.NormalizedChart
        (E := EuclideanSpace ℝ (Fin 3)) (fun p => (shapeOperator e hEB3 p).range)
        (shapeDagger e hEB3),
      p₀ ∈ a.U ∧
      Nonempty ({z : pure C u × H // z.1 ∈ a.U ∧
        chartCenter hEB3 z.1 + kernelInclusion e z.2 ∈ exclusion C u z.1} ≃ₜ
          (a.U × closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)) ∧
      Nonempty ({z : pure C u × H // z.1 ∈ a.U ∧
        chartCenter hEB3 z.1 + kernelInclusion e z.2 ∈
          intrinsicFrontier ℝ (exclusion C u z.1)} ≃ₜ
          (a.U × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ∧
      ∀ b : D5.S3.Geometry.ContinuousRangeBundle.NormalizedChart
          (E := EuclideanSpace ℝ (Fin 3)) (fun p => (shapeOperator e hEB3 p).range)
          (shapeDagger e hEB3),
        ContinuousOn (fun p => (b.backward p).comp (a.forward p)) (a.U ∩ b.U) ∧
        ContinuousOn (fun p => (a.backward p).comp (b.forward p)) (a.U ∩ b.U) := by
  have hshape := original_shape_continuous hc hs hg hEB3 hW1 e
  have hinverse := original_inverse_continuous hc hs hg hEB3 hW1 e
  have hr : ∀ p : pure C u, Module.finrank ℝ (shapeOperator e hEB3 p).range =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    intro p
    simpa using (hshape.2 p).2.1
  obtain ⟨a, ha⟩ := D5.S3.Geometry.ContinuousRangeBundle.exists_chart hinverse.2.1 hr p₀
  obtain ⟨b, hb⟩ := D5.S3.Geometry.ContinuousRangeBundle.exists_normalized_chart a
    (shapeDagger e hEB3) hinverse.1
    (fun p => D5.S3.Geometry.EllipsoidShape.dagger_positive _ (hshape.2 p).1)
    (fun p v hv hn => (original_metric_disc hc hs hg hEB3 hW1 e p).1 v hv hn)
  refine ⟨b, hb.symm ▸ ha, ?_, ?_, ?_⟩
  · refine ⟨(Homeomorph.setCongr ?_).trans b.discHomeomorph⟩
    ext z
    exact and_congr_right (fun _ => (original_metric_disc hc hs hg hEB3 hW1 e z.1).2.1 z.2)
  · refine ⟨(Homeomorph.setCongr ?_).trans b.sphereHomeomorph⟩
    ext z
    exact and_congr_right (fun _ => (original_metric_disc hc hs hg hEB3 hW1 e z.1).2.2 z.2)
  · intro d
    exact ⟨(d.continuousOn_backward.mono inter_subset_right).clm_comp
      (b.continuousOn_forward.mono inter_subset_left),
      (b.continuousOn_backward.mono inter_subset_left).clm_comp
        (d.continuousOn_forward.mono inter_subset_right)⟩

end D5.S3.Quantum.Foundation.ExclusionBallBundle
