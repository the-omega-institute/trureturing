/- GID: D5/S3/Quantum/Foundation/RegularAnchorHeight
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RegularAnchorHeight
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole zero-effect continuity controls original confirmation and endpoint heights. -/

import D5.S3.Quantum.Foundation.FixedZeroObstruction
import Mathlib.Analysis.SpecificLimits.Basic

/-! The whole original pure domain is used in the regularity premise. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.RegularAnchorHeight

open Set Filter Topology
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ContinuousFrameSum FixedZeroObstruction OriginalFacePolarity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Restrictions of every original effect vanishing at the label, on the entire K. -/
def zeroReadouts (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : pure C u) :
    Set C(base C u, ℝ) := stateReadout '' zeroEffects C u p

/-- Source Cont(B), with the original whole-state supremum metric and every
pure sequence in the entire original P. No closedness of P is assumed. -/
def ZeroContinuousAt (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (p : pure C u) : Prop :=
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  ∀ pn : ℕ → pure C u, Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V)) →
    Tendsto (fun n => Metric.hausdorffDist
      (zeroReadouts C u (pn n)) (zeroReadouts C u p)) atTop (𝓝 0)

/-- The original P0 intersect Cont(B), with the full confirming fiber. -/
def RegularAnchor (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (p : pure C u) : Prop :=
  (∃ ep : V →ₗ[ℝ] ℝ, ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep) ∧
    ZeroContinuousAt hc hs p

private theorem zero_readouts_nonempty
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (p : pure C u) :
    (zeroReadouts C u p).Nonempty := by
  refine ⟨stateReadout (0 : V →ₗ[ℝ] ℝ), 0, ⟨?_, by simp⟩, rfl⟩
  intro x hx
  have hu : 0 ≤ u x := by
    by_cases hz : x = 0
    · simp [hz]
    · exact (hs x hx hz).le
  simpa using hu

private theorem zero_readouts_bounded [CompactSpace (base C u)] (p : pure C u) :
    Bornology.IsBounded (zeroReadouts C u p) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro x
  change ‖f x.val‖ ≤ 1
  rw [Real.norm_eq_abs, abs_le]
  have hh := hf.1 x.val x.property.1
  rw [x.property.2] at hh
  exact ⟨by linarith [hh.1], hh.2⟩

private theorem regular_pure_lift
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    {p s : pure C u} (hreg : ZeroContinuousAt hc hs p)
    (hsp : (s : V) ∈ exclusion C u p)
    (pn : ℕ → pure C u) (hp : Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V))) :
    ∃ sn : ℕ → pure C u, (∀ n, (sn n : V) ∈ exclusion C u (pn n)) ∧
      Tendsto (fun n => (sn n : V)) atTop (𝓝 (s : V)) := by
  classical
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  obtain ⟨h, hh, hzero⟩ := ((exclusion_ball_faces hc hs hg hB).1 s).2.2.2.2.2.2
  have hhfull : h ∈ fullZeroConfirmers C u s :=
    ⟨hh, fun x hx => (show x ∈ {x | x ∈ base C u ∧ h x = 0} from hzero ▸ hx).2⟩
  have hhp : h ∈ zeroEffects C u p :=
    ⟨hh.1, hhfull.2 p ((exclusion_symmetric p s).mp hsp)⟩
  let δ : ℕ → ℝ := fun n => Metric.hausdorffDist
    (zeroReadouts C u (pn n)) (zeroReadouts C u p) + 1 / ((n : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [add_zero] using (hreg pn hp).add tendsto_one_div_add_atTop_nhds_zero_nat
  have happrox (n : ℕ) : ∃ b ∈ zeroEffects C u (pn n),
      dist (stateReadout (C := C) (u := u) h) (stateReadout b) < δ n := by
    have hfin := Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (zero_readouts_nonempty hs p) (zero_readouts_nonempty hs (pn n))
      (zero_readouts_bounded p) (zero_readouts_bounded (pn n))
    obtain ⟨b, ⟨f, hf, rfl⟩, hd⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (show stateReadout (C := C) (u := u) h ∈ zeroReadouts C u p from ⟨h, hhp, rfl⟩)
      (show Metric.hausdorffDist (zeroReadouts C u p) (zeroReadouts C u (pn n)) < δ n by
        rw [Metric.hausdorffDist_comm]
        dsimp [δ]
        have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith) hfin
    exact ⟨f, hf, hd⟩
  choose b hb hd using happrox
  choose sn hsn hmax using fun n => zero_effect_maximizer hc hs hg hB (pn n) (hb n)
  have hread (n : ℕ) (x : base C u) : |h x - b n x| ≤ δ n := by
    have he := ContinuousMap.dist_apply_le_dist x
      (f := stateReadout (C := C) (u := u) h) (g := stateReadout (b n))
    have he' : |h x - b n x| ≤ dist (stateReadout (C := C) (u := u) h) (stateReadout (b n)) := by
      simpa only [Real.dist_eq, stateReadout, ContinuousMap.coe_mk] using he
    exact he'.trans (hd n).le
  have hlow (n : ℕ) : 1 - 2 * δ n ≤ h (sn n) := by
    have ha := (abs_le.mp (hread n ⟨s, pure_mem s⟩)).2
    have hc' := (abs_le.mp (hread n ⟨sn n, pure_mem (sn n)⟩)).1
    have hm := hmax n s (pure_mem s)
    rw [hh.2] at ha
    linarith
  have hhigh (n : ℕ) : h (sn n) ≤ 1 := by
    simpa only [(pure_mem (sn n)).2] using (hh.1 (sn n) (pure_mem (sn n)).1).2
  have hval : Tendsto (fun n => h (sn n)) atTop (𝓝 1) := by
    have hlo : Tendsto (fun n => 1 - 2 * δ n) atTop (𝓝 1) := by
      convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hδ) using 1 <;> norm_num
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds hlow hhigh
  refine ⟨sn, hsn, ?_⟩
  apply (base_compact hc hs).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => pure_mem (sn n))
  intro x hx hcluster
  have hecluster := hcluster.continuousAt_comp h.continuous_of_finiteDimensional.continuousAt
  have heq : h x = 1 := by
    have hhcluster := hecluster.clusterPt.mono hval
    by_contra hn
    exact hhcluster.ne ((disjoint_nhds_nhds.mpr hn).eq_bot)
  have hxone : x ∈ ({(s : V)} : Set V) := by
    rw [← (full_zero_faces hc hs hg hB hinj s hhfull).2]
    exact ⟨hx, heq⟩
  exact hxone

/-- At the original Cont(B) point, every choice of full original confirmers
converges to its unique confirmer. The convergence is in the full linear dual,
and therefore controls moving evaluations on the compact original K. -/
theorem regular_confirmation_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) (ep : V →ₗ[ℝ] ℝ)
    (hunique : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep)
    (hreg : ZeroContinuousAt hc hs p)
    (pn : ℕ → pure C u) (hp : Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V)))
    (en : ℕ → (V →ₗ[ℝ] ℝ)) (hen : ∀ n, en n ∈ fullZeroConfirmers C u (pn n)) :
    Tendsto (fun n => (en n).toContinuousLinearMap) atTop (𝓝 ep.toContinuousLinearMap) := by
  classical
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨e, he, φ, hφ, hlim⟩ := (effects_compact hs hg).tendsto_subseq
    (x := fun n => (en (ns n)).toContinuousLinearMap)
    (fun n => (hen (ns n)).1.1)
  let ix : ℕ → ℕ := fun n => ns (φ n)
  have hpix : Tendsto (fun n => (pn (ix n) : V)) atTop (𝓝 (p : V)) :=
    hp.comp (hns.comp hφ.tendsto_atTop)
  have hev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have hep : e p = 1 := by
    apply tendsto_nhds_unique ((hev.tendsto (e, (p : V))).comp (hlim.prodMk_nhds hpix))
    simpa only [ix, (hen _).1.2] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hpurezero (s : pure C u) (hsp : (s : V) ∈ exclusion C u p) : e s = 0 := by
    obtain ⟨sn, hsn, hslim⟩ := regular_pure_lift hc hs hg hB hinj hreg hsp
      (fun n => pn (ix n)) hpix
    apply tendsto_nhds_unique ((hev.tendsto (e, (s : V))).comp (hlim.prodMk_nhds hslim))
    have hz : (fun n => en (ix n) (sn n)) = fun _ : ℕ => (0 : ℝ) :=
      funext fun n => (hen (ix n)).2 _ (hsn n)
    change Tendsto (fun n => en (ix n) (sn n)) atTop (𝓝 0)
    rw [hz]
    exact tendsto_const_nhds
  have hzero : ∀ x ∈ exclusion C u p, e x = 0 := by
    obtain ⟨b⟩ := hB p
    haveI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
    have hhull : exclusion C u p = convexHull ℝ (exclusion C u p ∩ pure C u) := by
      rw [chart_boundary hc hs hg hB p b, ← b.param.image_convexHull,
        convexHull_sphere_eq_closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) zero_le_one,
        b.whole]
    have hsub : exclusion C u p ∩ pure C u ⊆ e ⁻¹' ({0} : Set ℝ) := by
      intro x hx
      exact hpurezero ⟨x, hx.2⟩ hx.1
    intro x hx
    exact (convexHull_min hsub ((convex_singleton (0 : ℝ)).linear_preimage e.toLinearMap))
      (hhull ▸ hx)
  have heq : e = ep.toContinuousLinearMap := by
    apply ContinuousLinearMap.toLinearMap_injective
    exact (hunique e.toLinearMap).mp ⟨⟨he, hep⟩, hzero⟩
  exact ⟨φ, by simpa only [Function.comp_def, heq] using hlim⟩

/-- At a regular original anchor, a fixed positive reading somewhere on its
whole exclusion forces a common positive original height, uniformly over all
original pure labels and every one of their complete confirming effects. -/
theorem regular_anchor_uniform_height
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) (ep : V →ₗ[ℝ] ℝ)
    (hregular : RegularAnchor hc hs p) (hep : ep ∈ fullZeroConfirmers C u p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ (a : pure C u) (ea : V →ₗ[ℝ] ℝ),
      ea ∈ fullZeroConfirmers C u a →
      (∃ z ∈ exclusion C u p, ε ≤ ea z) → σ ≤ (u - ep) a := by
  classical
  obtain ⟨⟨e, he⟩, hreg⟩ := hregular
  have heep : e = ep := ((he ep).mp hep).symm
  have hunique : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep := by
    simpa only [heep] using he
  by_contra! hn
  have hbad (n : ℕ) : ∃ (a : pure C u) (ea : V →ₗ[ℝ] ℝ),
      ea ∈ fullZeroConfirmers C u a ∧
      (∃ z ∈ exclusion C u p, ε ≤ ea z) ∧ (u - ep) a < 1 / ((n : ℝ) + 1) :=
    hn (1 / ((n : ℝ) + 1)) (by positivity)
  choose a ea hea z hz hreading hsmall using hbad
  have hnonneg (n : ℕ) : 0 ≤ (u - ep) (a n) := by
    change 0 ≤ u (a n) - ep (a n)
    exact sub_nonneg.mpr (hep.1.1 (a n) (pure_mem (a n)).1).2
  have hheight : Tendsto (fun n => (u - ep) (a n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat hnonneg (fun n => (hsmall n).le)
  have ha : Tendsto (fun n => (a n : V)) atTop (𝓝 (p : V)) := by
    apply (base_compact hc hs).tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun n => pure_mem (a n))
    intro x hx hcluster
    have hcx := hcluster.continuousAt_comp
      (u - ep).continuous_of_finiteDimensional.continuousAt
    have hzero : (u - ep) x = 0 := by
      have hzcluster := hcx.clusterPt.mono hheight
      by_contra hne
      exact hzcluster.ne ((disjoint_nhds_nhds.mpr hne).eq_bot)
    have hone : ep x = 1 := by
      simpa only [LinearMap.sub_apply, hx.2, sub_eq_zero] using hzero.symm
    have hxone : x ∈ ({(p : V)} : Set V) := by
      rw [← (full_zero_faces hc hs hg hB hinj p hep).2]
      exact ⟨hx, hone⟩
    exact hxone
  have heconv := regular_confirmation_tendsto hc hs hg hB hinj p ep hunique hreg a ha ea hea
  obtain ⟨R, hR, hbound⟩ := (base_compact hc hs).isBounded.exists_pos_norm_le
  have hnorm : Tendsto (fun n => ‖(ea n).toContinuousLinearMap - ep.toContinuousLinearMap‖)
      atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (heconv.sub tendsto_const_nhds).norm
  have hscale : Tendsto (fun n =>
      ‖(ea n).toContinuousLinearMap - ep.toContinuousLinearMap‖ * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using hnorm.mul_const R
  have hupper (n : ℕ) : ε ≤ ‖(ea n).toContinuousLinearMap - ep.toContinuousLinearMap‖ * R := by
    have hb := ((ea n).toContinuousLinearMap - ep.toContinuousLinearMap).le_opNorm (z n)
    have hepz := hep.2 (z n) (hz n)
    have hnormeval : ea n (z n) ≤ ‖(ea n).toContinuousLinearMap - ep.toContinuousLinearMap‖ * ‖z n‖ := by
      have hreadnonneg := (hea n).1.1 (z n) (hz n).1.1
      simpa only [ContinuousLinearMap.sub_apply, LinearMap.coe_toContinuousLinearMap,
        hepz, sub_zero, Real.norm_eq_abs, abs_of_nonneg hreadnonneg.1] using hb
    exact (hreading n).trans (hnormeval.trans
      (mul_le_mul_of_nonneg_left (hbound (z n) (hz n).1) (norm_nonneg _)))
  have hle : ε ≤ 0 := le_of_tendsto' hscale hupper
  exact hε.not_ge hle

#print axioms regular_confirmation_tendsto
#print axioms regular_anchor_uniform_height

end D5.S3.Quantum.Foundation.RegularAnchorHeight
