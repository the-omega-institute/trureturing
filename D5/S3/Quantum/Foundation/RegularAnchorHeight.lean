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
  apply ContinuousMap.norm_le (by norm_num) |>.mpr
  intro x
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
      dist (stateReadout h) (stateReadout b) < δ n := by
    have hfin := Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (zero_readouts_nonempty hs p) (zero_readouts_nonempty hs (pn n))
      (zero_readouts_bounded p) (zero_readouts_bounded (pn n))
    obtain ⟨b, ⟨f, hf, rfl⟩, hd⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (show stateReadout h ∈ zeroReadouts C u p from ⟨h, hhp, rfl⟩)
      (show Metric.hausdorffDist (zeroReadouts C u p) (zeroReadouts C u (pn n)) < δ n by
        rw [Metric.hausdorffDist_comm]; dsimp [δ]; positivity) hfin
    exact ⟨f, hf, hd⟩
  choose b hb hd using happrox
  choose sn hsn hmax using fun n => zero_effect_maximizer hc hs hg hB (pn n) (hb n)
  have hread (n : ℕ) (x : base C u) : |h x - b n x| ≤ δ n := by
    have he := ContinuousMap.dist_apply_le_dist x (f := stateReadout h) (g := stateReadout (b n))
    exact (by simpa only [Real.dist_eq, stateReadout, ContinuousMap.coe_mk] using he).trans (hd n).le
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

end D5.S3.Quantum.Foundation.RegularAnchorHeight
