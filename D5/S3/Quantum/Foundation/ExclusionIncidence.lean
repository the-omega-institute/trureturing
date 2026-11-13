/- GID: D5/S3/Quantum/Foundation/ExclusionIncidence
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionIncidence
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Topology.Sequences]
   utility: none
   digest: Compact original effects control limits of entire original exclusion fibers. -/

import D5.S3.Quantum.Foundation.ContinuousFrameSum
import D5.S3.Quantum.Foundation.OriginalFacePolarity
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! The original-domain upper association needed by IX118.3. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.ExclusionIncidence

open Set Filter Topology
open CircuitBalancedConfirmation FacetZeroGluing ContinuousFrameSum
open ExclusionBallFaces OriginalFacePolarity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- IX118.1(O), on every actual original edge and every index of each label sequence. -/
def edgeLifting (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ (p q : pure C u), (q : V) ∈ exclusion C u p →
    ∀ pn : ℕ → pure C u, Tendsto pn atTop (𝓝 p) →
      ∃ qn : ℕ → pure C u,
        (∀ n, (qn n : V) ∈ exclusion C u (pn n)) ∧ Tendsto qn atTop (𝓝 q)

/-- A pure limiting label retains every limit of actual mixed exclusion states.
The effect interval and base compactness are derived on the original normed space. -/
theorem exclusion_upper_limit {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {p : pure C u} {pn : ℕ → pure C u} {y : V} {yn : ℕ → V}
    (hp : Tendsto pn atTop (𝓝 p)) (hy : Tendsto yn atTop (𝓝 y))
    (hyn : ∀ n, yn n ∈ exclusion C u (pn n)) : y ∈ exclusion C u p := by
  let f (n : ℕ) : V →L[ℝ] ℝ := ((hyn n).2.choose).toContinuousLinearMap
  have hf (n : ℕ) : confirms C u (pn n) (f n).toLinearMap :=
    (hyn n).2.choose_spec.1
  have hz (n : ℕ) : f n (yn n) = 0 := (hyn n).2.choose_spec.2
  obtain ⟨e, he, φ, hφ, hfe⟩ :=
    (effects_compact hs hg).tendsto_subseq (fun n => (hf n).1)
  have hpp : Tendsto (fun n => (pn (φ n) : V)) atTop (𝓝 (p : V)) :=
    (continuous_subtype_val.tendsto p |>.comp hp).comp hφ.tendsto_atTop
  have hyy : Tendsto (fun n => yn (φ n)) atTop (𝓝 y) := hy.comp hφ.tendsto_atTop
  have hev : Continuous (fun t : (V →L[ℝ] ℝ) × V => t.1 t.2) := by fun_prop
  have hep : e p = 1 := by
    apply tendsto_nhds_unique ((hev.tendsto (e, (p : V))).comp (hfe.prodMk_nhds hpp))
    have hconst : (fun n => f (φ n) (pn (φ n))) = fun _ : ℕ => (1 : ℝ) :=
      funext (fun n => (hf (φ n)).2)
    change Tendsto (fun n => f (φ n) (pn (φ n))) atTop (𝓝 1)
    rw [hconst]
    exact tendsto_const_nhds
  have hey : e y = 0 := by
    apply tendsto_nhds_unique ((hev.tendsto (e, y)).comp (hfe.prodMk_nhds hyy))
    have hconst : (fun n => f (φ n) (yn (φ n))) = fun _ : ℕ => (0 : ℝ) :=
      funext (fun n => hz (φ n))
    change Tendsto (fun n => f (φ n) (yn (φ n))) atTop (𝓝 0)
    rw [hconst]
    exact tendsto_const_nhds
  exact ⟨(base_compact hc hs).isClosed.mem_of_tendsto hy
    (Eventually.of_forall fun n => (hyn n).1), e.toLinearMap, ⟨he, hep⟩, hey⟩

/-- Uniform upper approximation of each entire nearby exclusion fiber, in the
original norm. No ball, faithful-label or closed-pure-carrier hypothesis is used. -/
theorem exclusion_upper_eventually {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {p : pure C u} {pn : ℕ → pure C u}
    (hp : Tendsto pn atTop (𝓝 p)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ exclusion C u (pn n),
      ∃ z ∈ exclusion C u p, dist y z < ε := by
  classical
  by_contra h
  have hb : ∃ᶠ n in atTop, ∃ y ∈ exclusion C u (pn n),
      ∀ z ∈ exclusion C u p, ε ≤ dist y z := by
    apply (not_eventually.mp h).mono
    intro n hn
    push_neg at hn
    exact hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hb
  choose y hy hfar using hbad
  obtain ⟨z, _, ψ, hψ, hyz⟩ :=
    (base_compact hc hs).tendsto_subseq (fun n => (hy n).1)
  have hz : z ∈ exclusion C u p := exclusion_upper_limit hc hs hg
    (hp.comp (hφ.comp hψ).tendsto_atTop) hyz (fun n => hy (ψ n))
  have hnear : ∀ᶠ n in atTop, dist (y (ψ n)) z < ε :=
    (Metric.tendsto_nhds.mp hyz) ε hε
  obtain ⟨n, hn⟩ := hnear.exists
  exact (hfar (ψ n) z hz).not_gt hn

private theorem exclusion_lower_sequence {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hB : exclusionBalls C u) (hO : edgeLifting C u)
    {p : pure C u} {pn : ℕ → pure C u} (hp : Tendsto pn atTop (𝓝 p))
    {x : V} (hx : x ∈ exclusion C u p) :
    ∃ xn : ℕ → V, (∀ n, xn n ∈ exclusion C u (pn n)) ∧
      Tendsto xn atTop (𝓝 x) := by
  let L : Set V := {z | ∃ zn : ℕ → V,
    (∀ n, zn n ∈ exclusion C u (pn n)) ∧ Tendsto zn atTop (𝓝 z)}
  have hconv : Convex ℝ L := by
    rintro a ⟨an, ha, hta⟩ b ⟨bn, hb, htb⟩ r s hr hs' hrs
    refine ⟨fun n => r • an n + s • bn n, ?_, ?_⟩
    · intro n
      exact ((exclusion_ball_faces hc hs hg hB).1 (pn n)).2.2.1
        (ha n) (hb n) hr hs' hrs
    · exact (hta.const_smul r).add (htb.const_smul s)
  have hboundary : exclusion C u p ∩ pure C u ⊆ L := by
    intro q hq
    obtain ⟨qn, hqn, ht⟩ := hO p ⟨q, hq.2⟩ hq.1 pn hp
    exact ⟨fun n => (qn n : V), hqn, continuous_subtype_val.tendsto _ |>.comp ht⟩
  have hhull : exclusion C u p = convexHull ℝ (exclusion C u p ∩ pure C u) := by
    obtain ⟨b⟩ := hB p
    haveI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
    rw [chart_boundary hc hs hg hB p b, ← b.param.image_convexHull,
      convexHull_sphere_eq_closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) zero_le_one,
      b.whole]
  exact (convexHull_min hboundary hconv) (hhull ▸ hx)

private theorem exclusion_lower_eventually {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hB : exclusionBalls C u) (hO : edgeLifting C u)
    {p : pure C u} {pn : ℕ → pure C u} (hp : Tendsto pn atTop (𝓝 p))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ exclusion C u p,
      ∃ y ∈ exclusion C u (pn n), dist x y < ε := by
  classical
  have hcompact := ((exclusion_ball_faces hc hs hg hB).1 p).2.1
  obtain ⟨s, hsD, hcover⟩ := hcompact.finite_cover_balls (half_pos hε)
  have hlower (x : V) (hx : x ∈ s) :
      ∀ᶠ n in atTop, ∃ y ∈ exclusion C u (pn n), dist x y < ε / 2 := by
    obtain ⟨xn, hxn, ht⟩ := exclusion_lower_sequence hc hs hg hB hO hp (hsD hx)
    filter_upwards [(Metric.tendsto_nhds.mp ht) (ε / 2) (half_pos hε)] with n hn
    exact ⟨xn n, hxn n, by simpa [dist_comm] using hn⟩
  have hall : ∀ᶠ n in atTop, ∀ x ∈ s,
      ∃ y ∈ exclusion C u (pn n), dist x y < ε / 2 :=
    (eventually_all_finset s).mpr hlower
  filter_upwards [hall] with n hn x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hcover hx)
  obtain ⟨y, hy, hay⟩ := hn a ha
  refine ⟨y, hy, (dist_triangle x a y).trans_lt ?_⟩
  have hxa' : dist x a < ε / 2 := hxa
  linarith

/-- Original edge lifting forces Hausdorff convergence of the entire original
exclusions. The forward implication holds for all positive ball dimensions. -/
theorem whole_exclusions_tendsto_of_edge_lifting
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hB : exclusionBalls C u) (hO : edgeLifting C u)
    {p : pure C u} {pn : ℕ → pure C u} (hp : Tendsto pn atTop (𝓝 p)) :
    Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) (exclusion C u p))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [exclusion_upper_eventually hc hs hg hp (half_pos hε),
    exclusion_lower_eventually hc hs hg hB hO hp (half_pos hε)] with n hup hlo
  have hbound : Metric.hausdorffDist (exclusion C u (pn n)) (exclusion C u p) ≤ ε / 2 :=
    Metric.hausdorffDist_le_of_mem_dist (half_pos hε).le
      (fun y hy => let ⟨z, hz, hd⟩ := hup y hy; ⟨z, hz, hd.le⟩)
      (fun y hy => let ⟨z, hz, hd⟩ := hlo y hy; ⟨z, hz, hd.le⟩)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] using
    hbound.trans_lt (half_lt_self hε)

#print axioms exclusion_upper_limit
#print axioms exclusion_upper_eventually
#print axioms whole_exclusions_tendsto_of_edge_lifting

end D5.S3.Quantum.Foundation.ExclusionIncidence
