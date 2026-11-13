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
import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-! The original-domain upper association needed by IX118.3. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.ExclusionIncidence

open Set Filter Topology
open CircuitBalancedConfirmation FacetZeroGluing ContinuousFrameSum
open ExclusionBallFaces OriginalFacePolarity
open WeightedRelationConfirmation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- IX118.1(O), on every actual original edge and every index of each label sequence. -/
def edgeLifting (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ (p q : pure C u), comparison C u p q = 0 →
    ∀ pn : ℕ → pure C u, Tendsto pn atTop (𝓝 p) →
      ∃ qn : ℕ → pure C u,
        (∀ n, comparison C u (pn n) (qn n) = 0) ∧ Tendsto qn atTop (𝓝 q)

/-- The actual original incidence, with its inherited product-subspace topology. -/
abbrev incidence (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) :=
  {z : pure C u × pure C u // (z.2 : V) ∈ exclusion C u z.1}

/-- The first actual incidence projection. -/
def firstProjection (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) :
    incidence C u → pure C u := fun z => z.1.1

/-- The second actual incidence projection. -/
def secondProjection (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) :
    incidence C u → pure C u := fun z => z.1.2

/-- Original full-effect zero symmetry makes the actual swap a homeomorphism. -/
def incidenceSwap (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) :
    incidence C u ≃ₜ incidence C u where
  toFun z := ⟨(z.1.2, z.1.1), (exclusion_symmetric z.1.1 z.1.2).mp z.2⟩
  invFun z := ⟨(z.1.2, z.1.1), (exclusion_symmetric z.1.1 z.1.2).mp z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem comparison_zero_iff_exclusion
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) {x : V} (hx : x ∈ base C u) :
    comparison C u p x = 0 ↔ x ∈ exclusion C u p := by
  constructor
  · intro hzero
    let F : Set (V →L[ℝ] ℝ) := {f | f ∈ effects C u ∧ f p = 1}
    have hcompact : IsCompact F := (effects_compact hs hg).inter_right
      (isClosed_eq (by fun_prop) continuous_const)
    have hunit : u.toContinuousLinearMap ∈ F := by
      refine ⟨?_, (pure_mem p).2⟩
      intro y hy
      refine ⟨?_, le_rfl⟩
      by_cases he : y = 0
      · simp [he]
      · exact (hs y hy he).le
    obtain ⟨f, hf, hmin⟩ := hcompact.exists_isMinOn ⟨_, hunit⟩
      (show ContinuousOn (fun g : V →L[ℝ] ℝ => g x) F by fun_prop)
    have heq : comparison C u p x = f x :=
      attained_comparison hx.1 f.toLinearMap hf
        (fun g hg => hmin (show g.toContinuousLinearMap ∈ F from hg))
    exact ⟨hx, f.toLinearMap, hf, heq.symm.trans hzero⟩
  · rintro ⟨_, f, hf, hfx⟩
    have heq := attained_comparison hx.1 f hf (fun g hg => by
      rw [hfx]
      exact (hg.1 x hx.1).1)
    exact heq.trans hfx

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
    push Not at hn
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
    obtain ⟨qn, hqn, ht⟩ := hO p ⟨q, hq.2⟩
      ((comparison_zero_iff_exclusion hs hg p hq.1.1).mpr hq.1) pn hp
    exact ⟨fun n => (qn n : V),
      fun n => (comparison_zero_iff_exclusion hs hg (pn n) (pure_mem (qn n))).mp (hqn n),
      continuous_subtype_val.tendsto _ |>.comp ht⟩
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
  obtain ⟨s, hsD, hsfin, hcover⟩ := hcompact.finite_cover_balls (half_pos hε)
  have hlower (x : V) (hx : x ∈ s) :
      ∀ᶠ n in atTop, ∃ y ∈ exclusion C u (pn n), dist x y < ε / 2 := by
    obtain ⟨xn, hxn, ht⟩ := exclusion_lower_sequence hc hs hg hB hO hp (hsD hx)
    filter_upwards [(Metric.tendsto_nhds.mp ht) (ε / 2) (half_pos hε)] with n hn
    exact ⟨xn n, hxn n, by simpa [dist_comm] using hn⟩
  have hall : ∀ᶠ n in atTop, ∀ x ∈ s,
      ∃ y ∈ exclusion C u (pn n), dist x y < ε / 2 :=
    (hsfin.eventually_all).mpr hlower
  filter_upwards [hall] with n hn x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hcover hx)
  obtain ⟨y, hy, hay⟩ := hn a ha
  refine ⟨y, hy, (dist_triangle x a y).trans_lt ?_⟩
  have hxa' : dist x a < ε / 2 := hxa
  linarith

/-- Original edge lifting forces Hausdorff convergence of the entire original
exclusions. The forward implication holds for all positive ball dimensions. -/
private theorem whole_exclusions_tendsto_of_edge_lifting
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

private theorem edge_lifting_iff_projection_open
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    edgeLifting C u ↔ IsOpenMap (firstProjection C u) := by
  classical
  constructor
  · intro hO W hW
    apply isClosed_compl_iff.mp
    apply isSeqClosed_iff_isClosed.mp
    intro pn p hn hp
    by_contra hnot
    have hmem : p ∈ firstProjection C u '' W := by simpa using hnot
    obtain ⟨z, hz, rfl⟩ := hmem
    obtain ⟨qn, hqn, ht⟩ := hO z.1.1 z.1.2
      ((comparison_zero_iff_exclusion hs hg z.1.1 (pure_mem z.1.2)).mpr z.2) pn hp
    let zn : ℕ → incidence C u := fun n => ⟨(pn n, qn n),
      (comparison_zero_iff_exclusion hs hg (pn n) (pure_mem (qn n))).mp (hqn n)⟩
    have hzt : Tendsto zn atTop (𝓝 z) :=
      tendsto_subtype_rng.mpr (hp.prodMk_nhds ht)
    obtain ⟨n, hzn⟩ := (hzt.eventually (hW.mem_nhds hz)).exists
    exact hn n ⟨zn n, hzn, rfl⟩
  · intro hopen p q hq pn hp
    let z : incidence C u := ⟨(p, q),
      (comparison_zero_iff_exclusion hs hg p (pure_mem q)).mp hq⟩
    have hlower : LowerHemicontinuousAt
        (fun r => (firstProjection C u) ⁻¹' {r}) p :=
      (isOpenMap_iff_lowerHemicontinuous.mp hopen) p
    obtain ⟨zn, hzn, ht⟩ := hlower.exists_seq_tendsto hp
      (show z ∈ (firstProjection C u) ⁻¹' {p} from rfl)
    have hnonempty (r : pure C u) : ∃ s : pure C u, (s : V) ∈ exclusion C u r := by
      have g := (exclusion_ball_faces hc hs hg hB).1 r
      obtain ⟨s, hs'⟩ := g.2.1.extremePoints_nonempty g.1.nonempty
      exact ⟨⟨s, g.2.2.2.2.1.extremePoints_subset_extremePoints hs'⟩, hs'.1⟩
    choose fallback hfallback using hnonempty
    let qn (n : ℕ) : pure C u :=
      if firstProjection C u (zn n) = pn n then (zn n).1.2 else fallback (pn n)
    have hqmem (n : ℕ) : (qn n : V) ∈ exclusion C u (pn n) := by
      dsimp [qn]
      split_ifs with he
      · simpa only [firstProjection] using he ▸ (zn n).2
      · exact hfallback (pn n)
    refine ⟨qn, fun n =>
      (comparison_zero_iff_exclusion hs hg (pn n) (pure_mem (qn n))).mpr (hqmem n), ?_⟩
    have hsecond : Tendsto (fun n => (zn n).1.2) atTop (𝓝 q) :=
      (continuous_snd.comp continuous_subtype_val).tendsto z |>.comp ht
    apply hsecond.congr'
    filter_upwards [hzn] with n hn
    change firstProjection C u (zn n) = pn n at hn
    simp only [qn, if_pos hn]

/-- On the complete original domain, edge lifting is equivalent to openness
of the actual incidence projection and implies whole-exclusion Hausdorff limits. -/
theorem original_open_incidence_whole_limit
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    (edgeLifting C u ↔ IsOpenMap (firstProjection C u)) ∧
    (edgeLifting C u → IsOpenMap (secondProjection C u) ∧
      ∀ (p : pure C u) (pn : ℕ → pure C u),
      Tendsto pn atTop (𝓝 p) →
      Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) (exclusion C u p))
        atTop (𝓝 0)) := by
  refine ⟨edge_lifting_iff_projection_open hc hs hg hB, ?_⟩
  intro hO
  refine ⟨?_, fun p pn hp => whole_exclusions_tendsto_of_edge_lifting hc hs hg hB hO hp⟩
  exact ((edge_lifting_iff_projection_open hc hs hg hB).mp hO).comp
    (incidenceSwap C u).isOpenMap

#print axioms exclusion_upper_limit
#print axioms exclusion_upper_eventually
#print axioms original_open_incidence_whole_limit

end D5.S3.Quantum.Foundation.ExclusionIncidence
