/- GID: D5/S3/Quantum/Foundation/ExclusionIncidence
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionIncidence
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Topology.Sequences]
   utility: none
   digest: Compact original effects control limits of entire original exclusion fibers. -/

import D5.S3.Quantum.Foundation.ContinuousFrameSum
import D5.S3.Quantum.Foundation.OriginalFacePolarity
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Semicontinuity.Hemicontinuity

import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.AffineSpace.Restrict
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! The original-domain upper association needed by IX118.3. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.ExclusionIncidence

open Set Filter Topology TopologicalSpace
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
      ((ExclusionWidthCompactness.comparison_zero_iff hs hg p hq.1.1).mpr hq.1) pn hp
    exact ⟨fun n => (qn n : V),
      fun n => (ExclusionWidthCompactness.comparison_zero_iff hs hg (pn n) (pure_mem (qn n))).mp (hqn n),
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
      ((ExclusionWidthCompactness.comparison_zero_iff hs hg z.1.1 (pure_mem z.1.2)).mpr z.2) pn hp
    let zn : ℕ → incidence C u := fun n => ⟨(pn n, qn n),
      (ExclusionWidthCompactness.comparison_zero_iff hs hg (pn n) (pure_mem (qn n))).mp (hqn n)⟩
    have hzt : Tendsto zn atTop (𝓝 z) :=
      tendsto_subtype_rng.mpr (hp.prodMk_nhds ht)
    obtain ⟨n, hzn⟩ := (hzt.eventually (hW.mem_nhds hz)).exists
    exact hn n ⟨zn n, hzn, rfl⟩
  · intro hopen p q hq pn hp
    let z : incidence C u := ⟨(p, q),
      (ExclusionWidthCompactness.comparison_zero_iff hs hg p (pure_mem q)).mp hq⟩
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
      (ExclusionWidthCompactness.comparison_zero_iff hs hg (pn n) (pure_mem (qn n))).mpr (hqmem n), ?_⟩
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

section AffineBallLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def ballImage (c : V) (L : E →L[ℝ] V) : NonemptyCompacts V :=
  (⟨⟨Metric.closedBall (0 : E) 1, isCompact_closedBall _ _⟩,
    ⟨0, by simp⟩⟩ : NonemptyCompacts E).map (fun x => c + L x) (by fun_prop)

private theorem parameter_subsequence (c : ℕ → V) (L : ℕ → (E →L[ℝ] V)) (F : NonemptyCompacts V)
    (hF : Tendsto (fun n => ballImage (c n) (L n)) atTop (𝓝 F)) :
    ∃ a : V × (E →L[ℝ] V), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (c (φ n), L (φ n))) atTop (𝓝 a) ∧
      ballImage a.1 a.2 = F := by
  let S := insert F (Set.range fun n => ballImage (c n) (L n))
  have hS : IsCompact S := hF.isCompact_insert_range
  have hU := NonemptyCompacts.isCompact_biUnion_coe_of_isCompact hS
  obtain ⟨R, hR, hbound⟩ := hU.isBounded.exists_pos_norm_le
  have himage (n : ℕ) (x : E) (hx : ‖x‖ ≤ 1) : ‖c n + L n x‖ ≤ R := by
    apply hbound
    exact Set.mem_iUnion₂.mpr ⟨ballImage (c n) (L n),
      Set.mem_insert_of_mem _ ⟨n, rfl⟩, ⟨x, by simpa using hx, rfl⟩⟩
  have hc (n : ℕ) : ‖c n‖ ≤ R := by simpa using himage n 0 (by simp)
  have hL (n : ℕ) : ‖L n‖ ≤ 2 * R := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    have h := norm_sub_le (c n + L n x) (c n)
    have he : c n + L n x - c n = L n x := by abel
    rw [he] at h
    exact h.trans (by linarith [himage n x hx.le, hc n])
  have hpair (n : ℕ) : (c n, L n) ∈ Metric.closedBall (0 : V × (E →L[ℝ] V)) (2 * R) := by
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    exact ⟨(hc n).trans (by linarith), hL n⟩
  obtain ⟨a, ha, φ, hφ, ht⟩ :=
    (isCompact_closedBall (0 : V × (E →L[ℝ] V)) (2 * R)).tendsto_subseq hpair
  refine ⟨a, φ, hφ, ht, ?_⟩
  have hcont : Continuous (fun z : V × (E →L[ℝ] V) => ballImage z.1 z.2) :=
    Continuous.nonemptyCompacts_map' continuous_const (by fun_prop)
  exact tendsto_nhds_unique ((hcont.tendsto a).comp ht) (hF.comp hφ.tendsto_atTop)

omit [FiniteDimensional ℝ V] in
private theorem same_ball_injective (c d : V) (L B : E →L[ℝ] V)
    (hB : Function.Injective B) (heq : ballImage c L = ballImage d B) :
    Function.Injective L := by
  have hunit (x : E) (hx : ‖x‖ ≤ 1) : B x ∈ L.toLinearMap.range := by
    have hdx : d + B x ∈ ballImage c L := by
      rw [heq]
      exact ⟨x, by simpa using hx, rfl⟩
    have hd : d ∈ ballImage c L := by
      rw [heq]
      exact ⟨0, by simp, by simp⟩
    obtain ⟨y, hy, hyx⟩ := hdx
    obtain ⟨z, hz, hzd⟩ := hd
    dsimp only at hyx hzd
    refine ⟨y-z, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, map_sub]
    have : L y - L z = B x := by
      calc
        L y - L z = (c + L y) - (c + L z) := by abel
        _ = (d + B x) - d := by rw [hyx, hzd]
        _ = B x := by abel
    exact this
  have hrange : B.toLinearMap.range ≤ L.toLinearMap.range := by
    rintro _ ⟨x, rfl⟩
    by_cases hx : x = 0
    · simp [hx]
    have hnorm : ‖(‖x‖⁻¹ : ℝ) • x‖ ≤ 1 := by
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have hm := (L.toLinearMap.range).smul_mem ‖x‖ (hunit _ hnorm)
    simpa [map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx)] using hm
  have hdim := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hB] at hdim
  have hnull := L.toLinearMap.finrank_range_add_finrank_ker
  have hzero : Module.finrank ℝ L.toLinearMap.ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)

variable [Nontrivial E]
private def sphereImage (c : V) (L : E →L[ℝ] V) : NonemptyCompacts V :=
  (⟨⟨Metric.sphere (0 : E) 1, isCompact_sphere _ _⟩,
    NormedSpace.sphere_nonempty.mpr (by norm_num)⟩ : NonemptyCompacts E).map
      (fun x => c + L x) (by fun_prop)

omit [FiniteDimensional ℝ V] in
private theorem continuous_sphereImage :
    Continuous (fun z : V × (E →L[ℝ] V) => sphereImage z.1 z.2) :=
  Continuous.nonemptyCompacts_map' continuous_const (by fun_prop)

omit [FiniteDimensional ℝ V] in
private theorem sphere_eq_extreme [StrictConvexSpace ℝ E] (c : V) (L : E →L[ℝ] V)
    (hL : Function.Injective L) :
    (sphereImage c L : Set V) = Set.extremePoints ℝ (ballImage c L : Set V) := by
  let a : E →ᵃ[ℝ] V := (AffineEquiv.constVAdd ℝ V c).toAffineMap.comp L.toLinearMap.toAffineMap
  have ha : Function.Injective a := fun x y h => hL (add_left_cancel h)
  have hext : a '' Set.extremePoints ℝ (Metric.closedBall (0 : E) 1) =
      Set.extremePoints ℝ (a '' Metric.closedBall (0 : E) 1) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact CircuitBalancedConfirmation.affine_extreme_image _ (convex_closedBall _ _)
        a ha.injOn hx
    · intro hy
      obtain ⟨x, _, rfl⟩ := hy.1
      exact ⟨x, WholePairBallConfirmation.affine_extreme_preimage a ha _ x hy, rfl⟩
  rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere] at hext
  exact hext

private theorem fullrank_sphere_limit [StrictConvexSpace ℝ E]
    (c : ℕ → V) (L : ℕ → (E →L[ℝ] V)) (d : V) (B : E →L[ℝ] V)
    (hB : Function.Injective B)
    (ht : Tendsto (fun n => ballImage (c n) (L n)) atTop (𝓝 (ballImage d B))) :
    Tendsto (fun n => sphereImage (c n) (L n)) atTop (𝓝 (sphereImage d B)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨a, ms, hms, ha, heq⟩ := parameter_subsequence
    (c ∘ ns) (L ∘ ns) (ballImage d B) (ht.comp hns)
  have hinj := same_ball_injective a.1 d a.2 B hB heq
  have hs : sphereImage a.1 a.2 = sphereImage d B := by
    apply NonemptyCompacts.ext
    rw [sphere_eq_extreme _ _ hinj, sphere_eq_extreme _ _ hB, heq]
  refine ⟨ms, ?_⟩
  simpa [Function.comp_def, hs] using
    (continuous_sphereImage.tendsto a).comp ha

omit [Nontrivial E] in
theorem intrinsic_ball :
    intrinsicFrontier ℝ (Metric.closedBall (0 : E) 1) = Metric.sphere 0 1 := by
  have hspan : affineSpan ℝ (Metric.closedBall (0 : E) 1) = ⊤ := by
    apply top_unique
    have hb : (Metric.ball (0 : E) 1).Nonempty := ⟨0, by simp⟩
    rw [← Metric.isOpen_ball.affineSpan_eq_top hb]
    exact affineSpan_mono ℝ Metric.ball_subset_closedBall
  unfold intrinsicFrontier
  rw [hspan]
  change (AffineSubspace.topEquiv ℝ E E : (⊤ : AffineSubspace ℝ E) ≃ᵃ[ℝ] E) ''
    frontier ((AffineSubspace.topEquiv ℝ E E : (⊤ : AffineSubspace ℝ E) ≃ᵃ[ℝ] E) ⁻¹'
      Metric.closedBall (0 : E) 1) = _
  let e := (AffineSubspace.topEquiv ℝ E E).toContinuousAffineEquiv.toHomeomorph
  change e '' frontier (e ⁻¹' Metric.closedBall (0 : E) 1) = _
  rw [← e.preimage_frontier, e.image_preimage]
  exact frontier_closedBall (0 : E) (by norm_num)

omit [FiniteDimensional ℝ V] [Nontrivial E] in
theorem intrinsic_image (a : E →ᵃ[ℝ] V) (ha : Function.Injective a) (s : Set E) :
    intrinsicFrontier ℝ (a '' s) = a '' intrinsicFrontier ℝ s := by
  let T : AffineSubspace ℝ V := (⊤ : AffineSubspace ℝ E).map a
  let e : E ≃ᵃ[ℝ] T := (AffineSubspace.topEquiv ℝ E E).symm.trans
    (AffineEquiv.ofBijective (AffineMap.restrict.bijective ha))
  have he : (fun x => T.subtypeₐᵢ (e x)) = a := rfl
  calc
    intrinsicFrontier ℝ (a '' s) = intrinsicFrontier ℝ (T.subtypeₐᵢ '' (e '' s)) := by
      rw [Set.image_image]; rfl
    _ = T.subtypeₐᵢ '' intrinsicFrontier ℝ (e '' s) := T.subtypeₐᵢ.intrinsicFrontier_image _
    _ = T.subtypeₐᵢ '' (e '' intrinsicFrontier ℝ s) := by rw [e.intrinsicFrontier_image]
    _ = a '' intrinsicFrontier ℝ s := by rw [Set.image_image]; rfl

private theorem affine_sphere_limit [StrictConvexSpace ℝ E]
    (a : ℕ → E →ᵃ[ℝ] V) (b : E →ᵃ[ℝ] V)
    (hb : Function.Injective b)
    (ht : Tendsto (fun n => Metric.hausdorffDist
      (a n '' Metric.closedBall 0 1) (b '' Metric.closedBall 0 1)) atTop (𝓝 0)) :
    Tendsto (fun n => Metric.hausdorffDist
      (a n '' Metric.sphere 0 1) (b '' Metric.sphere 0 1)) atTop (𝓝 0) := by
  let c := fun n => a n 0
  let L := fun n => (a n).linear.toContinuousLinearMap
  let d := b 0
  let B := b.linear.toContinuousLinearMap
  have hfa (n : ℕ) (x : E) : c n + L n x = a n x := by
    simpa [c, L, add_comm] using (congrFun (a n).decomp x).symm
  have hfb (x : E) : d + B x = b x := by
    simpa [d, B, add_comm] using (congrFun b.decomp x).symm
  have hball (n : ℕ) : (ballImage (c n) (L n) : Set V) = a n '' Metric.closedBall 0 1 := by
    change (fun x => c n + L n x) '' _ = _
    simp_rw [hfa]
  have hballb : (ballImage d B : Set V) = b '' Metric.closedBall 0 1 := by
    change (fun x => d + B x) '' _ = _
    simp_rw [hfb]
  have hsphere (n : ℕ) : (sphereImage (c n) (L n) : Set V) = a n '' Metric.sphere 0 1 := by
    change (fun x => c n + L n x) '' _ = _
    simp_rw [hfa]
  have hsphereb : (sphereImage d B : Set V) = b '' Metric.sphere 0 1 := by
    change (fun x => d + B x) '' _ = _
    simp_rw [hfb]
  have hn : Tendsto (fun n => ballImage (c n) (L n)) atTop (𝓝 (ballImage d B)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [NonemptyCompacts.dist_eq, hball, hballb] using ht
  have hinj : Function.Injective B := b.linear_injective_iff.mpr hb
  have h := tendsto_iff_dist_tendsto_zero.mp (fullrank_sphere_limit c L d B hinj hn)
  simpa only [NonemptyCompacts.dist_eq, hsphere, hsphereb] using h

theorem affine_ball_boundary_limit [StrictConvexSpace ℝ E]
    (a : ℕ → E →ᵃ[ℝ] V) (b : E →ᵃ[ℝ] V)
    (ha : ∀ n, Function.Injective (a n)) (hb : Function.Injective b)
    (ht : Tendsto (fun n => Metric.hausdorffDist
      (a n '' Metric.closedBall 0 1) (b '' Metric.closedBall 0 1)) atTop (𝓝 0)) :
    Tendsto (fun n => Metric.hausdorffDist
      (intrinsicFrontier ℝ (a n '' Metric.closedBall 0 1))
      (intrinsicFrontier ℝ (b '' Metric.closedBall 0 1))) atTop (𝓝 0) ∧
    ∀ (xn : ℕ → V) (x : V),
      (∀ n, xn n ∈ intrinsicFrontier ℝ (a n '' Metric.closedBall 0 1)) →
      Tendsto xn atTop (𝓝 x) → x ∈ intrinsicFrontier ℝ (b '' Metric.closedBall 0 1) := by
  have h := affine_sphere_limit a b hb ht
  have hconv : Tendsto (fun n => Metric.hausdorffDist
      (intrinsicFrontier ℝ (a n '' Metric.closedBall 0 1))
      (intrinsicFrontier ℝ (b '' Metric.closedBall 0 1))) atTop (𝓝 0) := by
    simpa only [intrinsic_image _ (ha _), intrinsic_image _ hb, intrinsic_ball] using h
  refine ⟨hconv, ?_⟩
  intro xn x hxn hx
  let M (f : E →ᵃ[ℝ] V) : NonemptyCompacts V :=
    ⟨⟨f '' Metric.sphere 0 1, (isCompact_sphere (0 : E) 1).image
      f.continuous_of_finiteDimensional⟩,
      (NormedSpace.sphere_nonempty.mpr (by norm_num) :
        (Metric.sphere (0 : E) 1).Nonempty).image f⟩
  have hM (f : E →ᵃ[ℝ] V) (hf : Function.Injective f) :
      (M f : Set V) = intrinsicFrontier ℝ (f '' Metric.closedBall 0 1) := by
    rw [intrinsic_image _ hf, intrinsic_ball]
    rfl
  have hMt : Tendsto (fun n => M (a n)) atTop (𝓝 (M b)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [NonemptyCompacts.dist_eq, hM _ (ha _), hM _ hb] using hconv
  have hzero (n : ℕ) : Metric.infDist (xn n) (M (a n)) = 0 :=
    Metric.infDist_zero_of_mem ((hM _ (ha n)).symm ▸ hxn n)
  have hi := NonemptyCompacts.lipschitz_infDist.continuous.tendsto (x, M b) |>.comp
    (hx.prodMk_nhds hMt)
  have heq : Metric.infDist x (M b) = 0 := tendsto_nhds_unique hi (by
    simpa only [Function.comp_def, hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  rw [← hM b hb]
  exact (M b).isCompact.isClosed.mem_iff_infDist_zero (M b).nonempty |>.mpr heq

end AffineBallLimits

/-- The entire original incidence, whole exclusions and pure spheres have the
claimed topology on the full rank-three domain in the original norm. -/
theorem original_open_incidence_iff_whole_continuous
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : ∀ p : pure C u, ∃ b : ExclusionChart C u p, b.dim = 3) :
    (edgeLifting C u ↔ IsOpenMap (firstProjection C u)) ∧
    (edgeLifting C u ↔ ∀ p : pure C u,
      Tendsto (fun r : pure C u => Metric.hausdorffDist
        (exclusion C u r) (exclusion C u p)) (𝓝 p) (𝓝 0)) ∧
    (edgeLifting C u →
      (∀ p : pure C u, Tendsto (fun r : pure C u => Metric.hausdorffDist
        (pure C u ∩ exclusion C u r) (pure C u ∩ exclusion C u p)) (𝓝 p) (𝓝 0)) ∧
      IsOpenMap (secondProjection C u)) := by
  classical
  have hB : exclusionBalls C u := fun p => ⟨(h3 p).choose⟩
  have hcharts (p : pure C u) : ∃ a : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] V,
      Function.Injective a ∧ a '' Metric.closedBall 0 1 = exclusion C u p := by
    obtain ⟨⟨d, hd, a, ha, hw⟩, he⟩ := h3 p
    dsimp only at he
    subst d
    exact ⟨a, ha, hw⟩
  choose a ha hw using hcharts
  let b (p : pure C u) : ExclusionChart C u p := ⟨3, by decide, a p, ha p, hw p⟩
  let S (p : pure C u) : NonemptyCompacts V :=
    ⟨⟨a p '' Metric.sphere 0 1,
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).image
        (a p).continuous_of_finiteDimensional⟩,
      (NormedSpace.sphere_nonempty.mpr (by norm_num) :
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty).image (a p)⟩
  have hS (p : pure C u) : (S p : Set V) = pure C u ∩ exclusion C u p := by
    have h := chart_boundary hc hs hg hB p (b p)
    simpa [S, b, Set.inter_comm] using h.symm
  have sphere_limit (p : pure C u) (pn : ℕ → pure C u)
      (ht : Tendsto (fun n => Metric.hausdorffDist
        (exclusion C u (pn n)) (exclusion C u p)) atTop (𝓝 0)) :
      Tendsto (fun n => S (pn n)) atTop (𝓝 (S p)) := by
    have h := affine_ball_boundary_limit (fun n => a (pn n)) (a p)
      (fun n => ha (pn n)) (ha p) (by simpa only [hw] using ht) |>.1
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa [intrinsic_image _ (ha _), intrinsic_ball, NonemptyCompacts.dist_eq, S] using h
  have hforward : edgeLifting C u → ∀ p : pure C u,
      Tendsto (fun r : pure C u => Metric.hausdorffDist
        (exclusion C u r) (exclusion C u p)) (𝓝 p) (𝓝 0) := by
    intro hO p
    apply tendsto_nhds_iff_seq_tendsto.mpr
    intro pn hp
    exact (original_open_incidence_whole_limit hc hs hg hB).2 hO |>.2 p pn hp
  refine ⟨(original_open_incidence_whole_limit hc hs hg hB).1, ⟨hforward, ?_⟩, ?_⟩
  · intro hcont p q hq pn hp
    have ht := sphere_limit p pn ((hcont p).comp hp)
    have hqS : (q : V) ∈ S p := by
      change (q : V) ∈ (S p : Set V)
      rw [hS p]
      exact ⟨q.property, (ExclusionWidthCompactness.comparison_zero_iff hs hg p (pure_mem q)).mp hq⟩
    choose xn hxn heq using fun n =>
      (S (pn n)).isCompact.exists_infDist_eq_dist (S (pn n)).nonempty (q : V)
    let qn (n : ℕ) : pure C u := ⟨xn n, ((hS (pn n)) ▸ hxn n).1⟩
    refine ⟨qn, ?_, ?_⟩
    · intro n
      exact (ExclusionWidthCompactness.comparison_zero_iff hs hg (pn n) (pure_mem (qn n))).mpr
        (((hS (pn n)) ▸ hxn n).2)
    · apply tendsto_subtype_rng.mpr
      apply tendsto_iff_dist_tendsto_zero.mpr
      have hi := ((NonemptyCompacts.lipschitz_infDist_const (q : V)).continuous.tendsto
        (S p)).comp ht
      simpa [Function.comp_def, Metric.infDist_zero_of_mem hqS, heq, qn, dist_comm] using hi
  · intro hO
    refine ⟨?_, (original_open_incidence_whole_limit hc hs hg hB).2 hO |>.1⟩
    intro p
    apply tendsto_nhds_iff_seq_tendsto.mpr
    intro pn hp
    have ht := tendsto_iff_dist_tendsto_zero.mp (sphere_limit p pn ((hforward hO p).comp hp))
    simpa only [NonemptyCompacts.dist_eq, hS, Function.comp_def] using ht

#print axioms original_open_incidence_iff_whole_continuous


#print axioms affine_ball_boundary_limit
#print axioms exclusion_upper_limit
#print axioms exclusion_upper_eventually
#print axioms original_open_incidence_whole_limit

end D5.S3.Quantum.Foundation.ExclusionIncidence
