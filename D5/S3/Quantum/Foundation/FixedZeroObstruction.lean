/- GID: D5/S3/Quantum/Foundation/FixedZeroObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FixedZeroObstruction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original whole-state zero-effect maxima and singleton one-faces. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import D5.S3.Quantum.Foundation.ExclusionIncidence
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness

/-! Full original effects and state body; no closed pure locus or least effects are assumed. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.FixedZeroObstruction

open Set Filter Topology TopologicalSpace
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ContinuousFrameSum ExclusionIncidence ExclusionWidthCompactness OriginalFacePolarity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The original entire zero-confirming effects at a pure label. -/
def zeroEffects (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (t : pure C u) :
    Set (V →ₗ[ℝ] ℝ) := {g | proper C u g ∧ g t = 0}

/-- The original confirmers that vanish on the entire exclusion face. -/
def fullZeroConfirmers (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (s : pure C u) :
    Set (V →ₗ[ℝ] ℝ) :=
  {h | confirms C u s h ∧ ∀ x ∈ exclusion C u s, h x = 0}

/-- A global maximum of every actual zero effect is attained at a pure point
of the entire exclusion. The zero effect is included. -/
theorem zero_effect_maximizer
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (t : pure C u) {g : V →ₗ[ℝ] ℝ} (hgt : g ∈ zeroEffects C u t) :
    ∃ v : pure C u, (v : V) ∈ exclusion C u t ∧
      ∀ x ∈ base C u, g x ≤ g v := by
  have hK := base_compact hc hs
  have hD := (exclusion_ball_faces hc hs hg hB).1 t
  by_cases hg0 : g = 0
  · obtain ⟨v, hv⟩ := hD.2.1.extremePoints_nonempty hD.1.nonempty
    exact ⟨⟨v, hD.2.2.2.2.1.extremePoints_subset_extremePoints hv⟩,
      hv.1, by simp [hg0]⟩
  · have hpos : ∃ q : pure C u, 0 < g q := by
      by_contra! hn
      have hz (q : pure C u) : g q = 0 :=
        le_antisymm (hn q) (hgt.1 q (pure_mem q).1).1
      have hk : Submodule.span ℝ (pure C u) ≤ LinearMap.ker g :=
        Submodule.span_le.mpr (fun x hx => hz ⟨x, hx⟩)
      rw [pure_span hK hs hg] at hk
      exact hg0 (LinearMap.ker_eq_top.mp (top_le_iff.mp hk))
    obtain ⟨q, hq⟩ := hpos
    let L := g.toContinuousLinearMap
    obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn ⟨q, pure_mem q⟩
      L.continuous.continuousOn
    have hex : IsExposed ℝ (base C u) (L.toExposed (base C u)) :=
      ContinuousLinearMap.toExposed.isExposed
    obtain ⟨v, hv⟩ := (hex.isCompact hK).extremePoints_nonempty ⟨m, hm, hmax⟩
    let vp : pure C u := ⟨v, hex.isExtreme.extremePoints_subset_extremePoints hv⟩
    have hgv : 0 < g v := hq.trans_le (hv.1.2 q (pure_mem q))
    let f : V →ₗ[ℝ] ℝ := (g v)⁻¹ • g
    have hf : confirms C u vp f := by
      refine ⟨cone_bound hK hs ?_, ?_⟩
      · intro r
        change 0 ≤ (g v)⁻¹ * g r ∧ (g v)⁻¹ * g r ≤ 1
        refine ⟨mul_nonneg (inv_nonneg.mpr hgv.le)
          (hgt.1 r (pure_mem r).1).1, ?_⟩
        rw [← div_eq_inv_mul, div_le_one hgv]
        exact hv.1.2 r (pure_mem r)
      · simp [f, vp, hgv.ne']
    have ht : (t : V) ∈ exclusion C u vp :=
      ⟨pure_mem t, f, hf, by simp [f, hgt.2]⟩
    exact ⟨vp, (exclusion_symmetric vp t).mp ht, hv.1.2⟩

/-- Under faithful labels every full zero confirmer has exactly its labelled
singleton as its one-face, even among mixed states. -/
theorem full_zero_faces
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (s : pure C u) {h : V →ₗ[ℝ] ℝ} (hh : h ∈ fullZeroConfirmers C u s) :
    ({x | x ∈ base C u ∧ h x = 0} = exclusion C u s) ∧
    ({x | x ∈ base C u ∧ h x = 1} = {(s : V)}) := by
  constructor
  · ext x
    exact ⟨fun hx => ⟨hx.1, h, hh.1, hx.2⟩,
      fun hx => ⟨hx.1, hh.2 x hx⟩⟩
  have geom := (exclusion_ball_faces hc hs hg hB).1
  have hpure (v : pure C u) (hv : h v = 1) : v = s := by
    have hsub : exclusion C u s ⊆ exclusion C u v := by
      intro x hx
      exact ⟨hx.1, h, ⟨hh.1.1, hv⟩, hh.2 x hx⟩
    obtain ⟨b⟩ := hB v
    have he : exclusion C u s = exclusion C u v :=
      chart_face_eq b (geom s).2.2.1
        ((geom s).2.2.2.2.1.mono (geom v).2.2.2.2.1.subset hsub) (geom s).1
    exact (hInj he).symm
  let L := h.toContinuousLinearMap
  let F := L.toExposed (base C u)
  have hex : IsExposed ℝ (base C u) F := ContinuousLinearMap.toExposed.isExposed
  have hF : F = {x | x ∈ base C u ∧ h x = 1} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, le_antisymm
        (by simpa [hx.1.2] using (hh.1.1 x hx.1.1).2)
        (by
          have hb := hx.2 s (pure_mem s)
          change h s ≤ h x at hb
          simpa [hh.1.2] using hb)⟩
    · rintro ⟨hx, hx1⟩
      refine ⟨hx, fun y hy => ?_⟩
      change h y ≤ h x
      rw [hx1]
      simpa [hy.2] using (hh.1.1 y hy.1).2
  have hpoints : F.extremePoints ℝ ⊆ {(s : V)} := by
    intro v hv
    have hvp := hex.isExtreme.extremePoints_subset_extremePoints hv
    have hv1 := (hF ▸ hv.1).2
    exact congrArg Subtype.val (hpure ⟨v, hvp⟩ hv1)
  have hFs : F ⊆ {(s : V)} := by
    rw [← closure_convexHull_extremePoints (hex.isCompact (base_compact hc hs))
      (hex.convex (base_convex C u))]
    exact closure_minimal (convexHull_min hpoints (convex_singleton _)) isClosed_singleton
  rw [← hF]
  exact Set.Subset.antisymm hFs (Set.singleton_subset_iff.mpr
    (hF.symm ▸ (show (s : V) ∈ {x | x ∈ base C u ∧ h x = 1} from ⟨pure_mem s, hh.1.2⟩)))

/-- Restriction to every actual normalized state. -/
def stateReadout (f : V →ₗ[ℝ] ℝ) : C(base C u, ℝ) :=
  ⟨fun x => f x, f.continuous_of_finiteDimensional.comp continuous_subtype_val⟩

/-- The existing continuous-map supremum norm on the entire original K. -/
def stateNorm (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (f : V →ₗ[ℝ] ℝ) : ℝ :=
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  ‖stateReadout (C := C) (u := u) f‖

/-- The actual maximum value over the entire original exclusion. -/
def faceMaximum (t : pure C u) (h : V →ₗ[ℝ] ℝ) : ℝ :=
  sSup (h '' exclusion C u t)

/-- Distance to the image of the entire original zero-effect fiber in C(K,R). -/
def zeroDistance (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (t : pure C u) (h : V →ₗ[ℝ] ℝ) : ℝ :=
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  Metric.infDist (stateReadout (C := C) (u := u) h)
    (stateReadout (C := C) (u := u) '' zeroEffects C u t)

/-- Every original full zero confirmer has the claimed whole-state repair bound. -/
theorem fixed_zero_distance_bound
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (s t : pure C u) {h : V →ₗ[ℝ] ℝ} (hh : h ∈ fullZeroConfirmers C u s) :
    (1 - faceMaximum t h) / 2 ≤ zeroDistance hc hs t h := by
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  have hz : (0 : V →ₗ[ℝ] ℝ) ∈ zeroEffects C u t := by
    refine ⟨?_, by simp⟩
    intro x hx
    have hu : 0 ≤ u x := by
      by_cases h0 : x = 0
      · simp [h0]
      · exact (hs x hx h0).le
    simpa using hu
  change (1 - faceMaximum t h) / 2 ≤ Metric.infDist
    (stateReadout (C := C) (u := u) h) (stateReadout (C := C) (u := u) '' zeroEffects C u t)
  apply (Metric.le_infDist (Set.Nonempty.image (stateReadout (C := C) (u := u)) ⟨0, hz⟩)).mpr
  rintro _ ⟨g, hgt, rfl⟩
  obtain ⟨v, hvD, hvmax⟩ := zero_effect_maximizer hc hs hg hB t hgt
  have hb : BddAbove (h '' exclusion C u t) :=
    ((exclusion_ball_faces hc hs hg hB).1 t).2.1.bddAbove_image
      h.continuous_of_finiteDimensional.continuousOn
  have hvh : h v ≤ faceMaximum t h :=
    le_csSup hb (Set.mem_image_of_mem h hvD)
  let d := ‖stateReadout (C := C) (u := u) h - stateReadout g‖
  have ha := ((stateReadout (C := C) (u := u) h) - stateReadout g).norm_coe_le_norm
    ⟨s, pure_mem s⟩
  have hb' := ((stateReadout (C := C) (u := u) g) - stateReadout h).norm_coe_le_norm
    ⟨v, pure_mem v⟩
  rw [norm_sub_rev] at hb'
  change ‖h s - g s‖ ≤ d at ha
  change ‖g v - h v‖ ≤ d at hb'
  rw [Real.norm_eq_abs] at ha hb'
  have ha' := (abs_le.mp ha).2
  have hb'' := (abs_le.mp hb').2
  rw [hh.1.2] at ha'
  have hm := hvmax s (pure_mem s)
  rw [dist_eq_norm]
  change (1 - faceMaximum t h) / 2 ≤ d
  linarith

/-- One fixed full zero confirmer per edge, selected before all input sequences. -/
def stableZeroWitness (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) : Prop :=
  ∀ s r : pure C u, (r : V) ∈ exclusion C u s →
    ∃ h ∈ fullZeroConfirmers C u s, ∀ t : ℕ → pure C u,
      Filter.Tendsto (fun n => (t n : V)) Filter.atTop (nhds (r : V)) →
      ∃ g : ℕ → (V →ₗ[ℝ] ℝ), (∀ n, g n ∈ zeroEffects C u (t n)) ∧
        Filter.Tendsto (fun n => stateNorm hc hs (g n - h)) Filter.atTop (nhds 0)

/-- All original pure input sequences lift every actual orthogonal edge. -/
def openEdges : Prop :=
  ∀ p s : pure C u, (s : V) ∈ exclusion C u p →
    ∀ t : ℕ → pure C u,
      Filter.Tendsto (fun n => (t n : V)) Filter.atTop (nhds (p : V)) →
      ∃ v : ℕ → pure C u, (∀ n, (v n : V) ∈ exclusion C u (t n)) ∧
        Filter.Tendsto (fun n => (v n : V)) Filter.atTop (nhds (s : V))

/-- Qualitative fixed-witness stability implies the original all-index edge lifting.
The chosen pure maximizers include indices with identically zero effects; cluster
points are treated in K before singleton one-face rigidity is applied. -/
theorem stable_zero_implies_open_edges
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (hW : stableZeroWitness hc hs) : openEdges (C := C) (u := u) := by
  classical
  intro p s hsp t ht
  obtain ⟨h, hh, hstable⟩ := hW s p ((exclusion_symmetric p s).mp hsp)
  obtain ⟨g, hgt, hgn⟩ := hstable t ht
  have hmax (n : ℕ) : ∃ v : pure C u, (v : V) ∈ exclusion C u (t n) ∧
      faceMaximum (t n) h = h v := by
    have hD := (exclusion_ball_faces hc hs hg hB).1 (t n)
    let L := h.toContinuousLinearMap
    have hex : IsExposed ℝ (exclusion C u (t n))
        (L.toExposed (exclusion C u (t n))) := ContinuousLinearMap.toExposed.isExposed
    obtain ⟨m, hm, hmv⟩ := hD.2.1.exists_isMaxOn hD.1.nonempty
      L.continuous.continuousOn
    obtain ⟨v, hv⟩ := (hex.isCompact hD.2.1).extremePoints_nonempty ⟨m, hm, hmv⟩
    have hvP := (hD.2.2.2.2.1.trans hex.isExtreme).extremePoints_subset_extremePoints hv
    refine ⟨⟨v, hvP⟩, hv.1.1, ?_⟩
    apply le_antisymm
    · exact csSup_le (hD.1.nonempty.image h) (by
        rintro _ ⟨x, hx, rfl⟩
        exact hv.1.2 x hx)
    · exact le_csSup (hD.2.1.bddAbove_image L.continuous.continuousOn)
        (Set.mem_image_of_mem h hv.1.1)
  choose v hvD hvmax using hmax
  refine ⟨v, hvD, ?_⟩
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  let d := fun n => stateNorm hc hs (g n - h)
  have hvlow (n : ℕ) : 1 - 2 * d n ≤ h (v n) := by
    have hb := fixed_zero_distance_bound hc hs hg hB s (t n) hh
    have hd : zeroDistance hc hs (t n) h ≤ d n := by
      have hi := Metric.infDist_le_dist_of_mem
        (y := stateReadout (C := C) (u := u) (g n))
        (s := stateReadout (C := C) (u := u) '' zeroEffects C u (t n))
        (x := stateReadout (C := C) (u := u) h)
        (Set.mem_image_of_mem (stateReadout (C := C) (u := u)) (hgt n))
      rw [dist_eq_norm, norm_sub_rev] at hi
      have he : stateReadout (C := C) (u := u) (g n - h) =
          stateReadout (g n) - stateReadout h := by ext x; rfl
      simpa only [zeroDistance, d, stateNorm, he] using hi
    rw [hvmax n] at hb
    linarith
  have hvhigh (n : ℕ) : h (v n) ≤ 1 := by
    simpa [(pure_mem (v n)).2] using (hh.1.1 (v n) (pure_mem (v n)).1).2
  have hconv : Filter.Tendsto (fun n => h (v n)) Filter.atTop (nhds 1) := by
    have hd : Filter.Tendsto d Filter.atTop (nhds 0) := hgn
    have hlo : Filter.Tendsto (fun n => 1 - 2 * d n) Filter.atTop (nhds 1) := by
      convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hd) using 1 <;> norm_num
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds hvlow hvhigh
  apply (base_compact hc hs).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall (fun n => pure_mem (v n)))
  intro x hx hcluster
  have hcx := hcluster.continuousAt_comp h.continuous_of_finiteDimensional.continuousAt
  have hcl : ClusterPt (h x) (nhds (1 : ℝ)) := hcx.clusterPt.mono hconv
  have hx1 : h x = 1 := by
    by_contra hne
    exact hcl.ne ((disjoint_nhds_nhds.mpr hne).eq_bot)
  have hxS : x ∈ ({(s : V)} : Set V) := by
    rw [← (full_zero_faces hc hs hg hB hInj s hh).2]
    exact ⟨hx, hx1⟩
  exact hxS

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Recover every point of a whole compact Hausdorff limit along the same indices. -/
private theorem recover_limit (F : ℕ → NonemptyCompacts V) (G : NonemptyCompacts V)
    (hF : Tendsto F atTop (𝓝 G)) {y : V} (hy : y ∈ G) :
    ∃ yn : ℕ → V, (∀ n, yn n ∈ F n) ∧ Tendsto yn atTop (𝓝 y) := by
  choose yn hyn heq using fun n =>
    (F n).isCompact.exists_infDist_eq_dist (F n).nonempty y
  refine ⟨yn, hyn, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  have hi := ((NonemptyCompacts.lipschitz_infDist_const y).continuous.tendsto G).comp hF
  simpa only [Function.comp_def, Metric.infDist_zero_of_mem hy, heq, dist_comm] using hi

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem mem_compact_limit (F : ℕ → NonemptyCompacts V) (G : NonemptyCompacts V)
    (hF : Tendsto F atTop (𝓝 G)) {yn : ℕ → V} {y : V}
    (hyn : ∀ n, yn n ∈ F n) (hy : Tendsto yn atTop (𝓝 y)) : y ∈ G := by
  have hi := NonemptyCompacts.lipschitz_infDist.continuous.tendsto (y, G) |>.comp
    (hy.prodMk_nhds hF)
  have hz : Metric.infDist y G = 0 := tendsto_nhds_unique hi (by
    simpa only [Function.comp_def, Metric.infDist_zero_of_mem (hyn _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  exact G.isCompact.isClosed.mem_iff_infDist_zero G.nonempty |>.mpr hz

/-- One limit effect simultaneously vanishes on the entire compact limit. -/
private theorem whole_limit_effect
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (pn : ℕ → pure C u) {x : V}
    (hpx : Tendsto (fun n => (pn n : V)) atTop (𝓝 x))
    (G : NonemptyCompacts V)
    (hG : Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) G) atTop (𝓝 0)) :
    x ∈ base C u ∧ (G : Set V) ⊆ base C u ∧
      ∃ e ∈ effects C u, e x = 1 ∧ ∀ y ∈ G, e y = 0 := by
  let F (n : ℕ) : NonemptyCompacts V :=
    ⟨⟨exclusion C u (pn n), ((exclusion_ball_faces hc hs hg hB).1 (pn n)).2.1⟩,
      ((exclusion_ball_faces hc hs hg hB).1 (pn n)).1.nonempty⟩
  have hFG : Tendsto F atTop (𝓝 G) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact hG
  choose e he hz using fun n => ((exclusion_ball_faces hc hs hg hB).1 (pn n)).2.2.2.2.2.2
  obtain ⟨b, hb, φ, hφ, heb⟩ := (effects_compact hs hg).tendsto_subseq
    (fun n => (show (e n).toContinuousLinearMap ∈ effects C u from (he n).1))
  have ev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have hbx : b x = 1 := by
    apply tendsto_nhds_unique ((ev.tendsto (b, x)).comp
      (heb.prodMk_nhds (hpx.comp hφ.tendsto_atTop)))
    change Tendsto (fun n => e (φ n) (pn (φ n))) atTop (𝓝 1)
    have hh (n : ℕ) : e (φ n) (pn (φ n)) = 1 := (he (φ n)).2
    simpa only [hh] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hyK (y : V) (hy : y ∈ G) : y ∈ base C u := by
    obtain ⟨yn, hyn, hyt⟩ := recover_limit F G hFG hy
    exact (base_compact hc hs).isClosed.mem_of_tendsto hyt
      (Eventually.of_forall fun n => (hyn n).1)
  refine ⟨(base_compact hc hs).isClosed.mem_of_tendsto hpx
    (Eventually.of_forall fun n => pure_mem (pn n)), hyK, b, hb, hbx, ?_⟩
  intro y hy
  obtain ⟨yn, hyn, hyt⟩ := recover_limit F G hFG hy
  apply tendsto_nhds_unique ((ev.tendsto (b, y)).comp
    (heb.prodMk_nhds (hyt.comp hφ.tendsto_atTop)))
  have hzero (n : ℕ) : e (φ n) (yn (φ n)) = 0 := by
    have hyD : yn (φ n) ∈ exclusion C u (pn (φ n)) := hyn (φ n)
    exact (hz (φ n) ▸ hyD).2
  change Tendsto (fun n => e (φ n) (yn (φ n))) atTop (𝓝 0)
  simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Full original label criterion, including mixed singleton limits and pure upper graph. -/
theorem exclusion_limit_labels
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (pn : ℕ → pure C u) {x : V}
    (hpx : Tendsto (fun n => (pn n : V)) atTop (𝓝 x))
    (G : NonemptyCompacts V)
    (hG : Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) G) atTop (𝓝 0)) :
    (Function.Injective (fun p : pure C u => exclusion C u p) →
      ((G : Set V).Nontrivial → x ∈ pure C u) ∧
    (∀ q : V, (G : Set V) = {q} → x ∉ pure C u →
      q ∈ pure C u ∧ x ∈ intrinsicInterior ℝ (exclusion C u q))) ∧
    (x ∈ pure C u → (G : Set V) ⊆ exclusion C u x) := by
  obtain ⟨hxK, hGK, e, he, hex, heG⟩ := whole_limit_effect hc hs hg hB pn hpx G hG
  refine ⟨?_, ?_⟩
  · intro hInj
    constructor
    · rintro ⟨y, hy, z, hz, hyz⟩
      exact common_zero_pure hc hs hg hB hInj hxK (hGK hy) (hGK hz) hyz he hex
        (heG y hy) (heG z hz)
    · intro q hGq hx
      have hqG : q ∈ G := by change q ∈ (G : Set V); rw [hGq]; exact Set.mem_singleton q
      have heq : e q = 0 := heG q hqG
      let H := e.toExposed (base C u)
      have hH : IsExposed ℝ (base C u) H := ContinuousLinearMap.toExposed.isExposed
      have hxH : x ∈ H := by
        refine ⟨hxK, fun z hz => ?_⟩
        change e z ≤ e x
        rw [hex]
        simpa [hz.2] using (he z hz.1).2
      obtain ⟨p, hp⟩ := (hH.isCompact (base_compact hc hs)).extremePoints_nonempty ⟨x, hxH⟩
      have hpP : p ∈ pure C u := hH.isExtreme.extremePoints_subset_extremePoints hp
      have hpxne : x ≠ p := fun h => hx (h ▸ hpP)
      have hep : e p = 1 := by
        apply le_antisymm
        · simpa [(pure_mem ⟨p, hpP⟩).2] using (he p (pure_mem ⟨p, hpP⟩).1).2
        · simpa [hex] using hp.1.2 x hxK
      let b := u.toContinuousLinearMap - e
      have hb : b ∈ effects C u := by
        intro z hz
        have hez : 0 ≤ e z ∧ e z ≤ u z := he z hz
        change 0 ≤ u z - e z ∧ u z - e z ≤ u z
        constructor <;> linarith
      have hbq : b q = 1 := by
        change u q - e q = 1
        rw [(hGK hqG).2, heq]; norm_num
      have hbx : b x = 0 := by change u x - e x = 0; rw [hxK.2, hex]; norm_num
      have hbp : b p = 0 := by
        change u p - e p = 0
        rw [(pure_mem ⟨p, hpP⟩).2, hep]; norm_num
      have hqP := common_zero_pure hc hs hg hB hInj (hGK hqG) hxK
        (pure_mem ⟨p, hpP⟩) hpxne hb hbq hbx hbp
      have hxD : x ∈ exclusion C u q := ⟨hxK, b.toLinearMap, ⟨hb, hbq⟩, hbx⟩
      refine ⟨hqP, ?_⟩
      obtain ⟨chart⟩ := hB ⟨q, hqP⟩
      haveI : Nonempty (Fin chart.dim) := ⟨⟨0, chart.dim_pos⟩⟩
      have hfront : intrinsicFrontier ℝ (exclusion C u q) =
          exclusion C u q ∩ pure C u := by
        rw [← chart.whole, intrinsic_image chart.param chart.injective, intrinsic_ball]
        simpa only [chart.whole] using (chart_boundary hc hs hg hB ⟨q, hqP⟩ chart).symm
      have hxnot : x ∉ intrinsicFrontier ℝ (exclusion C u q) := by
        rw [hfront]
        exact fun h => hx h.2
      rw [← closure_sdiff_intrinsicFrontier]
      exact ⟨subset_closure hxD, hxnot⟩
  · intro hx y hy
    exact ⟨hGK hy, e.toLinearMap, ⟨he, hex⟩, heG y hy⟩

private theorem compact_maximum_tendsto (F : ℕ → NonemptyCompacts V)
    (G : NonemptyCompacts V) (hF : Tendsto F atTop (𝓝 G)) (h : V →ₗ[ℝ] ℝ) :
    Tendsto (fun n => sSup (h '' (F n : Set V))) atTop (𝓝 (sSup (h '' (G : Set V)))) := by
  obtain ⟨y, hy, hmax⟩ := G.isCompact.exists_sSup_image_eq G.nonempty
    h.continuous_of_finiteDimensional.continuousOn
  obtain ⟨yn, hyn, hyt⟩ := recover_limit F G hF hy
  have hhv := h.continuous_of_finiteDimensional.tendsto y |>.comp hyt
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hev : ∀ᶠ n in atTop, a < h (yn n) := hhv.eventually (lt_mem_nhds (by simpa [hmax] using ha))
    exact hev.mono fun n hn => hn.trans_le (le_csSup
      ((F n).isCompact.bddAbove_image h.continuous_of_finiteDimensional.continuousOn)
      (Set.mem_image_of_mem h (hyn n)))
  · intro a ha
    let b := (sSup (h '' (G : Set V)) + a) / 2
    have hmb : sSup (h '' (G : Set V)) < b := by dsimp [b]; linarith
    have hba : b < a := by dsimp [b]; linarith
    have hsub : (G : Set V) ⊆ {z | h z < b} := by
      intro z hz
      exact (le_csSup (G.isCompact.bddAbove_image h.continuous_of_finiteDimensional.continuousOn)
        (Set.mem_image_of_mem h hz)).trans_lt hmb
    have hev := hF.eventually_mem ((NonemptyCompacts.isOpen_subsets_of_isOpen
      (isOpen_lt h.continuous_of_finiteDimensional continuous_const)).mem_nhds hsub)
    exact hev.mono fun n hn => (csSup_le ((F n).nonempty.image h)
      (by rintro _ ⟨z, hz, rfl⟩; exact (hn hz).le)).trans_lt hba

/-- A proper common whole-face limit obstructs every fixed test on one selected edge. -/
private theorem fixed_tests_of_proper_limit
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (s r : pure C u) (hrs : (r : V) ∈ exclusion C u s)
    (tn : ℕ → pure C u) (htr : Tendsto (fun n => (tn n : V)) atTop (𝓝 (r : V)))
    (G : NonemptyCompacts V) (hGK : (G : Set V) ⊆ base C u) (hsG : (s : V) ∉ G)
    (hG : Tendsto (fun n => Metric.hausdorffDist (exclusion C u (tn n)) G) atTop (𝓝 0)) :
    ∀ h ∈ fullZeroConfirmers C u s,
      Tendsto (fun n => h (tn n)) atTop (𝓝 0) ∧
      0 < liminf (fun n => zeroDistance hc hs (tn n) h) atTop := by
  intro h hh
  have hhr : h r = 0 := hh.2 r hrs
  refine ⟨by simpa only [Function.comp_def, hhr] using h.continuous_of_finiteDimensional.tendsto (r : V) |>.comp htr, ?_⟩
  let F (n : ℕ) : NonemptyCompacts V :=
    ⟨⟨exclusion C u (tn n), ((exclusion_ball_faces hc hs hg hB).1 (tn n)).2.1⟩,
      ((exclusion_ball_faces hc hs hg hB).1 (tn n)).1.nonempty⟩
  have hFG : Tendsto F atTop (𝓝 G) := tendsto_iff_dist_tendsto_zero.mpr hG
  let m := sSup (h '' (G : Set V))
  obtain ⟨y, hy, hmy⟩ := G.isCompact.exists_sSup_image_eq G.nonempty
    h.continuous_of_finiteDimensional.continuousOn
  have hm : m < 1 := by
    have hyK := hGK hy
    have hle : h y ≤ 1 := by simpa [hyK.2] using (hh.1.1 y hyK.1).2
    have hne : h y ≠ 1 := by
      intro heq
      have hyS : y ∈ ({(s : V)} : Set V) := by
        rw [← (full_zero_faces hc hs hg hB hInj s hh).2]
        exact ⟨hyK, heq⟩
      exact hsG (Set.mem_singleton_iff.mp hyS ▸ hy)
    change sSup (h '' (G : Set V)) < 1
    rw [hmy]
    exact lt_of_le_of_ne hle hne
  have hmax : Tendsto (fun n => faceMaximum (tn n) h) atTop (𝓝 m) :=
    compact_maximum_tendsto F G hFG h
  let δ := (1 - m) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlow : Tendsto (fun n => (1 - faceMaximum (tn n) h) / 2)
      atTop (𝓝 ((1 - m) / 2)) := (tendsto_const_nhds.sub hmax).div_const 2
  have hev : ∀ᶠ n in atTop, δ ≤ zeroDistance hc hs (tn n) h := by
    have hlt : δ < (1 - m) / 2 := by dsimp [δ]; linarith
    exact (hlow.eventually (lt_mem_nhds hlt)).mono fun n hn =>
      hn.le.trans (fixed_zero_distance_bound hc hs hg hB s (tn n) hh)
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  have hzero : stateReadout (C := C) (u := u) (0 : V →ₗ[ℝ] ℝ) = 0 := by ext x; rfl
  have hdub (n : ℕ) : zeroDistance hc hs (tn n) h ≤ stateNorm hc hs h := by
    have hz : (0 : V →ₗ[ℝ] ℝ) ∈ zeroEffects C u (tn n) := by
      refine ⟨?_, by simp⟩
      intro z hz
      have hu : 0 ≤ u z := by
        by_cases he : z = 0
        · simp [he]
        · exact (hs z hz he).le
      simpa using hu
    have hi := Metric.infDist_le_dist_of_mem
      (x := stateReadout (C := C) (u := u) h)
      (s := stateReadout (C := C) (u := u) '' zeroEffects C u (tn n))
      (Set.mem_image_of_mem (stateReadout (C := C) (u := u)) hz)
    simpa only [zeroDistance, stateNorm, hzero, dist_zero_right] using hi
  exact hδ.trans_le (le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hdub) hev)

/-- The original whole-ball collapse obstructs all fixed complete zero tests on one edge. -/
theorem fixed_zero_distance_obstruction
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : ∀ p : pure C u, ∃ b : ExclusionChart C u p, b.dim = 3)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (pn : ℕ → pure C u) {x q : V}
    (hpx : Tendsto (fun n => (pn n : V)) atTop (𝓝 x))
    (hcollapse : Tendsto (fun n => Metric.hausdorffDist
      (exclusion C u (pn n)) {q}) atTop (𝓝 0)) :
    ∃ s r : pure C u, (r : V) ∈ exclusion C u s ∧
      ∃ tn : ℕ → pure C u,
        Tendsto (fun n => (tn n : V)) atTop (𝓝 (r : V)) ∧
        ∀ h ∈ fullZeroConfirmers C u s,
          Tendsto (fun n => h (tn n)) atTop (𝓝 0) ∧
          0 < liminf (fun n => zeroDistance hc hs (tn n) h) atTop := by
  classical
  have hB : exclusionBalls C u := fun p => ⟨(h3 p).choose⟩
  let Q : NonemptyCompacts V := {q}
  let F (n : ℕ) : NonemptyCompacts V :=
    ⟨⟨exclusion C u (pn n), ((exclusion_ball_faces hc hs hg hB).1 (pn n)).2.1⟩,
      ((exclusion_ball_faces hc hs hg hB).1 (pn n)).1.nonempty⟩
  have hFQ : Tendsto F atTop (𝓝 Q) := tendsto_iff_dist_tendsto_zero.mpr hcollapse
  have hlabels := exclusion_limit_labels hc hs hg hB pn hpx Q hcollapse
  have hQK : (Q : Set V) ⊆ base C u := (whole_limit_effect hc hs hg hB pn hpx Q hcollapse).2.1
  by_cases hx : x ∈ pure C u
  · let r : pure C u := ⟨x, hx⟩
    obtain ⟨a, b, ha, hb, hab⟩ := pure_pair_in_ball hc hs hg hB r
    obtain ⟨s, hsD, hsQ⟩ : ∃ s : pure C u,
        (s : V) ∈ exclusion C u r ∧ (s : V) ∉ Q := by
      by_cases haq : (a : V) = q
      · refine ⟨b, hb, ?_⟩
        intro hbq
        apply hab
        apply Subtype.ext
        exact haq.trans (Set.mem_singleton_iff.mp hbq).symm
      · exact ⟨a, ha, haq⟩
    have hrs := (exclusion_symmetric r s).mp hsD
    exact ⟨s, r, hrs, pn, hpx,
      fixed_tests_of_proper_limit hc hs hg hB hInj s r hrs pn hpx Q hQK hsQ hcollapse⟩
  · obtain ⟨hq, hxri⟩ := (hlabels.1 hInj).2 q rfl hx
    let r : pure C u := ⟨q, hq⟩
    have hchoose (n : ℕ) : ∃ t : pure C u, (t : V) ∈ exclusion C u (pn n) := by
      have g := (exclusion_ball_faces hc hs hg hB).1 (pn n)
      obtain ⟨t, ht⟩ := g.2.1.extremePoints_nonempty g.1.nonempty
      exact ⟨⟨t, g.2.2.2.2.1.extremePoints_subset_extremePoints ht⟩, ht.1⟩
    choose tn htnD using hchoose
    have htr : Tendsto (fun n => (tn n : V)) atTop (𝓝 (r : V)) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hsub : (Q : Set V) ⊆ Metric.ball q ε := by
        intro z hz
        have hzq : z = q := hz
        subst z
        simpa using hε
      have hev := hFQ.eventually_mem
        ((NonemptyCompacts.isOpen_subsets_of_isOpen Metric.isOpen_ball).mem_nhds hsub)
      exact hev.mono fun n hn => hn (htnD n)
    have hswap (n : ℕ) : (pn n : V) ∈ exclusion C u (tn n) :=
      (exclusion_symmetric (pn n) (tn n)).mp (htnD n)
    let H (n : ℕ) : NonemptyCompacts V :=
      ⟨⟨exclusion C u (tn n), ((exclusion_ball_faces hc hs hg hB).1 (tn n)).2.1⟩,
        ((exclusion_ball_faces hc hs hg hB).1 (tn n)).1.nonempty⟩
    obtain ⟨G, hGK, φ, hφ, hHG⟩ :=
      (NonemptyCompacts.isCompact_subsets_of_isCompact (base_compact hc hs)).tendsto_subseq
        (fun n => (show (H n : Set V) ⊆ base C u from fun z hz => hz.1))
    have hconv : Convex ℝ (G : Set V) := by
      intro y hy z hz a b ha hb hab
      obtain ⟨yn, hyn, hyt⟩ := recover_limit (fun n => H (φ n)) G hHG hy
      obtain ⟨zn, hzn, hzt⟩ := recover_limit (fun n => H (φ n)) G hHG hz
      exact mem_compact_limit (fun n => H (φ n)) G hHG
        (fun n => ((exclusion_ball_faces hc hs hg hB).1 (tn (φ n))).2.2.1
          (hyn n) (hzn n) ha hb hab)
        ((hyt.const_smul a).add (hzt.const_smul b))
    have hxG : x ∈ G := mem_compact_limit (fun n => H (φ n)) G hHG
      (fun n => hswap (φ n)) (hpx.comp hφ.tendsto_atTop)
    have hGdist : Tendsto (fun n => Metric.hausdorffDist
        (exclusion C u (tn (φ n))) G) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hHG
    have htφ := htr.comp hφ.tendsto_atTop
    have hsub : (G : Set V) ⊆ exclusion C u r :=
      (exclusion_limit_labels hc hs hg hB (fun n => tn (φ n)) htφ G hGdist).2 hq
    have hcharts (p : pure C u) : ∃ a : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] V,
        Function.Injective a ∧ a '' Metric.closedBall 0 1 = exclusion C u p := by
      obtain ⟨⟨d, hd, a, ha, hw⟩, he⟩ := h3 p
      dsimp only at he
      subst d
      exact ⟨a, ha, hw⟩
    choose a ha hw using hcharts
    let chart (p : pure C u) : ExclusionChart C u p := ⟨3, by decide, a p, ha p, hw p⟩
    have hfront (p : pure C u) : intrinsicFrontier ℝ (exclusion C u p) =
        exclusion C u p ∩ pure C u := by
      rw [← hw p, intrinsic_image _ (ha p), intrinsic_ball]
      simpa only [hw] using (chart_boundary hc hs hg hB p (chart p)).symm
    have hproper : (G : Set V) ≠ exclusion C u r := by
      intro heq
      have hd : Tendsto (fun n => Metric.hausdorffDist
          (a (tn (φ n)) '' Metric.closedBall 0 1) (a r '' Metric.closedBall 0 1))
          atTop (𝓝 0) := by simpa only [hw, ← heq] using hGdist
      have hboundary := (affine_ball_boundary_limit (fun n => a (tn (φ n))) (a r)
        (fun n => ha _) (ha r) hd).2 (fun n => (pn (φ n) : V)) x
        (fun n => by rw [hw, hfront]; exact ⟨hswap (φ n), (pn (φ n)).property⟩)
        (hpx.comp hφ.tendsto_atTop)
      have hxf : x ∈ intrinsicFrontier ℝ (exclusion C u r) := by
        simpa only [hw] using hboundary
      have hnot : x ∉ intrinsicFrontier ℝ (exclusion C u r) := by
        rw [← closure_sdiff_intrinsicInterior]
        exact fun h => h.2 hxri
      exact hnot hxf
    obtain ⟨s, hsD, hsG⟩ : ∃ s : pure C u,
        (s : V) ∈ exclusion C u r ∧ (s : V) ∉ G := by
      by_contra! hn
      have hall : (exclusion C u r).extremePoints ℝ ⊆ (G : Set V) := by
        intro z hz
        have hzP := ((exclusion_ball_faces hc hs hg hB).1 r).2.2.2.2.1.extremePoints_subset_extremePoints hz
        exact hn ⟨z, hzP⟩ hz.1
      apply hproper
      apply Set.Subset.antisymm hsub
      rw [← closure_convexHull_extremePoints
        ((exclusion_ball_faces hc hs hg hB).1 r).2.1
        ((exclusion_ball_faces hc hs hg hB).1 r).2.2.1]
      exact closure_minimal (convexHull_min hall hconv) G.isCompact.isClosed
    have hrs := (exclusion_symmetric r s).mp hsD
    exact ⟨s, r, hrs, (fun n => tn (φ n)), htφ,
      fixed_tests_of_proper_limit hc hs hg hB hInj s r hrs (fun n => tn (φ n)) htφ
        G hGK hsG hGdist⟩

#print axioms fixed_zero_distance_obstruction

#print axioms exclusion_limit_labels
#print axioms zero_effect_maximizer
#print axioms full_zero_faces
#print axioms fixed_zero_distance_bound
#print axioms stable_zero_implies_open_edges

end D5.S3.Quantum.Foundation.FixedZeroObstruction
