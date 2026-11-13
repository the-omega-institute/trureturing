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

/-! Full original effects and state body; no closed pure locus or least effects are assumed. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.FixedZeroObstruction

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces

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

#print axioms zero_effect_maximizer
#print axioms full_zero_faces
#print axioms fixed_zero_distance_bound
#print axioms stable_zero_implies_open_edges

end D5.S3.Quantum.Foundation.FixedZeroObstruction
