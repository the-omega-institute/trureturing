/- GID: D5/S3/Quantum/Foundation/OriginalExclusionLimits
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalExclusionLimits
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original whole-exclusion collapse and exact regular-region continuity. -/

import D5.S3.Quantum.Foundation.OriginalNormalFamily

noncomputable section
open Set Filter Topology TopologicalSpace

namespace D5.S3.Quantum.Foundation.OriginalExclusionLimits
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces OriginalFacePolarity
open ExclusionIncidence ReciprocalExclusionLimits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The original EB3 data supplies the full positive-dimensional ball condition. -/
theorem ballHyp (h3 : threeBallExclusions C u) : exclusionBalls C u := fun s =>
  ⟨⟨3, by norm_num, (h3 s).choose, (h3 s).choose_spec.1, (h3 s).choose_spec.2⟩⟩

/-- The actual whole exclusion as a nonempty compact set. -/
def wholeExclusion
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : NonemptyCompacts V :=
  ⟨⟨exclusion C u p, ((exclusion_ball_faces hc hs hg hB).1 p).2.1⟩,
    ((exclusion_ball_faces hc hs hg hB).1 p).1.nonempty⟩

/-- Every actual Hausdorff discontinuity has a whole-ball singleton-collapse
witness with original pure labels and a pure point in the old whole exclusion. -/
theorem original_discontinuity_collapse
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (p : pure C u)
    (hdisc : ¬ ContinuousAt (wholeExclusion hc hs hg (ballHyp h3)) p) :
    ∃ pn : ℕ → pure C u, Tendsto pn atTop (𝓝 p) ∧
      ∃ q : pure C u, (q : V) ∈ exclusion C u p ∧
        Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)})
          atTop (𝓝 0) := by
  classical
  let hB := ballHyp h3
  let D := wholeExclusion hc hs hg hB
  by_contra hno
  apply hdisc
  change Tendsto D (𝓝 p) (𝓝 (D p))
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro pn hp
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨Q, _, ms, hms, hlim⟩ :=
    (NonemptyCompacts.isCompact_subsets_of_isCompact (base_compact hc hs)).tendsto_subseq
      (fun n => (show (D (pn (ns n)) : Set V) ⊆ base C u from fun x hx => hx.1))
  have hpn : Tendsto (fun n => pn (ns (ms n))) atTop (𝓝 p) :=
    (hp.comp hns).comp hms.tendsto_atTop
  rcases exclusion_limit_dichotomy hc hs hg h3 hPR hpn
      (fun n => D (pn (ns (ms n)))) Q (fun _ => rfl) hlim with heq | ⟨q, hq, heq⟩
  · refine ⟨ms, ?_⟩
    have hQD : Q = D p := NonemptyCompacts.ext heq
    simpa only [hQD, Function.comp_def] using hlim
  · exfalso
    apply hno
    refine ⟨fun n => pn (ns (ms n)), hpn, q, hq, ?_⟩
    have ht := tendsto_iff_dist_tendsto_zero.mp hlim
    simpa only [NonemptyCompacts.dist_eq, heq, Function.comp_def, D, wholeExclusion,
      NonemptyCompacts.coe_mk, Compacts.coe_mk] using ht

private theorem compact_diameter_control (S T : NonemptyCompacts V) :
    Metric.diam (S : Set V) ≤ Metric.diam (T : Set V) + 2 * dist S T := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨x', hx', hxx'⟩ := T.isCompact.exists_infDist_eq_dist T.nonempty x
  obtain ⟨y', hy', hyy'⟩ := T.isCompact.exists_infDist_eq_dist T.nonempty y
  have hdx : dist x x' ≤ dist S T := by
    rw [← hxx']
    exact Metric.infDist_le_hausdorffDist_of_mem hx (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      S.nonempty T.nonempty S.isCompact.isBounded T.isCompact.isBounded)
  have hdy : dist y y' ≤ dist S T := by
    rw [← hyy']
    exact Metric.infDist_le_hausdorffDist_of_mem hy (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      S.nonempty T.nonempty S.isCompact.isBounded T.isCompact.isBounded)
  have hxy := Metric.dist_le_diam_of_mem T.isCompact.isBounded hx' hy'
  have ht := dist_triangle4 x x' y' y
  rw [dist_comm y' y] at ht
  linarith

theorem compact_diameter_lipschitz :
    LipschitzWith 2 (fun S : NonemptyCompacts V => Metric.diam (S : Set V)) := by
  apply LipschitzWith.of_dist_le_mul
  intro S T
  rw [Real.dist_eq]
  change |Metric.diam (S : Set V) - Metric.diam (T : Set V)| ≤ 2 * dist S T
  apply abs_le.mpr
  constructor
  · have h := compact_diameter_control T S
    rw [dist_comm T S] at h
    linarith
  · have h := compact_diameter_control S T
    linarith

/-- The IX115 regular region; the indexing j+1 ranges over every positive integer. -/
def regularRegion (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Set (pure C u) :=
  ⋃ j : ℕ, interior {p : pure C u | 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u p)}

/-- The regular region is exactly the whole Hausdorff continuity set. -/
theorem original_regular_iff_continuous
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (p : pure C u) :
    p ∈ regularRegion C u ↔ ContinuousAt (wholeExclusion hc hs hg (ballHyp h3)) p := by
  let D := wholeExclusion hc hs hg (ballHyp h3)
  constructor
  · intro hpreg
    obtain ⟨j, hj⟩ := mem_iUnion.mp hpreg
    by_contra hdisc
    obtain ⟨pn, hpn, q, _, hcollapse⟩ := original_discontinuity_collapse hc hs hg h3 hPR p hdisc
    have ht : Tendsto (fun n => D (pn n)) atTop (𝓝 ({(q : V)} : NonemptyCompacts V)) :=
      tendsto_iff_dist_tendsto_zero.mpr hcollapse
    have hd := (compact_diameter_lipschitz.continuous.tendsto
      ({(q : V)} : NonemptyCompacts V)).comp ht
    have hsmall : ∀ᶠ n in atTop,
        1 / (j + 1 : ℝ) ≤ Metric.diam (D (pn n) : Set V) :=
      (hpn.eventually (isOpen_interior.mem_nhds hj)).mono fun n h =>
        (show 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u (pn n)) from
          (interior_subset : interior {r : pure C u |
            1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u r)} ⊆
            {r : pure C u | 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u r)}) h)
    have hbad : 1 / (j + 1 : ℝ) ≤ 0 := by
      simpa using ge_of_tendsto hd hsmall
    exact (one_div_pos.mpr (by positivity : 0 < (j + 1 : ℝ))).not_ge hbad
  · intro hcont
    have hgeom := (exclusion_ball_faces hc hs hg (ballHyp h3)).1 p
    have hdpos : 0 < Metric.diam (D p : Set V) := Metric.diam_pos hgeom.1 hgeom.2.1.isBounded
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hdpos
    have hdi := compact_diameter_lipschitz.continuous.continuousAt.comp hcont
    have hn : {s : pure C u | 1 / (j + 1 : ℝ) < Metric.diam (D s : Set V)} ∈ 𝓝 p :=
      hdi.preimage_mem_nhds (Ioi_mem_nhds hj)
    exact mem_iUnion.mpr ⟨j, mem_interior_iff_mem_nhds.mpr
      (mem_of_superset hn fun x h =>
        (show 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u x) from
          (show 1 / (j + 1 : ℝ) < Metric.diam (D x : Set V) from h).le))⟩

#print axioms original_discontinuity_collapse

end D5.S3.Quantum.Foundation.OriginalExclusionLimits
