/- GID: D5/S1/Dynamics/Shadowing/FiniteGraphBowenArcs
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteGraphBowenArcs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separation of short arcs immersed by every iterate on finite graphs. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphSmallArcs
import Mathlib.Dynamics.PeriodicPts.Defs

/-! Iterated small arcs in the finite affine graph realization. -/

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing

/-- A continuous finitely positively expansive map of a compact metric space
has only finitely many points of each positive period. -/
theorem finite_ptsOfPeriod_of_finitelyPositiveExpansive {X : Type*}
    [MetricSpace X] [CompactSpace X] {f : X → X} (hf : Continuous f)
    (hfinite : FinitelyPositiveExpansive f) {p : ℕ} (hp : 0 < p) :
    (ptsOfPeriod f p).Finite := by
  obtain ⟨ε, hε, N, _, hB⟩ := hfinite
  obtain ⟨δ, hδ, hBδ⟩ := IntervalObstruction.forwardBowenBound_iterate
    isCompact_univ hf.continuousOn (mapsTo_univ f univ) hε hB hp
  obtain ⟨C, _, hC, hcover⟩ := (isCompact_univ : IsCompact (univ : Set X)).finite_cover_balls
    (show 0 < δ / 3 by positivity)
  have hcell (c : X) : (ptsOfPeriod f p ∩ Metric.ball c (δ / 3)).Finite := by
    rcases (ptsOfPeriod f p ∩ Metric.ball c (δ / 3)).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he]
      exact finite_empty
    · refine IntervalObstruction.finite_of_all_times_small hBδ (subset_univ _) x hx ?_
      intro y hy n
      have hxfix : IsFixedPt (f^[p]) x := hx.1
      have hyfix : IsFixedPt (f^[p]) y := hy.1
      rw [hxfix.iterate n, hyfix.iterate n]
      have hxc := Metric.mem_ball.mp hx.2
      have hyc := Metric.mem_ball.mp hy.2
      linarith [dist_triangle x c y, dist_comm c y]
  refine (hC.biUnion (fun c _ => hcell c)).subset ?_
  intro x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  exact mem_iUnion₂.mpr ⟨c, hc, hx, hxc⟩

end D5.S1.Dynamics.Shadowing

namespace D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {f : Space G → Space G}

/-- At a uniform positive scale, the endpoints of any nondegenerate arc of small
diameter must separate if every iterate of its parametrization is locally
injective at interior parameters. -/
theorem separates_immersed_interval_endpoints (hf : Continuous f)
    (hfinite : FinitelyPositiveExpansive f) :
    ∃ δ > 0, ∀ (g : ℝ → Space G) {a b : ℝ}, a < b →
      ContinuousOn g (Icc a b) →
      Metric.diam (g '' Icc a b) < δ →
      (∀ n : ℕ, ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn (f^[n] ∘ g) U) →
      ∃ n : ℕ, δ ≤ dist (f^[n] (g a)) (f^[n] (g b)) := by
  obtain ⟨ε, hε, N, _, hB⟩ := hfinite
  let r : ℝ := 1 / 8
  have hr : 0 < r := by norm_num [r]
  have hr' : r < 1 / 4 := by norm_num [r]
  obtain ⟨γ, hγ, hγcontrol⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) r hr
  let δ := min r (min ε γ)
  have hδ : 0 < δ := lt_min hr (lt_min hε hγ)
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδγ : δ ≤ γ := (min_le_right _ _).trans (min_le_right _ _)
  have hδr : δ ≤ r := min_le_left _ _
  refine ⟨δ, hδ, ?_⟩
  intro g a b hab hg hdiam hloc
  by_contra! hclose
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hbound (n : ℕ) : Bornology.IsBounded ((f^[n] ∘ g) '' Icc a b) :=
    Metric.isBounded_of_compactSpace
  have hiterdiam (n : ℕ) : Metric.diam ((f^[n] ∘ g) '' Icc a b) < δ := by
    induction n with
    | zero => simpa using hdiam
    | succ n ih =>
      have hrange : MapsTo (f^[n + 1] ∘ g) (Icc a b)
          (Metric.closedBall (f^[n + 1] (g a)) r) := by
        intro t ht
        rw [Metric.mem_closedBall]
        change dist (f^[n + 1] (g t)) (f^[n + 1] (g a)) ≤ r
        rw [iterate_succ_apply', iterate_succ_apply']
        have hdist := Metric.dist_le_diam_of_mem (hbound n)
          (mem_image_of_mem (f^[n] ∘ g) ht) (mem_image_of_mem (f^[n] ∘ g) ha)
        exact (hγcontrol ((hdist.trans_lt ih).trans_le hδγ)).le
      have h := injOn_and_diam_image_of_mapsTo_closedBall G hr hr' hab.le _
        ((hf.iterate (n + 1)).comp_continuousOn hg) hrange (hloc (n + 1))
      rw [h.2]
      exact hclose (n + 1)
  have hsmall : MapsTo g (Icc a b) (Metric.closedBall (g a) r) := by
    intro t ht
    apply Metric.mem_closedBall.mpr
    have hdist := Metric.dist_le_diam_of_mem
      (Metric.isBounded_of_compactSpace : Bornology.IsBounded (g '' Icc a b))
      (mem_image_of_mem g ht) (mem_image_of_mem g ha)
    exact (hdist.trans hdiam.le).trans hδr
  have hgInj : InjOn g (Icc a b) :=
    (injOn_and_diam_image_of_mapsTo_closedBall G hr hr' hab.le _ hg hsmall
      (by simpa using hloc 0)).1
  have hfin : (g '' Icc a b).Finite :=
    IntervalObstruction.finite_of_all_times_small hB (subset_univ _)
      (g a) (mem_image_of_mem g ha) fun y hy n => by
        obtain ⟨t, ht, rfl⟩ := hy
        have hdist := Metric.dist_le_diam_of_mem (hbound n)
          (mem_image_of_mem (f^[n] ∘ g) ha) (mem_image_of_mem (f^[n] ∘ g) ht)
        exact (hdist.trans_lt (hiterdiam n)).trans_le hδε
  exact ((Set.Icc_infinite hab).image hgInj) hfin

/-- For any small immersed path, distinct points on the path have separated
forward orbits at one uniform scale. The same scale works in every small ball. -/
theorem separates_points_of_immersed_paths (hf : Continuous f)
    (hfinite : FinitelyPositiveExpansive f) :
    ∃ δ > 0, ∀ (g : ℝ → Space G) {a b : ℝ} (z : Space G),
      ContinuousOn g (Icc a b) →
      MapsTo g (Icc a b) (Metric.closedBall z (1 / 8)) →
      (∀ n : ℕ, ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn (f^[n] ∘ g) U) →
      ∀ x ∈ g '' Icc a b, ∀ y ∈ g '' Icc a b, x ≠ y →
        ∃ n : ℕ, δ ≤ dist (f^[n] x) (f^[n] y) := by
  obtain ⟨δ, hδ, hsep⟩ := separates_immersed_interval_endpoints G hf hfinite
  refine ⟨δ, hδ, ?_⟩
  intro g a b z hg hmap hloc
  have ordered {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s < t) :
      ∃ n : ℕ, δ ≤ dist (f^[n] (g s)) (f^[n] (g t)) := by
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hsub' : Ioo s t ⊆ Ioo a b := Ioo_subset_Ioo hs.1 ht.2
    have hloc' n c hc := hloc n c (hsub' hc)
    have hd := (injOn_and_diam_image_of_mapsTo_closedBall G
      (by norm_num) (by norm_num) hst.le z (hg.mono hsub)
      (hmap.mono_left hsub) (by simpa using hloc' 0)).2
    by_cases hsmall : dist (g s) (g t) < δ
    · exact hsep g hst (hg.mono hsub) (hd.symm ▸ hsmall) hloc'
    · exact ⟨0, by simpa using le_of_not_gt hsmall⟩
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ hne
  rcases lt_or_gt_of_ne (fun e => hne (congrArg g e)) with hst | hts
  · exact ordered hs ht hst
  · obtain ⟨n, hn⟩ := ordered ht hs hts
    exact ⟨n, by rwa [dist_comm]⟩

end D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
