/- GID: D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphValenceBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphValenceBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forward Bowen bounds from separated arms at finite graph vertices. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphBowenArcs
import D5.S1.Dynamics.Shadowing.FiniteGraphNoFreeArcFold
import D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivisionRealization

/-! Small forward Bowen balls and incidence at vertices of affine graphs. -/

open D5.S1.Dynamics.Shadowing
open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {f : Space G → Space G}

private noncomputable def realEdge {u v : V} (h : G.Adj u v) (t : ℝ) : Space G :=
  edgeChart G h (projIcc 0 1 zero_le_one t)

omit [Fintype V] in
private theorem continuous_realEdge {u v : V} (h : G.Adj u v) :
    Continuous (realEdge G h) :=
  (continuous_edgeChart G h).comp continuous_projIcc

omit [Fintype V] in
private theorem realEdge_of_mem {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1) :
    realEdge G h t = edgeChart G h t := by
  rw [realEdge, projIcc_of_mem zero_le_one t.property]

/-- Every iterate is locally injective at each interior point of every edge. -/
private def IteratesLocallyInjectiveOnOpenEdges (f : Space G → Space G) : Prop :=
  ∀ n : ℕ, ∀ {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1),
    (t : ℝ) ∈ Ioo 0 1 →
      ∃ U ∈ 𝓝 (edgeChart G h t), InjOn (f^[n]) U

omit [Fintype V] in
private theorem realEdge_locally_injective (hreg : IteratesLocallyInjectiveOnOpenEdges G f)
    (n : ℕ) {u v : V} (h : G.Adj u v) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ∃ U ∈ 𝓝 t, InjOn (f^[n] ∘ realEdge G h) U := by
  let t' : Icc (0 : ℝ) 1 := ⟨t, Ioo_subset_Icc_self ht⟩
  obtain ⟨W, hW, hWInj⟩ := hreg n h t' ht
  rw [← realEdge_of_mem G h t'] at hW
  have hpre : (realEdge G h) ⁻¹' W ∈ 𝓝 t :=
    (continuous_realEdge G h).continuousAt.preimage_mem_nhds hW
  refine ⟨Ioo 0 1 ∩ (realEdge G h) ⁻¹' W, inter_mem (isOpen_Ioo.mem_nhds ht) hpre, ?_⟩
  intro a ha b hb he
  have hsame := hWInj ha.2 hb.2 he
  let a' : Icc (0 : ℝ) 1 := ⟨a, Ioo_subset_Icc_self ha.1⟩
  let b' : Icc (0 : ℝ) 1 := ⟨b, Ioo_subset_Icc_self hb.1⟩
  change realEdge G h a' = realEdge G h b' at hsame
  rw [realEdge_of_mem, realEdge_of_mem] at hsame
  simpa only [coord_edgeChart, edgeVector_right h.ne] using
    congrArg (fun x => coord G x v) hsame

private theorem two_arms_at_vertex [Nontrivial V]
    (hconn : G.Connected) (hf : Continuous f)
    (hhit : StronglyTransitive G f)
    (hreg : IteratesLocallyInjectiveOnOpenEdges G f) (z : V) :
    ∃ (u v : V) (hu : G.Adj z u) (hv : G.Adj z v)
      (s t : Icc (0 : ℝ) 1) (p : ℝ → Space G) (a b : ℝ),
      u ≠ v ∧ 0 < (s : ℝ) ∧ 0 < (t : ℝ) ∧ ContinuousOn p (Icc a b) ∧
      MapsTo p (Icc a b) (Metric.closedBall (vertex G z) (1 / 8)) ∧
      (∀ n : ℕ, ∀ c ∈ Ioo a b, ∃ W ∈ 𝓝 c, InjOn (f^[n] ∘ p) W) ∧
      edgeSegment G hu ⟨0, le_rfl, zero_le_one⟩ s ⊆ p '' Icc a b ∧
      edgeSegment G hv ⟨0, le_rfl, zero_le_one⟩ t ⊆ p '' Icc a b := by
  classical
  obtain ⟨w, hw⟩ := hconn.preconnected.exists_adj_of_nontrivial z
  let U : Set (Space G) := {x | 0 < coord G x z ∧ 0 < coord G x w}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_coord G z)).inter
    (isOpen_lt continuous_const (continuous_coord G w))
  have hU' : U.Nonempty := by
    let mid : Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
    exact ⟨edgeChart G hw mid, by
      change 0 < coord G (edgeChart G hw mid) z ∧ 0 < coord G (edgeChart G hw mid) w
      rw [coord_edgeChart, edgeVector_left hw.ne, coord_edgeChart, edgeVector_right hw.ne]
      norm_num [mid]⟩
  obtain ⟨k, x, hx, hhitx⟩ := hhit U hU hU' (vertex G z)
  obtain ⟨h, q, rfl⟩ := exists_edgeChart_of_two_pos G hw.ne hx.1 hx.2
  have hq : (q : ℝ) ∈ Ioo 0 1 := by
    change 0 < coord G (edgeChart G h q) z ∧ 0 < coord G (edgeChart G h q) w at hx
    rw [coord_edgeChart, edgeVector_left h.ne, coord_edgeChart, edgeVector_right h.ne] at hx
    exact ⟨hx.2, by linarith [hx.1]⟩
  let p := f^[k] ∘ realEdge G h
  have hp : Continuous p := (hf.iterate k).comp (continuous_realEdge G h)
  have hpq : p q = vertex G z := by simpa only [p, comp_apply, realEdge_of_mem] using hhitx
  obtain ⟨W, hW, hWInj⟩ := realEdge_locally_injective G hreg k h hq
  have hsmall : p ⁻¹' Metric.ball (vertex G z) (1 / 8) ∈ 𝓝 (q : ℝ) :=
    hp.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by simpa [hpq]))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hW hsmall) (isOpen_Ioo.mem_nhds hq))
  let a := (q : ℝ) - r / 2
  let b := (q : ℝ) + r / 2
  have hq' : (q : ℝ) ∈ Ioo a b := ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
  have hsub : Icc a b ⊆ (W ∩ p ⁻¹' Metric.ball (vertex G z) (1 / 8)) ∩ Ioo 0 1 := by
    have hball' := (Metric.closedBall_subset_ball (x := (q : ℝ))
      (show r / 2 < r by linarith)).trans hball
    rwa [Real.closedBall_eq_Icc] at hball'
  have hmap : MapsTo p (Icc a b) (Metric.closedBall (vertex G z) (1 / 8)) :=
    fun y hy => Metric.ball_subset_closedBall (hsub hy).1.2
  have hinj : InjOn p (Icc a b) := hWInj.mono fun y hy => (hsub hy).1.1
  have hstar : MapsTo p (Icc a b) (closedStar G z (1 / 8)) := by
    rw [closedStar_eq_closedBall G (by norm_num) (by norm_num)]
    exact hmap
  obtain ⟨u, v, hu, hv, s, t, huv, hs, ht, hA, hB⟩ :=
    two_incident_segments_of_star_path G (by norm_num) (by norm_num) hq'
      hp.continuousOn hstar hinj hpq
  refine ⟨u, v, hu, hv, s, t, p, a, b, huv, hs, ht, hp.continuousOn, hmap, ?_, hA, hB⟩
  intro n c hc
  have hci := (hsub (Ioo_subset_Icc_self hc)).2
  simpa only [p, ← comp_assoc, ← iterate_add] using
    realEdge_locally_injective G hreg (n + k) h hci

/-- A uniform bound one below the maximum valence follows from pointwise
reachability and the absence of folds in the interior of an edge. -/
private theorem forwardBowenBound_of_iteratesLocallyInjective [Nontrivial V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hf : Continuous f) (hfinite : FinitelyPositiveExpansive f)
    (hhit : StronglyTransitive G f)
    (hreg : IteratesLocallyInjectiveOnOpenEdges G f) {D : ℕ} (hD : 2 ≤ D)
    (hdeg : ∀ z, G.degree z ≤ D) :
    ∃ ε > 0, ForwardBowenBound f univ ε (D - 1) := by
  classical
  obtain ⟨δ, hδ, hsep⟩ := separates_points_of_immersed_paths G hf hfinite
  have edge_sep {u v : V} (h : G.Adj u v) (s t : Icc (0 : ℝ) 1)
      (hsmall : dist (edgeChart G h s) (edgeChart G h t) ≤ 1 / 8)
      (hne : edgeChart G h s ≠ edgeChart G h t) :
      ∃ n, δ ≤ dist (f^[n] (edgeChart G h s)) (f^[n] (edgeChart G h t)) := by
    wlog hst : s ≤ t generalizing s t
    · obtain ⟨n, hn⟩ := this t s (by rwa [dist_comm]) hne.symm (le_of_not_ge hst)
      exact ⟨n, by rwa [dist_comm]⟩
    have hinterval : Icc (s : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc s.2.1 t.2.2
    have hmap : MapsTo (realEdge G h) (Icc (s : ℝ) t)
        (Metric.closedBall (edgeChart G h s) (1 / 8)) := by
      intro q hq
      let q' : Icc (0 : ℝ) 1 := ⟨q, hinterval hq⟩
      change realEdge G h q' ∈ _
      rw [realEdge_of_mem, Metric.mem_closedBall, dist_edgeChart, abs_of_nonneg (sub_nonneg.mpr hq.1)]
      rw [dist_edgeChart, abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ t from hst))] at hsmall
      change q - (s : ℝ) ≤ 1 / 8
      linarith [hq.2]
    refine hsep (realEdge G h) (edgeChart G h s) (continuous_realEdge G h).continuousOn
      hmap (fun n q hq => realEdge_locally_injective G hreg n h
        ⟨s.2.1.trans_lt hq.1, hq.2.trans_le t.2.2⟩) _ ?_ _ ?_ hne
    · exact ⟨s, left_mem_Icc.mpr hst, realEdge_of_mem G h s⟩
    · exact ⟨t, right_mem_Icc.mpr hst, realEdge_of_mem G h t⟩
  have local_bound (z : V) : ∃ ρ > 0, ∀ r, 0 ≤ r → r ≤ ρ → ∀ x ε,
      2 * ε ≤ δ → (ForwardBowen f ε x ∩ closedStar G z r).encard ≤ ((D - 1 : ℕ) : ℕ∞) := by
    obtain ⟨u, v, hu, hv, s, t, p, a, b, huv, hs, ht, hp, hmap, hloc, hA, hB⟩ :=
      two_arms_at_vertex G hconn hf hhit hreg z
    refine ⟨min (1 / 8) (min (s : ℝ) (t : ℝ)), by positivity, ?_⟩
    intro r hr hrρ x ε hεδ
    have hrs : r ≤ (s : ℝ) := hrρ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hrt : r ≤ (t : ℝ) := hrρ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hr8 : r ≤ 1 / 8 := hrρ.trans (min_le_left _ _)
    let B := ForwardBowen f ε x ∩ closedStar G z r
    have eq_of_close {y w : Space G} (hy : y ∈ B) (hw : w ∈ B)
        (hseparate : y ≠ w → ∃ n, δ ≤ dist (f^[n] y) (f^[n] w)) : y = w := by
      by_contra hne
      obtain ⟨n, hn⟩ := hseparate hne
      have hy' := hy.1 n
      have hw' := hw.1 n
      linarith [dist_triangle (f^[n] y) (f^[n] x) (f^[n] w),
        dist_comm (f^[n] y) (f^[n] x)]
    let P (y : Space G) (w : V) :=
      ∃ (h : G.Adj z w) (q : Icc (0 : ℝ) 1), (q : ℝ) ≤ r ∧ y = edgeChart G h q
    have hlabeled (y : B) : ∃ w, P y w := by
      rcases (mem_closedStar_iff G hr (by linarith)).mp y.property.2 with h | h
      · exact ⟨u, hu, ⟨0, le_rfl, zero_le_one⟩, hr, h.trans (edgeChart_zero G hu).symm⟩
      · exact h
    choose arm harm using hlabeled
    let label (y : B) : V := if arm y = u then v else arm y
    have hlabel (y : B) : label y ∈ (G.neighborFinset z).erase u := by
      obtain ⟨h, _, _, _⟩ := harm y
      by_cases hy : arm y = u
      · simpa [label, hy, huv.symm, G.mem_neighborFinset] using hv
      · simpa [label, hy, G.mem_neighborFinset] using h
    have same_arm (y w : B) (h : arm y = arm w) : y.val = w.val := by
      obtain ⟨hy, q, hq, hyq⟩ := harm y
      have h' : P (w : Space G) (arm y) := h.symm ▸ harm w
      obtain ⟨_, q', hq', hwq'⟩ := h'
      refine eq_of_close y.2 w.2 ?_
      rw [hyq, hwq']
      exact edge_sep hy q q' (by
        rw [dist_edgeChart, abs_le]
        constructor <;> linarith [q.2.1, q'.2.1])
    have on_path (y : B) (hy : arm y = u ∨ arm y = v) : (y : Space G) ∈ p '' Icc a b := by
      rcases hy with hy | hy
      · obtain ⟨_, q, hq, hyq⟩ : P (y : Space G) u := hy ▸ harm y
        exact hA ⟨q, by
          rw [uIcc_of_le (show (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1) ≤ s from s.2.1)]
          exact ⟨q.2.1, hq.trans hrs⟩, hyq.symm⟩
      · obtain ⟨_, q, hq, hyq⟩ : P (y : Space G) v := hy ▸ harm y
        exact hB ⟨q, by
          rw [uIcc_of_le (show (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1) ≤ t from t.2.1)]
          exact ⟨q.2.1, hq.trans hrt⟩, hyq.symm⟩
    have hinj : Injective label := by
      intro y w hw
      apply Subtype.ext
      by_cases hy' : arm y = u <;> by_cases hw' : arm w = u
      · exact same_arm y w (hy'.trans hw'.symm)
      · simp only [label, ite_eq_left hy', ite_eq_right hw'] at hw
        exact eq_of_close y.2 w.2 (hsep p _ hp hmap hloc _ (on_path y (.inl hy'))
          _ (on_path w (.inr hw.symm)))
      · simp only [label, ite_eq_right hy', ite_eq_left hw'] at hw
        exact eq_of_close y.2 w.2 (hsep p _ hp hmap hloc _ (on_path y (.inr hw))
          _ (on_path w (.inl hw')))
      · exact same_arm y w (by simpa only [label, ite_eq_right hy', ite_eq_right hw'] using hw)
    let chooseLabel (y : Space G) : V := if hy : y ∈ B then label ⟨y, hy⟩ else v
    have hcount : B.encard ≤ ((↑((G.neighborFinset z).erase u) : Set V)).encard := by
      apply Set.encard_le_encard_of_injOn (f := chooseLabel)
      · intro y hy
        change chooseLabel y ∈ (G.neighborFinset z).erase u
        simpa only [chooseLabel, dif_pos hy] using hlabel ⟨y, hy⟩
      · intro y hy w hw he
        exact congrArg Subtype.val (hinj (by simpa [chooseLabel, hy, hw] using he))
    rw [Set.encard_coe_eq_coe_finsetCard,
      Finset.card_erase_of_mem ((G.mem_neighborFinset z u).mpr hu),
      SimpleGraph.card_neighborFinset_eq_degree] at hcount
    exact hcount.trans (by exact_mod_cast Nat.sub_le_sub_right (hdeg z) 1)
  choose ρ hρ hlocal using local_bound
  obtain ⟨z₀, _, hmin⟩ := Set.exists_min_image (univ : Set V) ρ (finite_univ) univ_nonempty
  let ε := min (1 / 16) (min (δ / 2) (ρ z₀ / 2))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (half_pos (hρ z₀)))
  have hε₈ : 2 * ε ≤ 1 / 8 := by linarith [min_le_left (1 / 16 : ℝ) (min (δ / 2) (ρ z₀ / 2))]
  have hεδ : 2 * ε ≤ δ := by
    have h := (min_le_right (1 / 16 : ℝ) _).trans (min_le_left (δ / 2) (ρ z₀ / 2))
    change ε ≤ δ / 2 at h
    linarith
  refine ⟨ε, hε, fun x _ => ?_⟩
  rw [univ_inter]
  have hx (y : Space G) (hy : y ∈ ForwardBowen f ε x) : y ∈ Metric.closedBall x ε := by
    rw [Metric.mem_closedBall, dist_comm]
    exact (by simpa using hy 0 : dist x y < ε).le
  rcases closedBall_subset_edge_or_closedStar G hε (by linarith) x with
    ⟨u, v, h, s, t, hball⟩ | ⟨z, _, hstar⟩
  · apply le_trans (Set.encard_le_one_iff.mpr ?_) (by exact_mod_cast (show 1 ≤ D - 1 by omega))
    intro y w hy hw
    by_contra hne
    have hy' := Metric.mem_closedBall.mp (hx y hy)
    have hw' := Metric.mem_closedBall.mp (hx w hw)
    have hd : dist y w ≤ 1 / 8 := by linarith [dist_triangle y x w, dist_comm x w]
    obtain ⟨q, _, rfl⟩ := hball (hx y hy)
    obtain ⟨q', _, rfl⟩ := hball (hx w hw)
    obtain ⟨n, hn⟩ := edge_sep h q q' hd hne
    have hy'' := hy n
    have hw'' := hw n
    linarith [dist_triangle (f^[n] (edgeChart G h q)) (f^[n] x) (f^[n] (edgeChart G h q')),
      dist_comm (f^[n] (edgeChart G h q)) (f^[n] x)]
  · have hr : 2 * ε ≤ ρ z := by
      have h := (min_le_right (1 / 16 : ℝ) _).trans (min_le_right (δ / 2) (ρ z₀ / 2))
      change ε ≤ ρ z₀ / 2 at h
      linarith [hmin z (mem_univ z)]
    have hsub : ForwardBowen f ε x ⊆ ForwardBowen f ε x ∩ closedStar G z (2 * ε) :=
      fun y hy => ⟨hy, hstar (hx y hy)⟩
    exact (Set.encard_le_encard hsub).trans (hlocal z _ (by positivity) hr x ε hεδ)

/-- On a nontrivial connected finite graph of maximum valence at most `D`, a
strongly transitive finitely positively expansive map has Bowen order at most `D - 1`. -/
theorem forwardBowenBound_of_stronglyTransitive [Nontrivial V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hf : Continuous f) (hfinite : FinitelyPositiveExpansive f)
    (htrans : StronglyTransitive G f) {D : ℕ} (hD : 2 ≤ D) (hdeg : ∀ z, G.degree z ≤ D) :
    ∃ ε > 0, ForwardBowenBound f univ ε (D - 1) := by
  apply forwardBowenBound_of_iteratesLocallyInjective G hconn hf hfinite htrans _ hD hdeg
  intro n u v h t ht
  cases n with
  | zero => exact ⟨univ, univ_mem, by simpa using (injective_id.injOn : InjOn id univ)⟩
  | succ n =>
    obtain ⟨U, hU, htU, hUinj⟩ :=
      isLocallyInjective_iterate_at_openEdge G hf htrans hfinite (Nat.succ_pos n) h t ht
    exact ⟨U, hU.mem_nhds htU, hUinj⟩

/--
info: 'D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization.forwardBowenBound_of_stronglyTransitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms forwardBowenBound_of_stronglyTransitive

end D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

namespace D5.S3.Combinatorics.Graph.LeaflessDynamics.FiniteMultigraphExactDynamics

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (DirectedMultigraph)
open D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision
  (Flag endpoint step graph connected neighbor_ncard_le_of_incident_flags_le)
open TripleEdgeSubdivisionRealization (realization subdivisionHomeomorph)

/-- A metric conjugacy with compact target preserves each finite Bowen bound at a suitable scale. -/
theorem forwardBowenBound_conjugate {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] [CompactSpace Y] (e : X ≃ₜ Y) {f : X → X}
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hbound : ForwardBowenBound f univ ε N) :
    ∃ δ > 0, ForwardBowenBound (e ∘ f ∘ e.symm) univ δ N := by
  let g := e ∘ f ∘ e.symm
  have hconj : Semiconj e.symm g f := by intro y; simp [g]
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous e.symm.continuous) ε hε
  refine ⟨δ, hδ, fun y _ => ?_⟩
  have hmap : MapsTo e.symm (univ ∩ ForwardBowen g δ y)
      (univ ∩ ForwardBowen f ε (e.symm y)) := by
    intro z hz
    refine ⟨mem_univ _, fun k => ?_⟩
    rw [← hconj.iterate_right k y, ← hconj.iterate_right k z]
    exact hsmall (hz.2 k)
  exact (Set.encard_le_encard_of_injOn hmap e.symm.injective.injOn).trans
    (hbound _ (mem_univ _))

/-- The valence bound holds on any metric realization of a connected finite
multigraph, with a loop contributing two flags at its vertex. -/
theorem forwardBowenBound_of_stronglyTransitive_multigraph {V E X : Type*}
    [Fintype V] [Fintype E] [Nonempty E] [DecidableEq V] [DecidableEq E]
    [TopologicalSpace V] [DiscreteTopology V] [TopologicalSpace E] [DiscreteTopology E]
    [MetricSpace X] (M : DirectedMultigraph V E) (e : X ≃ₜ realization M)
    (hconn : ∀ u v, Relation.ReflTransGen (step M) u v) {f : X → X} (hf : Continuous f)
    (hfinite : FinitelyPositiveExpansive f)
    (htrans : ∀ U : Set X, IsOpen U → U.Nonempty → ∀ x, ∃ k, x ∈ f^[k] '' U)
    {D : ℕ} (hD : 2 ≤ D) (hdeg : ∀ v, ({a : Flag E | endpoint M a = v} : Set _).ncard ≤ D) :
    ∃ ε > 0, ForwardBowenBound f univ ε (D - 1) := by
  classical
  obtain ⟨a⟩ : Nonempty E := inferInstance
  let : Nonempty V := ⟨M.source a⟩
  let : Nontrivial (V ⊕ Flag E) := ⟨⟨Sum.inr (Sum.inl a), Sum.inr (Sum.inr a), by simp⟩⟩
  let equiv := e.trans (subdivisionHomeomorph M)
  let : CompactSpace X := equiv.symm.compactSpace
  let g := equiv ∘ f ∘ equiv.symm
  have hconj : Semiconj equiv f g := by intro x; simp [g]
  have hg : Continuous g := equiv.continuous.comp (hf.comp equiv.symm.continuous)
  obtain ⟨ε, hε, N, hN, hbound⟩ := hfinite
  obtain ⟨δ, hδ, hδbound⟩ := forwardBowenBound_conjugate equiv hε hbound
  have hgtrans : FiniteGraphAffineRealization.StronglyTransitive (graph M) g := by
    intro U hU hUne y
    have hpre : (equiv ⁻¹' U).Nonempty := by
      obtain ⟨z, hz⟩ := hUne
      exact ⟨equiv.symm z, by simpa using hz⟩
    obtain ⟨k, x, hx, hk⟩ := htrans _ (hU.preimage equiv.continuous) hpre (equiv.symm y)
    refine ⟨k, equiv x, hx, ?_⟩
    rw [← hconj.iterate_right k x, hk, equiv.apply_symm_apply]
  have hgdeg (w : V ⊕ Flag E) : (graph M).degree w ≤ D := by
    rw [← SimpleGraph.ncard_neighborSet]
    exact neighbor_ncard_le_of_incident_flags_le M hD hdeg w
  obtain ⟨η, hη, hηbound⟩ := FiniteGraphAffineRealization.forwardBowenBound_of_stronglyTransitive
    (graph M) (connected M hconn) hg ⟨δ, hδ, N, hN, hδbound⟩ hgtrans hD hgdeg
  have hrefl : equiv.symm ∘ g ∘ equiv.symm.symm = f := by
    funext x
    simp [g]
  exact hrefl ▸ forwardBowenBound_conjugate equiv.symm hη hηbound

end D5.S3.Combinatorics.Graph.LeaflessDynamics.FiniteMultigraphExactDynamics
