/- GID: D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-target accessibility through actual full or proper iterate images on the circle. -/

import D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness.Basic

/-!
Actual circle order and finite packing for the proper-image crossing bridge.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness

open IntervalObstruction

namespace Arc

/-- Interior means the actual circle interior, including for arcs that cross
the zero seam. A slightly larger injective quotient chart handles endpoints. -/
theorem interior_eq (A : Arc) :
    interior (A : Set Circle) = project '' Ioo A.segment.left A.segment.right := by
  let a := A.segment.left - (1 - (A.segment.right - A.segment.left)) / 2
  have hchart : (A.segment : Set ℝ) ⊆ Ioo a (a + 1) := by
    intro t ht
    dsimp [a]
    constructor <;> linarith [ht.1, ht.2, A.length_lt_one]
  have hi : InjOn project (Ioo a (a + 1)) := by
    intro u hu v hv he
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (Ioo_subset_Ico_self hu) (Ioo_subset_Ico_self hv)).mp he
  apply subset_antisymm
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := interior_subset hx
    let U := project ⁻¹' interior (A : Set Circle) ∩ Ioo a (a + 1)
    have hU : IsOpen U :=
      (isOpen_interior.preimage continuous_project).inter isOpen_Ioo
    have htU : t ∈ U := ⟨hx, hchart ht⟩
    have hsub : U ⊆ (A.segment : Set ℝ) := by
      intro u hu
      obtain ⟨v, hv, he⟩ := interior_subset hu.1
      have huv : u = v := hi hu.2 (hchart hv) he.symm
      exact huv.symm ▸ hv
    have htint : t ∈ interior (A.segment : Set ℝ) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds htU) hsub)
    have ht' : t ∈ Ioo A.segment.left A.segment.right := by
      change t ∈ interior (Icc A.segment.left A.segment.right) at htint
      simpa only [interior_Icc] using htint
    exact ⟨t, ht', rfl⟩
  · have hopen : IsOpen (project '' Ioo A.segment.left A.segment.right) :=
      (AddCircle.isCoveringMap_coe (1 : ℝ)).isOpenMap _ isOpen_Ioo
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hopen.mem_nhds hx) (image_mono Ioo_subset_Icc_self))

theorem interior_connected (A : Arc) : IsConnected (interior (A : Set Circle)) := by
  rw [A.interior_eq]
  exact (show IsConnected (Ioo A.segment.left A.segment.right) from
    ⟨nonempty_Ioo.mpr A.segment.proper, isPreconnected_Ioo⟩).image
      project continuous_project.continuousOn

theorem closure_interior (A : Arc) : closure (interior (A : Set Circle)) = A := by
  apply subset_antisymm
  · exact closure_minimal interior_subset A.compact.isClosed
  · have h := image_closure_subset_closure_image
      (s := Ioo A.segment.left A.segment.right) continuous_project
    rw [closure_Ioo A.segment.proper.ne, ← A.interior_eq] at h
    exact h

/-- Only the two actual endpoints can fail to be interior points of an arc. -/
theorem mem_interior_of_ne_endpoints (A : Arc) {x : Circle} (hx : x ∈ (A : Set Circle))
    (hl : x ≠ project A.segment.left) (hr : x ≠ project A.segment.right) :
    x ∈ interior (A : Set Circle) := by
  obtain ⟨t, ht, rfl⟩ := hx
  rw [A.interior_eq]
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, rfl⟩
  · intro he; exact hl (congrArg project he.symm)
  · intro he; exact hr (congrArg project he)

/-- An infinite intersection cannot be supported on the four endpoints. -/
theorem interiors_overlap (A B : Arc)
    (h : ((A : Set Circle) ∩ (B : Set Circle)).Infinite) :
    (interior (A : Set Circle) ∩ interior (B : Set Circle)).Nonempty := by
  let E : Set Circle := {project A.segment.left, project A.segment.right,
    project B.segment.left, project B.segment.right}
  have hE : E.Finite := by simp [E]
  obtain ⟨x, hx, he⟩ := (h.sdiff hE).nonempty
  have hne : x ≠ project A.segment.left ∧ x ≠ project A.segment.right ∧
      x ≠ project B.segment.left ∧ x ≠ project B.segment.right := by
    simpa only [E, mem_insert_iff, mem_singleton_iff, not_or] using he
  exact ⟨x, A.mem_interior_of_ne_endpoints hx.1 hne.1 hne.2.1,
    B.mem_interior_of_ne_endpoints hx.2 hne.2.2.1 hne.2.2.2⟩

/-- A macroscopic arc contains a ball of uniform radius in its actual
interior. Centered quotient coordinates prove the metric containment. -/
theorem ball_subset_interior (A : Arc) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ρ ≤ A.segment.right - A.segment.left) :
    Metric.ball (project (A.segment.left + ρ / 2)) (ρ / 4) ⊆
      interior (A : Set Circle) := by
  let m := A.segment.left + ρ / 2
  intro x hx
  let t := coordinate (m - 1 / 2) x
  have ht := coordinate_mem (m - 1 / 2) x
  have hhalf : |t - m| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hd : dist t m < ρ / 4 := by
    rw [← project_dist_eq hhalf, project_coordinate]
    exact hx
  rw [Real.dist_eq, abs_lt] at hd
  rw [A.interior_eq]
  refine ⟨t, ?_, project_coordinate _ x⟩
  dsimp [m] at hd
  constructor <;> linarith [hd.1, hd.2]

end Arc

/-- Every nonempty open circle set contains a genuine compact subarc. -/
theorem arc_in_open {U : Set Circle} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ A : Arc, (A : Set Circle) ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  let c := coordinate 0 x
  have hc : project c = x := project_coordinate 0 x
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((hU.preimage continuous_project).mem_nhds (show project c ∈ U from by rw [hc]; exact hx))
  let h := min (r / 2) (1 / 4)
  have hh : 0 < h := lt_min (by positivity) (by norm_num)
  have hhr : h < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hh4 : h ≤ 1 / 4 := min_le_right _ _
  let A : Arc := ⟨⟨c - h, c + h, by linarith⟩, by dsimp; linarith⟩
  refine ⟨A, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  apply hsub
  change dist t c < r
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- Finite circle packing: infinitely many arcs of one positive minimum
length cannot have disjoint interiors. The finite ball cover is of the
actual compact metric circle; no length measure is postulated. -/
theorem macroscopic_interiors_overlap (A : ℕ → Arc) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hE : {n | ρ ≤ (A n).segment.right - (A n).segment.left}.Infinite) :
    ∃ i j : ℕ, i < j ∧
      (interior (A i : Set Circle) ∩ interior (A j : Set Circle)).Nonempty := by
  classical
  let z : ℕ → Circle := fun n => project ((A n).segment.left + ρ / 2)
  obtain ⟨C, _, hC, hcover⟩ :=
    (isCompact_univ : IsCompact (univ : Set Circle)).finite_cover_balls
      (show 0 < ρ / 16 by positivity)
  have hchoose : ∀ n, ∃ c ∈ C, z n ∈ Metric.ball c (ρ / 16) := by
    intro n
    obtain ⟨c, hc, hz⟩ := mem_iUnion₂.mp (hcover (mem_univ (z n)))
    exact ⟨c, hc, hz⟩
  choose c hc hclose using hchoose
  obtain ⟨i, hi, j, hj, hne, he⟩ :=
    hE.exists_ne_map_eq_of_mapsTo (fun n _ => hc n) hC
  have hnear : dist (z j) (z i) < ρ / 4 := by
    have h₁ : dist (z j) (c j) < ρ / 16 := hclose j
    have h₂ : dist (c j) (z i) < ρ / 16 := by
      simpa only [Metric.mem_ball, ← he, dist_comm] using hclose i
    linarith [dist_triangle (z j) (c j) (z i)]
  have hmeet : (interior (A i : Set Circle) ∩ interior (A j : Set Circle)).Nonempty :=
    ⟨z j, (A i).ball_subset_interior hρ hi hnear,
      (A j).ball_subset_interior hρ hj (by
        change dist (z j) (z j) < ρ / 4
        simpa only [dist_self] using (show 0 < ρ / 4 by positivity))⟩
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i, j, hij, hmeet⟩
  · exact ⟨j, i, hji, by simpa only [inter_comm] using hmeet⟩

/-- The interiors and the closed arcs in any family have the same union
closure. In particular density of a closed return chain transfers to its
open chain; density alone has not been substituted for target accessibility. -/
theorem closure_iUnion_interiors {ι : Type*} (A : ι → Arc) :
    closure (⋃ i, interior (A i : Set Circle)) = closure (⋃ i, (A i : Set Circle)) := by
  apply subset_antisymm
  · apply closure_mono
    exact iUnion_mono (fun _ => interior_subset)
  · apply closure_minimal ?_ isClosed_closure
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hsub : interior (A i : Set Circle) ⊆ ⋃ j, interior (A j : Set Circle) :=
      fun _ hx => mem_iUnion.mpr ⟨i, hx⟩
    exact closure_mono hsub ((A i).closure_interior.symm ▸ hi)

/-- A connected dense circle set cannot miss two distinct points. Cutting
at the first missing point puts the other strictly inside one real chart;
density supplies points on both sides and connectedness fills their interval. -/
theorem two_targets_mem_of_connected_dense {U : Set Circle} (hconn : IsConnected U)
    (hdense : Dense U) (c₁ c₂ : Circle) (hne : c₁ ≠ c₂) : c₁ ∈ U ∨ c₂ ∈ U := by
  classical
  by_cases hc₁ : c₁ ∈ U
  · exact Or.inl hc₁
  by_cases hc₂ : c₂ ∈ U
  · exact Or.inr hc₂
  exfalso
  let a := coordinate 0 c₁
  have ha : project a = c₁ := project_coordinate 0 c₁
  have hcut : project a ∉ U := by simpa only [ha] using hc₁
  let b := coordinate a c₂
  have hb := coordinate_mem a c₂
  have hab : a < b := by
    apply lt_of_le_of_ne hb.1
    intro he
    apply hne
    rw [← ha, ← project_coordinate a c₂]
    exact congrArg project he
  have hba : b < a + 1 := hb.2
  have hleftOpen : IsOpen (project '' Ioo a b) :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).isOpenMap _ isOpen_Ioo
  have hrightOpen : IsOpen (project '' Ioo b (a + 1)) :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).isOpenMap _ isOpen_Ioo
  obtain ⟨x, ⟨u, hu, rfl⟩, hx⟩ := hdense.inter_open_nonempty _ hleftOpen
    ((nonempty_Ioo.mpr hab).image project)
  obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := hdense.inter_open_nonempty _ hrightOpen
    ((nonempty_Ioo.mpr hba).image project)
  let S := coordinate a '' U
  have hS : IsConnected S := hconn.image (coordinate a) (continuousOn_coordinate hcut)
  have huS : u ∈ S := by
    have he : coordinate a (project u) = u :=
      coordinate_project ⟨hu.1.le, hu.2.trans hba⟩
    exact he ▸ mem_image_of_mem (coordinate a) hx
  have hvS : v ∈ S := by
    have he : coordinate a (project v) = v :=
      coordinate_project ⟨(hab.trans hv.1).le, hv.2⟩
    exact he ▸ mem_image_of_mem (coordinate a) hy
  obtain ⟨z, hz, he⟩ := hS.Icc_subset huS hvS (show b ∈ Icc u v from ⟨hu.2.le, hv.1.le⟩)
  apply hc₂
  have hzc : z = c₂ := by
    calc
      z = project (coordinate a z) := (project_coordinate a z).symm
      _ = project b := congrArg project he
      _ = c₂ := project_coordinate a c₂
  exact hzc ▸ hz

/-- An interior point of an actual proper iterate image has a strictly
crossed real representative in an actual lift. The real lift's compact
range is first proved shorter than one turn, then its interior is used. -/
theorem crossing_of_mem_interior {g : Circle → Circle} (hg : Continuous g)
    (A : Arc) (hproper : g '' (A : Set Circle) ≠ univ)
    (hinfinite : (g '' (A : Set Circle)).Infinite) {c : Circle}
    (hc : c ∈ interior (g '' (A : Set Circle))) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ t, project (G t) = g (project t)) ∧
      ∃ v : ℝ, project v = c ∧
        (∃ u ∈ (A.segment : Set ℝ), G u < v) ∧
        (∃ w ∈ (A.segment : Set ℝ), v < G w) := by
  obtain ⟨G, hG, hlift⟩ := exists_real_lift _ (hg.comp continuous_project)
  have heq : project '' (G '' (A.segment : Set ℝ)) = g '' (A : Set Circle) := by
    rw [Set.image_image]
    change (fun t => project (G t)) '' (A.segment : Set ℝ) =
      g '' (project '' (A.segment : Set ℝ))
    rw [Set.image_image]
    congr 1
    exact funext hlift
  have hrealInf : (G '' (A.segment : Set ℝ)).Infinite := by
    intro h
    apply hinfinite
    rw [← heq]
    exact h.image project
  obtain ⟨B, hB⟩ := compact_connected_segment (A.segment.compact.image hG)
    ((show IsConnected (A.segment : Set ℝ) from
      ⟨A.segment.nonempty, isPreconnected_Icc⟩).image G hG.continuousOn) hrealInf
  have hshort : B.right - B.left < 1 := by
    by_contra! hlong
    apply hproper
    apply eq_univ_of_forall
    intro x
    have ht := coordinate_mem B.left x
    rw [← heq, hB]
    exact ⟨coordinate B.left x, ⟨ht.1, by linarith [ht.2]⟩, project_coordinate B.left x⟩
  let D : Arc := ⟨B, hshort⟩
  have hD : (D : Set Circle) = g '' (A : Set Circle) := by
    change project '' (B : Set ℝ) = _
    rw [← hB]
    exact heq
  rw [← hD, D.interior_eq] at hc
  obtain ⟨v, hv, hvc⟩ := hc
  obtain ⟨u, hu, heu⟩ := hB.symm.subset (show B.left ∈ (B : Set ℝ) from ⟨le_rfl, B.proper.le⟩)
  obtain ⟨w, hw, hew⟩ := hB.symm.subset (show B.right ∈ (B : Set ℝ) from ⟨B.proper.le, le_rfl⟩)
  exact ⟨G, hG, hlift, v, hvc,
    ⟨u, hu, by simpa only [heu] using hv.1⟩,
    ⟨w, hw, by simpa only [hew] using hv.2⟩⟩

/-- An actual return overlap forces the closed return chain to be dense.
The chain is connected, its closure is invariant under the return iterate,
and a proper closure would be the forbidden trapping subtype interval. This
proves the closure part of the proper-image bridge without postulating a
classification, recurrence, exactness or mixing property. The open chain
and the actual target crossing are supplied by the following theorems.
-/
theorem return_chain_dense {f : Circle → Circle} (hf : Continuous f)
    (hfin : FinitelyPositiveExpansive f) (A : Arc) {p : ℕ} (hp : 0 < p)
    (hmeet : ((A : Set Circle) ∩ f^[p] '' (A : Set Circle)).Nonempty) :
    closure (⋃ r : ℕ, (f^[p])^[r] '' (A : Set Circle)) = univ := by
  let g := f^[p]
  let S : ℕ → Set Circle := fun r => g^[r] '' (A : Set Circle)
  have hg : Continuous g := hf.iterate p
  have hconn : ∀ r, IsConnected (S r) :=
    fun r => A.connected.image (g^[r]) (hg.iterate r).continuousOn
  have hoverlap : ∀ r, (S r ∩ S (r + 1)).Nonempty := by
    intro r
    obtain ⟨x, hx, y, hy, he⟩ := hmeet
    refine ⟨g^[r] x, ⟨x, hx, rfl⟩, y, hy, ?_⟩
    change g^[r + 1] y = g^[r] x
    rw [Function.iterate_succ_apply]
    exact congrArg (g^[r]) he
  have hUconn : IsConnected (⋃ r, S r) :=
    IsConnected.iUnion_of_chain hconn hoverlap
  have hAU : (A : Set Circle) ⊆ ⋃ r, S r := by
    intro x hx
    exact mem_iUnion.mpr ⟨0, x, hx, rfl⟩
  have hUmap : MapsTo g (⋃ r, S r) (⋃ r, S r) := by
    intro x hx
    obtain ⟨r, y, hy, rfl⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨r + 1, y, hy, ?_⟩
    exact Function.iterate_succ_apply' g r y
  have hKmap := hUmap.closure_of_continuousOn hg.continuousOn
  by_contra hproper
  obtain ⟨K, hK⟩ := arc_of_compact_connected isClosed_closure.isCompact
    hUconn.closure (A.infinite.mono (hAU.trans subset_closure)) hproper
  obtain ⟨ε, hε, N, hN, hB⟩ := id hfin
  apply no_periodic_trapping_arc hf hε hB hN hp K
  rw [← hK]
  exact hKmap

/-- Nondegenerate adjacent overlaps propagate through every return iterate
because its fibres are finite. The resulting actual open chain is connected
and has the same dense closure as the closed return chain. -/
theorem return_open_chain_dense {f : Circle → Circle} (hf : Continuous f)
    (hfin : FinitelyPositiveExpansive f) (A H : Arc) {p : ℕ} (hp : 0 < p)
    (hHA : (H : Set Circle) ⊆ (A : Set Circle))
    (hHR : (H : Set Circle) ⊆ f^[p] '' (A : Set Circle))
    (hproper : ∀ r : ℕ, (f^[p])^[r] '' (A : Set Circle) ≠ univ) :
    ∃ C : ℕ → Arc, (∀ r, (f^[p])^[r] '' (A : Set Circle) = (C r : Set Circle)) ∧
      IsOpen (⋃ r, interior (C r : Set Circle)) ∧
      IsConnected (⋃ r, interior (C r : Set Circle)) ∧
      Dense (⋃ r, interior (C r : Set Circle)) := by
  classical
  obtain ⟨ε, hε, N, _, hB⟩ := id hfin
  let g := f^[p]
  have hg : Continuous g := hf.iterate p
  have hgfib : ∀ z, (univ ∩ g ⁻¹' {z}).Finite :=
    finite_iterate_fibres (mapsTo_univ f univ) (finite_fibres isCompact_univ hB hε) p
  have hclass : ∀ r : ℕ, ∃ C : Arc, g^[r] '' (A : Set Circle) = (C : Set Circle) := by
    intro r
    exact arc_of_compact_connected (A.compact.image (hg.iterate r))
      (A.connected.image (g^[r]) (hg.iterate r).continuousOn)
      (infinite_iterate_image (mapsTo_univ g univ) hgfib (subset_univ _) A.infinite r)
      (hproper r)
  choose C hC using hclass
  have hoverlap : ∀ r, (interior (C r : Set Circle) ∩
      interior (C (r + 1) : Set Circle)).Nonempty := by
    intro r
    apply (C r).interiors_overlap (C (r + 1))
    apply (infinite_iterate_image (mapsTo_univ g univ) hgfib
      (subset_univ _) H.infinite r).mono
    rintro _ ⟨x, hx, rfl⟩
    constructor
    · exact (hC r).subset ⟨x, hHA hx, rfl⟩
    · obtain ⟨y, hy, he⟩ := hHR hx
      apply (hC (r + 1)).subset
      refine ⟨y, hy, ?_⟩
      rw [Function.iterate_succ_apply]
      exact congrArg (g^[r]) he
  have hconn : IsConnected (⋃ r, interior (C r : Set Circle)) :=
    IsConnected.iUnion_of_chain (fun r => (C r).interior_connected) hoverlap
  have hmeet : ((A : Set Circle) ∩ f^[p] '' (A : Set Circle)).Nonempty := by
    obtain ⟨x, hx⟩ := H.infinite.nonempty
    exact ⟨x, hHA hx, hHR hx⟩
  have hclosed : closure (⋃ r, (C r : Set Circle)) = univ := by
    simp_rw [← hC]
    exact return_chain_dense hf hfin A hp hmeet
  have hdense : Dense (⋃ r, interior (C r : Set Circle)) :=
    dense_iff_closure_eq.mpr ((closure_iUnion_interiors C).trans hclosed)
  exact ⟨C, hC, isOpen_iUnion (fun _ => isOpen_interior), hconn, hdense⟩

/-- The proper-image branch of the two-target bridge, under the original
finite all-time bound. Late macroscopic images force an actual interior
overlap, whose nondegenerate return chain reaches one of the two targets. -/
theorem two_target_crossing_of_proper_images {f : Circle → Circle}
    (hf : Continuous f) (hfin : FinitelyPositiveExpansive f) (J : Arc)
    (hproper : ∀ n : ℕ, f^[n] '' (J : Set Circle) ≠ univ)
    (c₁ c₂ : Circle) (hne : c₁ ≠ c₂) :
    ∃ q : ℕ, ∃ G : ℝ → ℝ, Continuous G ∧
      (∀ t, project (G t) = f^[q] (project t)) ∧
      ∃ v : ℝ, (project v = c₁ ∨ project v = c₂) ∧
        (∃ u ∈ (J.segment : Set ℝ), G u < v) ∧
        (∃ w ∈ (J.segment : Set ℝ), v < G w) := by
  classical
  obtain ⟨ε, hε, N, _, hB⟩ := id hfin
  have hfib := finite_fibres isCompact_univ hB hε
  have hclass : ∀ n : ℕ, ∃ A : Arc, f^[n] '' (J : Set Circle) = (A : Set Circle) := by
    intro n
    exact arc_of_compact_connected (J.compact.image (hf.iterate n))
      (J.connected.image (f^[n]) (hf.iterate n).continuousOn)
      (infinite_iterate_image (mapsTo_univ f univ) hfib (subset_univ _) J.infinite n)
      (hproper n)
  choose A hA using hclass
  let ρ := min ε (1 / 8)
  have hρ : 0 < ρ := lt_min hε (by norm_num)
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρ8 : ρ ≤ 1 / 8 := min_le_right _ _
  have hE : {n | ρ ≤ (A n).segment.right - (A n).segment.left}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro m
    obtain ⟨n, hn, x, hx, y, hy, hsep⟩ := arbitrarily_late_separation hB
      (mapsTo_univ f univ) hε hfib (subset_univ _) J.infinite (m + 1)
    refine ⟨n, ?_, by omega⟩
    change ρ ≤ (A n).segment.right - (A n).segment.left
    by_contra! hshort
    obtain ⟨u, hu, heu⟩ := (hA n).subset (mem_image_of_mem (f^[n]) hx)
    obtain ⟨v, hv, hev⟩ := (hA n).subset (mem_image_of_mem (f^[n]) hy)
    have hdist : dist u v ≤ (A n).segment.right - (A n).segment.left := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    have hhalf : |u - v| ≤ 1 / 2 := by
      rw [← Real.dist_eq]
      linarith
    have hsep' : ε ≤ dist u v := by
      rw [← project_dist_eq hhalf, heu, hev]
      exact hsep
    linarith
  obtain ⟨i, j, hij, hmeet⟩ := macroscopic_interiors_overlap A hρ hE
  obtain ⟨H, hH⟩ := arc_in_open (isOpen_interior.inter isOpen_interior) hmeet
  let p := j - i
  have hp : 0 < p := Nat.sub_pos_of_lt hij
  have hreturn : f^[p] '' (A i : Set Circle) = (A j : Set Circle) := by
    rw [← hA i, ← Set.image_comp, ← Function.iterate_add,
      show p + i = j by dsimp [p]; omega, hA j]
  have hHA : (H : Set Circle) ⊆ (A i : Set Circle) :=
    fun x hx => interior_subset (hH hx).1
  have hHR : (H : Set Circle) ⊆ f^[p] '' (A i : Set Circle) := by
    rw [hreturn]
    exact fun x hx => interior_subset (hH hx).2
  have hchain : ∀ r : ℕ,
      (f^[p])^[r] '' (A i : Set Circle) = f^[p * r + i] '' (J : Set Circle) := by
    intro r
    rw [← hA i, ← Function.iterate_mul, ← Set.image_comp, ← Function.iterate_add]
  have hproperChain : ∀ r : ℕ, (f^[p])^[r] '' (A i : Set Circle) ≠ univ := by
    intro r
    rw [hchain]
    exact hproper _
  obtain ⟨C, hC, _, hconn, hdense⟩ :=
    return_open_chain_dense hf hfin (A i) H hp hHA hHR hproperChain
  have htarget := two_targets_mem_of_connected_dense hconn hdense c₁ c₂ hne
  have hcross : ∀ c ∈ ⋃ r, interior (C r : Set Circle),
      ∃ q : ℕ, ∃ G : ℝ → ℝ, Continuous G ∧
        (∀ t, project (G t) = f^[q] (project t)) ∧
        ∃ v : ℝ, project v = c ∧
          (∃ u ∈ (J.segment : Set ℝ), G u < v) ∧
          (∃ w ∈ (J.segment : Set ℝ), v < G w) := by
    intro c hc
    obtain ⟨r, hr⟩ := mem_iUnion.mp hc
    have hcimage : c ∈ interior (f^[p * r + i] '' (J : Set Circle)) := by
      rw [← hchain r, hC r]
      exact hr
    exact ⟨p * r + i, crossing_of_mem_interior (hf.iterate _) J (hproper _)
      (infinite_iterate_image (mapsTo_univ f univ) hfib (subset_univ _) J.infinite _) hcimage⟩
  rcases htarget with hc | hc
  · obtain ⟨q, G, hG, hlift, v, hvc, hlo, hhi⟩ := hcross c₁ hc
    exact ⟨q, G, hG, hlift, v, Or.inl hvc, hlo, hhi⟩
  · obtain ⟨q, G, hG, hlift, v, hvc, hlo, hhi⟩ := hcross c₂ hc
    exact ⟨q, G, hG, hlift, v, Or.inr hvc, hlo, hhi⟩

/-- The actual two-target circle-order bridge. Both full and proper images
are proved cases; no accessibility, local injectivity, covering, orientation,
mixing or expansion hypothesis is supplied to this theorem. -/
theorem two_target_crossing {f : Circle → Circle} (hf : Continuous f)
    (hfin : FinitelyPositiveExpansive f) (J : Arc)
    (c₁ c₂ : Circle) (hne : c₁ ≠ c₂) :
    ∃ q : ℕ, ∃ G : ℝ → ℝ, Continuous G ∧
      (∀ t, project (G t) = f^[q] (project t)) ∧
      ∃ v : ℝ, (project v = c₁ ∨ project v = c₂) ∧
        (∃ u ∈ (J.segment : Set ℝ), G u < v) ∧
        (∃ w ∈ (J.segment : Set ℝ), v < G w) := by
  by_cases hfull : ∃ q : ℕ, f^[q] '' (J : Set Circle) = univ
  · obtain ⟨q, hq⟩ := hfull
    exact ⟨q, two_target_crossing_of_full_image (hf.iterate q) J hq c₁ c₂ hne⟩
  · exact two_target_crossing_of_proper_images hf hfin J
      (fun n hn => hfull ⟨n, hn⟩) c₁ c₂ hne

end D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness
