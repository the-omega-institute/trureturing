import D5.S1.Dynamics.Shadowing.IntervalObstruction
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homotopy.Lifting

/-!
Metric circle arcs, exact pullbacks, lifts, crossings and strict turns.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness

open IntervalObstruction

/-- The actual metric circle of circumference one. -/
abbrev Circle := AddCircle (1 : ℝ)

/-- The quotient map; the normed quotient supplies the geodesic metric. -/
def project (t : ℝ) : Circle := t

/-- The real representative in the specified half-open fundamental interval. -/
def coordinate (a : ℝ) (x : Circle) : ℝ := AddCircle.equivIco (1 : ℝ) a x

theorem continuous_project : Continuous project :=
  AddCircle.continuous_mk' (1 : ℝ)

theorem project_coordinate (a : ℝ) (x : Circle) :
    project (coordinate a x) = x :=
  AddCircle.coe_equivIco (p := (1 : ℝ)) (a := a) (y := x)

theorem coordinate_injective (a : ℝ) : Injective (coordinate a) := by
  intro x y h
  simpa only [project_coordinate] using congrArg project h

theorem coordinate_mem (a : ℝ) (x : Circle) :
    coordinate a x ∈ Ico a (a + 1) :=
  (AddCircle.equivIco (1 : ℝ) a x).property

theorem coordinate_project {a t : ℝ} (ht : t ∈ Ico a (a + 1)) :
    coordinate a (project t) = t :=
  AddCircle.equivIco_coe_of_mem ht

/-- A real cut is a continuous inverse precisely away from its seam. -/
theorem continuousOn_coordinate {a : ℝ} {K : Set Circle}
    (hK : project a ∉ K) : ContinuousOn (coordinate a) K := by
  intro x hx
  have hxa : x ≠ project a := fun he => hK (he ▸ hx)
  exact (continuousAt_subtype_val.comp
    (AddCircle.continuousAt_equivIco (1 : ℝ) a (x := x) hxa)).continuousWithinAt

/-- The quotient distance agrees with real distance for displacements at most
half a turn. This is an equality of the actual two metrics. -/
theorem project_dist_eq {u v : ℝ} (h : |u - v| ≤ 1 / 2) :
    dist (project u) (project v) = dist u v := by
  change dist (u : Circle) (v : Circle) = dist u v
  rw [dist_eq_norm, ← AddCircle.coe_sub, Real.dist_eq]
  exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by simpa using h)

/-- An explicit point at distance half a turn in the quotient metric. -/
theorem antipode_distance (x : Circle) :
    dist (project (coordinate 0 x + 1 / 2)) x = 1 / 2 := by
  have hh : |coordinate 0 x + 1 / 2 - coordinate 0 x| ≤ 1 / 2 := by
    rw [show coordinate 0 x + 1 / 2 - coordinate 0 x = 1 / 2 by ring]
    norm_num
  calc
    _ = dist (project (coordinate 0 x + 1 / 2)) (project (coordinate 0 x)) :=
      congrArg (dist (project (coordinate 0 x + 1 / 2))) (project_coordinate 0 x).symm
    _ = dist (coordinate 0 x + 1 / 2) (coordinate 0 x) := project_dist_eq hh
    _ = 1 / 2 := by rw [Real.dist_eq]; ring_nf; norm_num

/-- A proper compact arc is the actual image of a real segment of length < 1. -/
structure Arc where
  segment : Segment
  length_lt_one : segment.right - segment.left < 1

instance : Coe Arc (Set Circle) :=
  ⟨fun A => project '' (A.segment : Set ℝ)⟩

namespace Arc

theorem project_injOn (A : Arc) : InjOn project (A.segment : Set ℝ) := by
  intro u hu v hv h
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show u ∈ Ico A.segment.left (A.segment.left + 1) from
      ⟨hu.1, by linarith [hu.2, A.length_lt_one]⟩)
    (show v ∈ Ico A.segment.left (A.segment.left + 1) from
      ⟨hv.1, by linarith [hv.2, A.length_lt_one]⟩)).mp
  exact h

theorem infinite (A : Arc) : (A : Set Circle).Infinite :=
  A.segment.infinite.image A.project_injOn

theorem compact (A : Arc) : IsCompact (A : Set Circle) :=
  A.segment.compact.image continuous_project

theorem connected (A : Arc) : IsConnected (A : Set Circle) :=
  (show IsConnected (A.segment : Set ℝ) from
    ⟨A.segment.nonempty, isPreconnected_Icc⟩).image project continuous_project.continuousOn

/-- A selected real subinterval is again an actual proper arc. -/
def subarc (A : Arc) (J : Segment) (hJ : (J : Set ℝ) ⊆ (A.segment : Set ℝ)) : Arc :=
  ⟨J, by
    have hl := hJ (show J.left ∈ (J : Set ℝ) from ⟨le_rfl, J.proper.le⟩)
    have hr := hJ (show J.right ∈ (J : Set ℝ) from ⟨J.proper.le, le_rfl⟩)
    linarith [A.length_lt_one, hl.1, hr.2]⟩

theorem subarc_subset (A : Arc) (J : Segment)
    (hJ : (J : Set ℝ) ⊆ (A.segment : Set ℝ)) :
    (A.subarc J hJ : Set Circle) ⊆ (A : Set Circle) := image_mono hJ

/-- A cut in the complementary gap avoids the whole closed arc, including
both endpoints; the left endpoint of the arc itself is not used as a cut. -/
theorem exists_cut (A : Arc) : ∃ a : ℝ, project a ∉ (A : Set Circle) := by
  let a := (A.segment.right + A.segment.left + 1) / 2
  have hra : A.segment.right < a := by dsimp [a]; linarith [A.length_lt_one]
  have hal : a < A.segment.left + 1 := by dsimp [a]; linarith [A.length_lt_one]
  refine ⟨a, ?_⟩
  rintro ⟨t, ht, he⟩
  have ht' : t ∈ Ico A.segment.left (A.segment.left + 1) :=
    ⟨ht.1, by linarith [ht.2, A.length_lt_one]⟩
  have ha' : a ∈ Ico A.segment.left (A.segment.left + 1) :=
    ⟨by linarith [A.segment.proper], hal⟩
  have : t = a := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht' ha').mp he
  linarith [ht.2]

end Arc

/-- A compact connected infinite proper subset of the actual circle is a
proper arc. Cutting at a genuinely missing point proves this without a
circle classification or dynamical decomposition hypothesis. -/
theorem arc_of_compact_connected {K : Set Circle} (hKc : IsCompact K)
    (hKn : IsConnected K) (hKi : K.Infinite) (hKp : K ≠ univ) :
    ∃ A : Arc, K = (A : Set Circle) := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : Circle, z ∉ K := by
    by_contra! h
    exact hKp (eq_univ_of_forall h)
  let a := coordinate 0 z
  have ha : project a = z := project_coordinate 0 z
  have hcut : project a ∉ K := by simpa only [ha] using hz
  have hc := continuousOn_coordinate hcut
  let S := coordinate a '' K
  have hSc : IsCompact S := hKc.image_of_continuousOn hc
  have hSn : IsConnected S := hKn.image (coordinate a) hc
  have hSi : S.Infinite := hKi.image (coordinate_injective a).injOn
  obtain ⟨B, hB⟩ := compact_connected_segment hSc hSn hSi
  have hS : S ⊆ Ioo a (a + 1) := by
    rintro _ ⟨x, hx, rfl⟩
    have hm := coordinate_mem a x
    refine ⟨lt_of_le_of_ne hm.1 ?_, hm.2⟩
    intro he
    have he' : x = project a := by rw [← project_coordinate a x, ← he]
    exact hcut (he' ▸ hx)
  have hBl : B.left ∈ S := by rw [hB]; exact ⟨le_rfl, B.proper.le⟩
  have hBr : B.right ∈ S := by rw [hB]; exact ⟨B.proper.le, le_rfl⟩
  let A : Arc := ⟨B, by linarith [(hS hBl).1, (hS hBr).2]⟩
  refine ⟨A, ?_⟩
  change K = project '' (B : Set ℝ)
  rw [← hB]
  ext x
  constructor
  · intro hx
    exact ⟨coordinate a x, mem_image_of_mem _ hx, project_coordinate a x⟩
  · rintro ⟨t, ⟨y, hy, rfl⟩, rfl⟩
    simpa only [project_coordinate] using hy

section Transfer

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {f : X → X} {g : Y → Y} {ε : ℝ} {N : ℕ}

/-- Uniformly continuous injective semiconjugacies pull back a uniform finite
Bowen bound. The argument uses encard and every natural-number time. -/
theorem pullback_bound (e : Y → X) (he : UniformContinuous e) (hi : Injective e)
    (hs : Semiconj e g f) (hε : 0 < ε) (hB : ForwardBowenBound f univ ε N) :
    ∃ δ > 0, ForwardBowenBound g univ δ N := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp he ε hε
  refine ⟨δ, hδ, fun y _ => ?_⟩
  rw [← hi.encard_image (univ ∩ ForwardBowen g δ y)]
  apply le_trans (Set.encard_mono ?_) (hB (e y) (mem_univ _))
  rintro _ ⟨z, ⟨_, hz⟩, rfl⟩
  refine ⟨mem_univ _, fun t => ?_⟩
  rw [← hs.iterate_right t y, ← hs.iterate_right t z]
  exact hd (hz t)

end Transfer

section Trapping

variable {f : Circle → Circle} {ε : ℝ} {N : ℕ}

/-- No iterate can trap an injectively parameterized nondegenerate real
interval. The induced subtype interval map is continuous via the compact
embedding homeomorphism, and the actual interval obstruction is applied. -/
theorem no_trapping_interval (hf : Continuous f) (hε : 0 < ε)
    (hB : ForwardBowenBound f univ ε N) (hN : 1 ≤ N)
    {p : ℕ} (hp : 0 < p) (A : Segment)
    (e : Icc A.left A.right → Circle) (he : Continuous e) (hi : Injective e)
    (htrap : MapsTo (f^[p]) (range e) (range e)) : False := by
  classical
  let E : Icc A.left A.right ≃ range e := Equiv.ofInjective e hi
  have hE : Continuous E := he.subtype_mk (fun x => ⟨x, rfl⟩)
  let H : Icc A.left A.right ≃ₜ range e := hE.homeoOfEquivCompactToT2
  let F : range e → range e := fun x => ⟨f^[p] x, htrap x.property⟩
  have hF : Continuous F :=
    ((hf.iterate p).comp continuous_subtype_val).subtype_mk _
  let g : Icc A.left A.right → Icc A.left A.right := fun x => H.symm (F (H x))
  have hg : Continuous g := H.symm.continuous.comp (hF.comp H.continuous)
  have hs : Semiconj e g (f^[p]) := by
    intro x
    have h := congrArg Subtype.val (H.apply_symm_apply (F (H x)))
    exact h
  obtain ⟨δ, hδ, hBp⟩ := forwardBowenBound_iterate isCompact_univ hf.continuousOn
    (mapsTo_univ f univ) hε hB hp
  obtain ⟨γ, hγ, hBg⟩ := pullback_bound e
    (CompactSpace.uniformContinuous_of_continuous he) hi hs hδ hBp
  exact interval_not_finitelyPositiveExpansive A.proper g hg ⟨γ, hγ, N, hN, hBg⟩

/-- Periodic trapping is excluded for the actual projected arc; image
containment, rather than equality, is the hypothesis contradicted here. -/
theorem no_periodic_trapping_arc (hf : Continuous f) (hε : 0 < ε)
    (hB : ForwardBowenBound f univ ε N) (hN : 1 ≤ N)
    {p : ℕ} (hp : 0 < p) (A : Arc) :
    ¬MapsTo (f^[p]) (A : Set Circle) (A : Set Circle) := by
  intro ht
  let e : Icc A.segment.left A.segment.right → Circle := fun x => project x
  have he : Continuous e := continuous_project.comp continuous_subtype_val
  have hi : Injective e := by
    intro x y h
    exact Subtype.ext (A.project_injOn x.property y.property h)
  have hr : range e = (A : Set Circle) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  apply no_trapping_interval hf hε hB hN hp A.segment e he hi
  simpa only [hr] using ht

end Trapping

section Lifts

/-- Lift the composed map on the real line through the actual quotient
covering. No degree, orientation, injectivity, or degree-one lift is assumed. -/
theorem exists_real_lift (g : ℝ → Circle) (hg : Continuous g) :
    ∃ G : ℝ → ℝ, Continuous G ∧ ∀ t, project (G t) = g t := by
  let v := coordinate 0 (g 0)
  obtain ⟨G, hG, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      (⟨g, hg⟩ : C(ℝ, Circle)) (0 : ℝ) v (project_coordinate 0 (g 0))
  exact ⟨G, G.continuous, fun t => congrFun hG.2 t⟩

/-- A continuous circle selfmap, including each of its iterates, therefore
has an actual continuous real lift after precomposition with `project`. -/
theorem exists_iterate_lift (f : Circle → Circle) (hf : Continuous f) (n : ℕ) :
    ∃ G : ℝ → ℝ, Continuous G ∧ ∀ t, project (G t) = f^[n] (project t) :=
  exists_real_lift _ ((hf.iterate n).comp continuous_project)

/-- Exact real pullbacks are projected as selected subarcs. This is a
chart/lift statement, not an assertion that a whole preimage is an arc. -/
theorem exact_pullback_lift (A : Arc) (D : Segment) {g : Circle → Circle}
    {G : ℝ → ℝ} (hG : ContinuousOn G (A.segment : Set ℝ))
    (hlift : ∀ t ∈ (A.segment : Set ℝ), project (G t) = g (project t))
    (hD : (D : Set ℝ) ⊆ G '' (A.segment : Set ℝ)) :
    ∃ B : Arc, (B : Set Circle) ⊆ (A : Set Circle) ∧
      g '' (B : Set Circle) = project '' (D : Set ℝ) := by
  obtain ⟨J, hJ, he⟩ := exact_pullback A.segment D hG hD
  refine ⟨A.subarc J hJ, A.subarc_subset J hJ, ?_⟩
  change g '' (project '' (J : Set ℝ)) = project '' (D : Set ℝ)
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    rw [← hlift t (hJ ht)]
    exact mem_image_of_mem project (he.subset (mem_image_of_mem G ht))
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨t, ht, hGt⟩ := he.symm.subset hv
    exact ⟨project t, ⟨t, ht, rfl⟩, (hlift t (hJ ht)).symm.trans (congrArg project hGt)⟩

/-- When the entire image lies in a proper arc, the cut coordinate supplies
the lift needed for an exact pullback of every compact target subarc. -/
theorem exact_pullback_arc (g : Circle → Circle) (hg : Continuous g)
    (A D : Arc) (hAD : g '' (A : Set Circle) = (D : Set Circle))
    (B : Arc) (hBD : (B : Set Circle) ⊆ (D : Set Circle)) :
    ∃ J : Arc, (J : Set Circle) ⊆ (A : Set Circle) ∧
      g '' (J : Set Circle) = (B : Set Circle) := by
  obtain ⟨a, ha⟩ := D.exists_cut
  let G : ℝ → ℝ := fun t => coordinate a (g (project t))
  have hG : ContinuousOn G (A.segment : Set ℝ) :=
    (continuousOn_coordinate ha).comp (hg.comp continuous_project).continuousOn
      (fun t ht => hAD.subset ⟨project t, ⟨t, ht, rfl⟩, rfl⟩)
  have hcutB : project a ∉ (B : Set Circle) := fun hb => ha (hBD hb)
  have hcB := continuousOn_coordinate hcutB
  have hBi : (coordinate a '' (B : Set Circle)).Infinite :=
    B.infinite.image (coordinate_injective a).injOn
  obtain ⟨E, hE⟩ := compact_connected_segment
    (B.compact.image_of_continuousOn hcB) (B.connected.image (coordinate a) hcB) hBi
  have hES : (E : Set ℝ) ⊆ G '' (A.segment : Set ℝ) := by
    rw [← hE]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, ⟨t, ht, rfl⟩, he⟩ := hAD.symm.subset (hBD hx)
    exact ⟨t, ht, congrArg (coordinate a) he⟩
  obtain ⟨J, hJA, hGJ⟩ := exact_pullback_lift A E hG
    (fun t _ => project_coordinate a _) hES
  refine ⟨J, hJA, hGJ.trans ?_⟩
  rw [← hE]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa only [project_coordinate] using hy
  · intro hx
    exact ⟨coordinate a x, ⟨x, hx, rfl⟩, project_coordinate a x⟩

end Lifts

section FullImageCrossing

/-- The full-circle branch of the two-target bridge. A lift whose projection
covers the circle has width at least one; its open range can omit at most
one of two distinct targets, including the exact one-turn seam case. -/
theorem two_target_crossing_of_full_image {g : Circle → Circle}
    (hg : Continuous g) (A : Arc) (hfull : g '' (A : Set Circle) = univ)
    (c₁ c₂ : Circle) (hne : c₁ ≠ c₂) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ t, project (G t) = g (project t)) ∧
      ∃ v : ℝ, (project v = c₁ ∨ project v = c₂) ∧
        (∃ u ∈ (A.segment : Set ℝ), G u < v) ∧
        (∃ w ∈ (A.segment : Set ℝ), v < G w) := by
  obtain ⟨G, hG, hlift⟩ := exists_real_lift _ (hg.comp continuous_project)
  obtain ⟨u, hu, hmin⟩ := A.segment.compact.exists_isMinOn A.segment.nonempty hG.continuousOn
  obtain ⟨w, hw, hmax⟩ := A.segment.compact.exists_isMaxOn A.segment.nonempty hG.continuousOn
  let m := G u
  let M := G w
  have hlo : ∀ t ∈ (A.segment : Set ℝ), m ≤ G t := fun t ht => isMinOn_iff.mp hmin t ht
  have hhi : ∀ t ∈ (A.segment : Set ℝ), G t ≤ M := fun t ht => isMaxOn_iff.mp hmax t ht
  have hmM : m ≤ M := hlo w hw
  have hwidth : 1 ≤ M - m := by
    by_contra! hshort
    let a := (M + m + 1) / 2
    have hMa : M < a := by dsimp [a]; linarith
    have ham : a < m + 1 := by dsimp [a]; linarith
    have haI : a ∈ Ico m (m + 1) := ⟨by dsimp [a]; linarith, ham⟩
    obtain ⟨_, ⟨t, ht, rfl⟩, he⟩ := hfull.symm.subset (mem_univ (project a))
    have htI : G t ∈ Ico m (m + 1) := ⟨hlo t ht, by linarith [hhi t ht]⟩
    have heq : G t = a := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI haI).mp
      ((hlift t).trans he)
    linarith [hhi t ht]
  let v₁ := coordinate m c₁
  let v₂ := coordinate m c₂
  have hv₁ : v₁ ∈ Ico m (m + 1) := coordinate_mem m c₁
  have hv₂ : v₂ ∈ Ico m (m + 1) := coordinate_mem m c₂
  have hp₁ : project v₁ = c₁ := project_coordinate m c₁
  have hp₂ : project v₂ = c₂ := project_coordinate m c₂
  refine ⟨G, hG, hlift, ?_⟩
  by_cases h₁ : m < v₁
  · exact ⟨v₁, Or.inl hp₁, ⟨u, hu, h₁⟩, ⟨w, hw, by linarith [hv₁.2]⟩⟩
  · have he₁ : v₁ = m := le_antisymm (le_of_not_gt h₁) hv₁.1
    have h₂ : m < v₂ := by
      apply lt_of_le_of_ne hv₂.1
      intro he₂
      apply hne
      rw [← hp₁, ← hp₂, he₁, ← he₂]
    exact ⟨v₂, Or.inr hp₂, ⟨u, hu, h₂⟩, ⟨w, hw, by linarith [hv₂.2]⟩⟩

end FullImageCrossing

section SmallCrossing

/-- A finite level set forces an isolated sign-changing zero between
oppositely signed endpoints. Finite-set induction discards isolated touches;
it does not assume that every level preimage is a crossing. -/
private theorem crossing_of_finite_level (G : ℝ → ℝ) (hG : Continuous G) (v : ℝ)
    (S : Set ℝ) (hS : S.Finite) :
    ∀ u w : ℝ, u < w → G u < v → v < G w →
      (∀ z ∈ Icc u w, G z = v → z ∈ S) →
      ∃ c ∈ Ioo u w, ∃ δ > 0,
        (∀ z ∈ Ioo (c - δ) c, G z < v) ∧
        (∀ z ∈ Ioo c (c + δ), v < G z) := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro u w huw hu hw hroot
    obtain ⟨z, hz, he⟩ := intermediate_value_Icc huw.le hG.continuousOn ⟨hu.le, hw.le⟩
    exact (hroot z hz he).elim
  | @insert c S hcS hS ih =>
    intro u w huw hu hw hroot
    by_cases hc : c ∈ Ioo u w ∧ G c = v
    · obtain ⟨γ, hγ, havoid⟩ := Metric.mem_nhds_iff.mp (hS.isClosed.compl_mem_nhds hcS)
      obtain ⟨h, hh, hsmall⟩ := exists_between
        (lt_min hγ (lt_min (sub_pos.mpr hc.1.1) (sub_pos.mpr hc.1.2)))
      have hhγ : h < γ := hsmall.trans_le (min_le_left _ _)
      have hhu : h < c - u := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hhw : h < w - c := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have hlocal : ∀ z ∈ Icc (c - h) (c + h), z ≠ c → G z ≠ v := by
        intro z hz hzc he
        have hzu : z ∈ Icc u w := by constructor <;> linarith [hz.1, hz.2]
        have hzγ : dist z c < γ := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hz.1, hz.2]
        have hzS : z ∉ S := havoid hzγ
        rcases mem_insert_iff.mp (hroot z hzu he) with heq | hm
        · exact hzc heq
        · exact hzS hm
      have hleftne : G (c - h) ≠ v := hlocal _ ⟨le_rfl, by linarith⟩ (by linarith)
      have hrightne : G (c + h) ≠ v := hlocal _ ⟨by linarith, le_rfl⟩ (by linarith)
      by_cases hl : G (c - h) < v
      · by_cases hr : v < G (c + h)
        · refine ⟨c, hc.1, h, hh, ?_, ?_⟩
          · intro z hz
            by_contra! hbad
            obtain ⟨t, ht, he⟩ := intermediate_value_Icc hz.1.le hG.continuousOn ⟨hl.le, hbad⟩
            exact hlocal t ⟨ht.1, by linarith [ht.2, hz.2]⟩
              (by linarith [ht.2, hz.2]) he
          · intro z hz
            by_contra! hbad
            obtain ⟨t, ht, he⟩ := intermediate_value_Icc hz.2.le hG.continuousOn ⟨hbad, hr.le⟩
            exact hlocal t ⟨by linarith [ht.1, hz.1], ht.2⟩
              (by linarith [ht.1, hz.1]) he
        · have hright : G (c + h) < v := lt_of_le_of_ne (le_of_not_gt hr) hrightne
          obtain ⟨d, hd, δ, hδ, hsign⟩ := ih (c + h) w (by linarith) hright hw (by
            intro z hz he
            have hz' : z ∈ Icc u w := ⟨by linarith [hz.1], hz.2⟩
            exact (mem_insert_iff.mp (hroot z hz' he)).resolve_left (by linarith [hz.1]))
          exact ⟨d, ⟨by linarith [hd.1], hd.2⟩, δ, hδ, hsign⟩
      · have hleft : v < G (c - h) := lt_of_le_of_ne (le_of_not_gt hl) hleftne.symm
        obtain ⟨d, hd, δ, hδ, hsign⟩ := ih u (c - h) (by linarith) hu hleft (by
          intro z hz he
          have hz' : z ∈ Icc u w := ⟨hz.1, by linarith [hz.2]⟩
          exact (mem_insert_iff.mp (hroot z hz' he)).resolve_left (by linarith [hz.2]))
        exact ⟨d, ⟨hd.1, by linarith [hd.2]⟩, δ, hδ, hsign⟩
    · apply ih u w huw hu hw
      intro z hz he
      rcases mem_insert_iff.mp (hroot z hz he) with hzc | hzS
      · subst z
        apply (hc ⟨?_, he⟩).elim
        constructor
        · exact lt_of_le_of_ne hz.1 (fun heq => by rw [← heq] at he; linarith)
        · exact lt_of_le_of_ne hz.2 (fun heq => by rw [heq] at he; linarith)
      · exact hzS

/-- Interior lifted target values can be crossed on arbitrarily short
real subintervals, with either orientation. Fibres are required finite on
the actual source segment only. -/
theorem small_crossing (A : Segment) {G : ℝ → ℝ} (hG : Continuous G)
    {v : ℝ} (hfib : ((A : Set ℝ) ∩ G ⁻¹' {v}).Finite)
    (hbelow : ∃ u ∈ (A : Set ℝ), G u < v)
    (habove : ∃ w ∈ (A : Set ℝ), v < G w) :
    ∃ c ∈ Ioo A.left A.right, ∀ η > 0, ∃ B : Segment,
      (B : Set ℝ) ⊆ Ioo A.left A.right ∧ B.right - B.left < η ∧
      ∃ α > 0, Icc (v - α) (v + α) ⊆ G '' (B : Set ℝ) := by
  obtain ⟨u, hu, hlu⟩ := hbelow
  obtain ⟨w, hw, hlw⟩ := habove
  have hne : u ≠ w := by intro h; subst w; linarith
  have hcross : ∃ c ∈ Ioo A.left A.right, ∃ δ > 0,
      ((∀ z ∈ Ioo (c - δ) c, G z < v) ∧ (∀ z ∈ Ioo c (c + δ), v < G z)) ∨
      ((∀ z ∈ Ioo (c - δ) c, v < G z) ∧ (∀ z ∈ Ioo c (c + δ), G z < v)) := by
    rcases lt_or_gt_of_ne hne with huw | hwu
    · obtain ⟨c, hc, δ, hδ, hs⟩ := crossing_of_finite_level G hG v _ hfib u w huw hlu hlw
        (fun z hz he => ⟨Icc_subset_Icc hu.1 hw.2 hz, he⟩)
      exact ⟨c, ⟨hu.1.trans_lt hc.1, hc.2.trans_le hw.2⟩, δ, hδ, Or.inl hs⟩
    · have hnfib : ((A : Set ℝ) ∩ (fun z => -G z) ⁻¹' {-v}).Finite := by
        apply hfib.subset
        intro z hz
        exact ⟨hz.1, by change G z = v; have he : -G z = -v := hz.2; linarith⟩
      obtain ⟨c, hc, δ, hδ, hl, hr⟩ := crossing_of_finite_level
        (fun z => -G z) hG.neg (-v) _ hnfib w u hwu (neg_lt_neg hlw) (neg_lt_neg hlu)
        (fun z hz he => ⟨Icc_subset_Icc hw.1 hu.2 hz, he⟩)
      refine ⟨c, ⟨hw.1.trans_lt hc.1, hc.2.trans_le hu.2⟩, δ, hδ, Or.inr ⟨?_, ?_⟩⟩
      · intro z hz; exact neg_lt_neg_iff.mp (hl z hz)
      · intro z hz; exact neg_lt_neg_iff.mp (hr z hz)
  obtain ⟨c, hc, δ, hδ, hs⟩ := hcross
  refine ⟨c, hc, fun η hη => ?_⟩
  obtain ⟨h, hh, hsmall⟩ := exists_between
    (lt_min hδ (lt_min (by positivity : 0 < η / 2)
      (lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2))))
  have hhδ : h < δ := hsmall.trans_le (min_le_left _ _)
  have hhη : h < η / 2 := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhl : h < c - A.left := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhr : h < A.right - c := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let B : Segment := ⟨c - h, c + h, by linarith⟩
  refine ⟨B, ?_, by dsimp [B]; linarith, ?_⟩
  · intro z hz
    constructor <;> linarith [hz.1, hz.2]
  have hminus : c - h ∈ Ioo (c - δ) c := by constructor <;> linarith
  have hplus : c + h ∈ Ioo c (c + δ) := by constructor <;> linarith
  rcases hs with hs | hs
  · obtain ⟨α, hα, hαsmall⟩ := exists_between
      (lt_min (sub_pos.mpr (hs.1 _ hminus)) (sub_pos.mpr (hs.2 _ hplus)))
    refine ⟨α, hα, ?_⟩
    apply subset_trans (b := Icc (G (c - h)) (G (c + h)))
    · apply Icc_subset_Icc <;> linarith [min_le_left (v - G (c - h)) (G (c + h) - v),
        min_le_right (v - G (c - h)) (G (c + h) - v)]
    · exact intermediate_value_Icc B.proper.le hG.continuousOn
  · obtain ⟨α, hα, hαsmall⟩ := exists_between
      (lt_min (sub_pos.mpr (hs.2 _ hplus)) (sub_pos.mpr (hs.1 _ hminus)))
    refine ⟨α, hα, ?_⟩
    apply subset_trans (b := Icc (G (c + h)) (G (c - h)))
    · apply Icc_subset_Icc <;> linarith [min_le_left (v - G (c + h)) (G (c - h) - v),
        min_le_right (v - G (c + h)) (G (c - h) - v)]
    · exact intermediate_value_Icc' B.proper.le hG.continuousOn

end SmallCrossing

section CircleCrossing

/-- The real small-crossing result is realized on an actual circle subarc,
with every intermediate time up to and including the transit plus one.
The hypotheses specify actual below/above values of a continuous lift; they
are exactly the crossing supplied by the two-target bridge in CircleOrder,
and are not hypotheses of the original circle target. -/
theorem small_circle_crossing {f : Circle → Circle} (hf : Continuous f)
    {ε η : ℝ} {N q : ℕ} (hε : 0 < ε) (hη : 0 < η)
    (hB : ForwardBowenBound f univ ε N) (A : Arc)
    {G : ℝ → ℝ} (hG : Continuous G)
    (hlift : ∀ t, project (G t) = f^[q] (project t)) {v : ℝ}
    (hbelow : ∃ u ∈ (A.segment : Set ℝ), G u < v)
    (habove : ∃ w ∈ (A.segment : Set ℝ), v < G w) :
    ∃ B : Arc, (B : Set Circle) ⊆ (A : Set Circle) ∧
      project v ∈ interior (f^[q] '' (B : Set Circle)) ∧
      ∀ s ≤ q + 1, ∀ x ∈ (B : Set Circle), ∀ y ∈ (B : Set Circle),
        dist (f^[s] x) (f^[s] y) < η := by
  have hfib := finite_iterate_fibres (mapsTo_univ f univ)
    (finite_fibres isCompact_univ hB hε) q (project v)
  have hfinite : ((A.segment : Set ℝ) ∩ G ⁻¹' {v}).Finite := by
    apply Set.Finite.of_finite_image (f := project) (s := (A.segment : Set ℝ) ∩ G ⁻¹' {v})
    · apply hfib.subset
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨mem_univ _, (hlift t).symm.trans (congrArg project ht.2)⟩
    · exact A.project_injOn.mono inter_subset_left
  obtain ⟨δ, hδ, hd⟩ := finite_block_scale isCompact_univ hf.continuousOn
    (mapsTo_univ f univ) hη (q + 2)
  obtain ⟨c, _, hc⟩ := small_crossing A.segment hG hfinite hbelow habove
  obtain ⟨J, hJA, hlen, α, hα, hcover⟩ := hc (min δ (1 / 4)) (lt_min hδ (by norm_num))
  have hJA' : (J : Set ℝ) ⊆ (A.segment : Set ℝ) := hJA.trans Ioo_subset_Icc_self
  let B := A.subarc J hJA'
  have hprojectOpen : IsOpen (project '' Ioo (v - α) (v + α)) :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).isOpenMap _ isOpen_Ioo
  have hmem : project v ∈ project '' Ioo (v - α) (v + α) :=
    ⟨v, by constructor <;> linarith, rfl⟩
  have hsub : project '' Ioo (v - α) (v + α) ⊆ f^[q] '' (B : Set Circle) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨u, hu, hGu⟩ := hcover (Ioo_subset_Icc_self ht)
    exact ⟨project u, ⟨u, hu, rfl⟩, (hlift u).symm.trans (congrArg project hGu)⟩
  refine ⟨B, A.subarc_subset J hJA',
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hprojectOpen.mem_nhds hmem) hsub), ?_⟩
  intro s hs x hx y hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  change u ∈ (J : Set ℝ) at hu
  change w ∈ (J : Set ℝ) at hw
  have hdist : dist u w < min δ (1 / 4) := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2, hw.1, hw.2]
  have hhalf : |u - w| ≤ 1 / 2 := by
    rw [← Real.dist_eq]
    exact (hdist.trans_le (min_le_right _ _)).le.trans (by norm_num)
  apply hd s (by omega) _ (mem_univ _) _ (mem_univ _)
  rw [project_dist_eq hhalf]
  exact hdist.trans_le (min_le_left _ _)

end CircleCrossing

section Turns

/-- A strict extremum of an actual real lift, with a two-sided neighborhood. -/
def LiftedTurn (G : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ δ > 0, (∀ y, dist y c < δ → y ≠ c → G y < G c) ∨
    (∀ y, dist y c < δ → y ≠ c → G c < G y)

/-- Failure of actual local injectivity produces a genuine lifted strict
turn. The subsequent two-turn theorem excludes a unique circle turn.
The lift is confined to a short target chart before equal values are compared. -/
theorem exists_lifted_turn_of_not_locallyInjective {f : Circle → Circle}
    (hf : Continuous f) (hfin : FinitelyPositiveExpansive f)
    (hloc : ¬IsLocallyInjective f) :
    ∃ A : Arc, ∃ G : ℝ → ℝ, Continuous G ∧
      (∀ t, project (G t) = f (project t)) ∧
      ∃ c ∈ Ioo A.segment.left A.segment.right, ∃ δ > 0,
        (∀ y, dist y c < δ → y ≠ c → G y < G c) ∨
        (∀ y, dist y c < δ → y ≠ c → G c < G y) := by
  classical
  obtain ⟨ε, hε, N, _, hB⟩ := hfin
  have hfib := finite_fibres isCompact_univ hB hε
  unfold IsLocallyInjective at hloc
  push_neg at hloc
  obtain ⟨x, hx⟩ := hloc
  let a := coordinate 0 x
  have ha : project a = x := project_coordinate 0 x
  obtain ⟨G, hG, hlift'⟩ := exists_iterate_lift f hf 1
  have hlift : ∀ t, project (G t) = f (project t) := by simpa using hlift'
  obtain ⟨γ, hγ, hg⟩ := Metric.continuousAt_iff.mp (hG.continuousAt : ContinuousAt G a)
    (1 / 8) (by norm_num)
  let h := min (γ / 2) (1 / 8)
  have hh : 0 < h := lt_min (by positivity) (by norm_num)
  have hhγ : h < γ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hhsmall : h ≤ 1 / 8 := min_le_right _ _
  let A : Arc := ⟨⟨a - h, a + h, by linarith⟩, by dsimp; linarith⟩
  let U := project '' Ioo (a - h) (a + h)
  have hU : IsOpen U := (AddCircle.isCoveringMap_coe (1 : ℝ)).isOpenMap _ isOpen_Ioo
  have hxU : x ∈ U := ⟨a, by constructor <;> linarith, ha⟩
  have hni : ¬InjOn f U := hx U hU hxU
  have hchart : ∀ t ∈ (A.segment : Set ℝ),
      G t ∈ Ico (G a - 1 / 4) (G a - 1 / 4 + 1) := by
    intro t ht
    have htγ : dist t a < γ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hval := hg htγ
    rw [Real.dist_eq, abs_lt] at hval
    constructor <;> linarith [hval.1, hval.2]
  have hGni : ¬InjOn G (A.segment : Set ℝ) := by
    intro hi
    apply hni
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ he
    have huA : u ∈ (A.segment : Set ℝ) := Ioo_subset_Icc_self hu
    have hvA : v ∈ (A.segment : Set ℝ) := Ioo_subset_Icc_self hv
    have hproj : project (G u) = project (G v) := (hlift u).trans (he.trans (hlift v).symm)
    have heG : G u = G v :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (hchart u huA) (hchart v hvA)).mp hproj
    exact congrArg project (hi huA hvA heG)
  have hGfib : ∀ z, ((A.segment : Set ℝ) ∩ G ⁻¹' {z}).Finite := by
    intro z
    apply Set.Finite.of_finite_image (f := project)
    · apply (hfib (project z)).subset
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨mem_univ _, (hlift t).symm.trans (congrArg project ht.2)⟩
    · exact A.project_injOn.mono inter_subset_left
  obtain ⟨c, hc, δ, hδ, hturn⟩ := strict_turn A.segment hG.continuousOn hGfib hGni
  exact ⟨A, G, hG, hlift, c, hc, δ, hδ, hturn⟩

/-- There are two distinct actual circle turns if local injectivity fails.
If the complementary open interval had a noninjective lifted restriction,
the finite-fibre strict-turn theorem would already supply the second turn.
Otherwise that whole restriction is monotone. Its two ends are incompatible
with the translated strict extremum; covering uniqueness proves the required
translation identity, without a degree-one or orientation assumption. -/
theorem two_distinct_lifted_turns {f : Circle → Circle} (hf : Continuous f)
    (hfin : FinitelyPositiveExpansive f) (hloc : ¬IsLocallyInjective f) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ t, project (G t) = f (project t)) ∧
      ∃ c d : ℝ, project c ≠ project d ∧ LiftedTurn G c ∧ LiftedTurn G d := by
  classical
  obtain ⟨A, G, hG, hlift, c, _, δ, hδ, hturn⟩ :=
    exists_lifted_turn_of_not_locallyInjective hf hfin hloc
  have hcTurn : LiftedTurn G c := ⟨δ, hδ, hturn⟩
  suffices hex : ∃ d, project c ≠ project d ∧ LiftedTurn G d by
    obtain ⟨d, hcd, hd⟩ := hex
    exact ⟨G, hG, hlift, c, d, hcd, hcTurn, hd⟩
  by_contra! hno
  obtain ⟨ε, hε, N, _, hB⟩ := hfin
  have hfib := finite_fibres isCompact_univ hB hε
  have nodup : ∀ u ∈ Ioo c (c + 1), ∀ v ∈ Ioo c (c + 1),
      u < v → G u = G v → False := by
    intro u hu v hv huv he
    let B : Arc := ⟨⟨u, v, huv⟩, by linarith [hu.1, hv.2]⟩
    have hGfib : ∀ z, ((B.segment : Set ℝ) ∩ G ⁻¹' {z}).Finite := by
      intro z
      apply Set.Finite.of_finite_image (f := project)
      · apply (hfib (project z)).subset
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨mem_univ _, (hlift t).symm.trans (congrArg project ht.2)⟩
      · exact B.project_injOn.mono inter_subset_left
    have hni : ¬InjOn G (B.segment : Set ℝ) := by
      intro hi
      exact huv.ne (hi ⟨le_rfl, huv.le⟩ ⟨huv.le, le_rfl⟩ he)
    obtain ⟨d, hd, γ, hγ, hdTurn⟩ := strict_turn B.segment hG.continuousOn hGfib hni
    change d ∈ Ioo u v at hd
    have hdI : d ∈ Ico c (c + 1) := ⟨hu.1.le.trans hd.1.le, hd.2.trans hv.2⟩
    have hcI : c ∈ Ico c (c + 1) := ⟨le_rfl, by linarith⟩
    have hcd : project c ≠ project d := by
      intro h
      have heq : c = d := (AddCircle.coe_eq_coe_iff_of_mem_Ico hcI hdI).mp h
      exact (hu.1.trans hd.1).ne heq
    exact hno d hcd ⟨γ, hγ, hdTurn⟩
  have hi : InjOn G (Ioo c (c + 1)) := by
    intro u hu v hv he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact nodup u hu v hv h he
    · exact nodup v hv u hu h he.symm
  have hcl : closure (Ioo c (c + 1)) = Icc c (c + 1) :=
    closure_Ioo (by linarith)
  have hm : MonotoneOn G (Icc c (c + 1)) ∨ AntitoneOn G (Icc c (c + 1)) := by
    rcases ContinuousOn.strictMonoOn_of_injOn_Ioo (by linarith : c < c + 1)
      hG.continuousOn hi with hm | ha
    · have hh := monotoneOn_closure hG.continuousOn hm.monotoneOn
      rw [hcl] at hh
      exact Or.inl hh
    · have hn : MonotoneOn (fun t => -G t) (Ioo c (c + 1)) :=
        fun u hu v hv huv => neg_le_neg (ha.antitoneOn hu hv huv)
      have hh := monotoneOn_closure hG.neg.continuousOn hn
      rw [hcl] at hh
      exact Or.inr (fun u hu v hv huv => neg_le_neg_iff.mp (hh hu hv huv))
  let D : ℝ → ℝ := fun t => G (t + 1) - G t
  have hD : Continuous D := (hG.comp (continuous_id.add continuous_const)).sub hG
  have hDproj : ∀ t, project (D t) = 0 := by
    intro t
    change project (G (t + 1)) - project (G t) = 0
    have hp : project (t + 1) = project t := AddCircle.coe_add_period (1 : ℝ) t
    rw [hlift, hlift, hp, sub_self]
  have hshift : ∀ t, G (t + 1) - G t = G (c + 1) - G c := by
    intro t
    exact (AddCircle.isCoveringMap_coe (1 : ℝ)).const_of_comp hD
      (fun u v => (hDproj u).trans (hDproj v).symm) t c
  let h := min (δ / 2) (1 / 4)
  have hh : 0 < h := lt_min (by positivity) (by norm_num)
  have hhδ : h < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hh1 : h < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hl : dist (c - h) c < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have hr : dist (c + h) c < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have htrans := hshift (c - h)
  have h0 : c ∈ Icc c (c + 1) := ⟨le_rfl, by linarith⟩
  have h1 : c + 1 ∈ Icc c (c + 1) := ⟨by linarith, le_rfl⟩
  have hp : c + h ∈ Icc c (c + 1) := ⟨by linarith, by linarith⟩
  have hq : c - h + 1 ∈ Icc c (c + 1) := ⟨by linarith, by linarith⟩
  rcases hturn with hpeak | htrough
  · have hleft := hpeak (c - h) hl (by linarith)
    have hright := hpeak (c + h) hr (by linarith)
    rcases hm with hm | ha
    · linarith [hm h0 hp (by linarith)]
    · linarith [ha hq h1 (by linarith)]
  · have hleft := htrough (c - h) hl (by linarith)
    have hright := htrough (c + h) hr (by linarith)
    rcases hm with hm | ha
    · linarith [hm hq h1 (by linarith)]
    · linarith [ha h0 hp (by linarith)]

end Turns

section ShortArcs

private def anchor (x : Circle) : ℝ := coordinate 0 x

private def endpoint (x y : Circle) : ℝ := coordinate (anchor x - 1 / 2) y

/-- The actual shorter arc from x to y, using the centered half-open chart.
At antipodes the chart makes a fixed choice; subsequent uses have distance
strictly less than 1/8 and therefore never encounter that ambiguity. -/
def shortArc (x y : Circle) : Set Circle :=
  project '' uIcc (anchor x) (endpoint x y)

private theorem anchor_project (x : Circle) : project (anchor x) = x :=
  project_coordinate 0 x

private theorem endpoint_project (x y : Circle) : project (endpoint x y) = y :=
  project_coordinate _ y

private theorem short_parameters {x y : Circle} {t : ℝ}
    (ht : t ∈ uIcc (anchor x) (endpoint x y)) :
    t ∈ Ico (anchor x - 1 / 2) (anchor x - 1 / 2 + 1) := by
  have hb := coordinate_mem (anchor x - 1 / 2) y
  change anchor x - 1 / 2 ≤ endpoint x y ∧
    endpoint x y < anchor x - 1 / 2 + 1 at hb
  rcases mem_uIcc.mp ht with ht | ht
  · constructor <;> linarith [ht.1, ht.2, hb.1, hb.2]
  · constructor <;> linarith [ht.1, ht.2, hb.1, hb.2]

private theorem short_project_inj (x y : Circle) :
    InjOn project (uIcc (anchor x) (endpoint x y)) := by
  intro u hu v hv he
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (short_parameters hu)
    (short_parameters hv)).mp he

private theorem short_parameter_distance (x y : Circle) :
    dist (anchor x) (endpoint x y) = dist x y := by
  have hb := short_parameters (x := x) (y := y) right_mem_uIcc
  have hd : |anchor x - endpoint x y| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
  simpa only [anchor_project, endpoint_project] using (project_dist_eq hd).symm

theorem shortArc_left (x y : Circle) : x ∈ shortArc x y :=
  ⟨anchor x, left_mem_uIcc, anchor_project x⟩

/-- Every point on the shorter arc is no farther from its first endpoint
than its length, measured in the actual quotient metric. -/
theorem shortArc_dist_le {x y z : Circle} (hz : z ∈ shortArc x y) :
    dist z x ≤ dist x y := by
  obtain ⟨t, ht, rfl⟩ := hz
  have hp := short_parameters ht
  have hhalf : |t - anchor x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2]
  have heq : dist (project t) x = dist t (anchor x) := by
    calc
      _ = dist (project t) (project (anchor x)) :=
        congrArg (dist (project t)) (anchor_project x).symm
      _ = dist t (anchor x) := project_dist_eq hhalf
  rw [heq, ← short_parameter_distance x y]
  rw [Real.dist_eq, Real.dist_eq]
  rcases mem_uIcc.mp ht with ht | ht
  · rw [abs_of_nonneg (by linarith : 0 ≤ t - anchor x),
      abs_of_nonpos (by linarith : anchor x - endpoint x y ≤ 0)]
    linarith [ht.2]
  · rw [abs_of_nonpos (by linarith : t - anchor x ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ anchor x - endpoint x y)]
    linarith [ht.1]

theorem shortArc_infinite {x y : Circle} (hne : x ≠ y) :
    (shortArc x y).Infinite := by
  have hab : anchor x ≠ endpoint x y := by
    intro he
    exact hne ((anchor_project x).symm.trans ((congrArg project he).trans (endpoint_project x y)))
  have hinf : (uIcc (anchor x) (endpoint x y)).Infinite := by
    rcases lt_or_gt_of_ne hab with h | h
    · rw [uIcc_of_le h.le]
      exact Icc_infinite h
    · rw [uIcc_of_ge h.le]
      exact Icc_infinite h
  exact hinf.image (short_project_inj x y)

/-- On an injective short arc whose image stays in a ball of radius 1/8,
the image is exactly the short arc between the endpoint images. -/
theorem image_shortArc (f : Circle → Circle) (hf : Continuous f) (x y : Circle)
    (hi : InjOn f (shortArc x y))
    (hsmall : ∀ z ∈ shortArc x y, dist (f z) (f x) < 1 / 8) :
    f '' shortArc x y = shortArc (f x) (f y) := by
  let a := anchor (f x)
  let cut := a - 1 / 2
  have hseam : dist (project cut) (f x) = 1 / 2 := by
    have heq : a - 1 / 2 - a = -(1 / 2 : ℝ) := by ring
    calc
      _ = dist (project (a - 1 / 2)) (project a) :=
        congrArg (dist (project cut)) (anchor_project (f x)).symm
      _ = dist (a - 1 / 2) a := project_dist_eq (by rw [heq]; norm_num)
      _ = 1 / 2 := by rw [Real.dist_eq, heq]; norm_num
  have hcut : project cut ∉ f '' shortArc x y := by
    rintro ⟨z, hz, he⟩
    have h := hsmall z hz
    rw [he, hseam] at h
    norm_num at h
  let G : ℝ → ℝ := fun t => coordinate cut (f (project t))
  have hG : ContinuousOn G (uIcc (anchor x) (endpoint x y)) :=
    (continuousOn_coordinate hcut).comp
      (hf.comp continuous_project).continuousOn
      (fun t ht => ⟨project t, ⟨t, ht, rfl⟩, rfl⟩)
  have hGi : InjOn G (uIcc (anchor x) (endpoint x y)) := by
    intro u hu v hv h
    have h' : f (project u) = f (project v) := by
      simpa only [G, project_coordinate] using congrArg project h
    exact short_project_inj x y hu hv (hi ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ h')
  have himage : G '' uIcc (anchor x) (endpoint x y) =
      uIcc (G (anchor x)) (G (endpoint x y)) := by
    rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (min_le_max) hG hGi with hm | ha
    · exact hG.image_uIcc_of_monotoneOn hm.monotoneOn
    · exact hG.image_uIcc_of_antitoneOn ha.antitoneOn
  have hGa : G (anchor x) = anchor (f x) := by
    change coordinate (a - 1 / 2) (f (project (anchor x))) = a
    rw [anchor_project]
    calc
      _ = coordinate (a - 1 / 2) (project a) :=
        congrArg (coordinate (a - 1 / 2)) (anchor_project (f x)).symm
      _ = a := coordinate_project ⟨by linarith, by linarith⟩
  have hGb : G (endpoint x y) = endpoint (f x) (f y) := by
    change coordinate (anchor (f x) - 1 / 2) (f (project (endpoint x y))) = _
    rw [endpoint_project]
    rfl
  calc
    f '' shortArc x y = project '' (G '' uIcc (anchor x) (endpoint x y)) := by
      rw [shortArc, Set.image_image, Set.image_image]
      congr 1
      funext t
      exact (project_coordinate cut (f (project t))).symm
    _ = shortArc (f x) (f y) := by rw [himage, hGa, hGb]; rfl

end ShortArcs

end D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness
