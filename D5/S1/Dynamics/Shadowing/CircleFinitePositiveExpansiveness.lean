import D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness.CircleOrder
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.SeparatedMap

/-!
Actual circle arcs, exact selected pullbacks and coalescing histories.
The original target is

  ∀ f : AddCircle (1 : ℝ) → AddCircle (1 : ℝ),
    Continuous f → FinitelyPositiveExpansive f → PositivelyExpansive f.

The final declaration below has this original type. The two-target bridge
handles both full and proper images and feeds the actual fold induction.
Every time through T+q+1 is controlled and terminal equality supplies every
later natural time.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness

open IntervalObstruction

/-- Disjoint nondegenerate actual circle arcs with a common exact terminal
image. The prefix estimate includes both time zero and the terminal time. -/
structure Histories (f : Circle → Circle) (η : ℝ) (ι : Type*) where
  domain : ι → Arc
  disjoint : ∀ i j, i ≠ j → Disjoint (domain i : Set Circle) (domain j : Set Circle)
  time : ℕ
  terminal : Arc
  onto : ∀ i, f^[time] '' (domain i : Set Circle) = (terminal : Set Circle)
  small : ∀ s ≤ time, ∀ i j, ∀ x ∈ (domain i : Set Circle),
    ∀ y ∈ (domain j : Set Circle), dist (f^[s] x) (f^[s] y) < η

namespace Histories

variable {f : Circle → Circle} {η : ℝ} {ι : Type*}

/-- A genuinely small actual arc starts the coalescing construction at time
zero. Its diameter bound is checked in the quotient metric. -/
def initial (f : Circle → Circle) {η : ℝ} (hη : 0 < η) : Histories f η Unit := by
  let h := min (η / 4) (1 / 8)
  have hh : 0 < h := lt_min (by positivity) (by norm_num)
  have hhη : h < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hh8 : h ≤ 1 / 8 := min_le_right _ _
  let A : Arc := ⟨⟨0, h, hh⟩, by dsimp; linarith⟩
  refine
    { domain := fun _ => A
      disjoint := ?_
      time := 0
      terminal := A
      onto := by intro i; simp
      small := ?_ }
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · intro s hs i j x hx y hy
    have hs0 : s = 0 := by omega
    subst s
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have hdist : dist u v ≤ h := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    have hhalf : |u - v| ≤ 1 / 2 := by
      rw [← Real.dist_eq]
      linarith
    simpa only [Function.iterate_zero_apply, project_dist_eq hhalf] using hdist.trans_lt hhη

/-- Exact pullbacks through the old terminal map double an actual circle
family. The additional time is the full transit-plus-fold time supplied by r. -/
def double (H : Histories f η ι) (hf : Continuous f) {r : ℕ}
    (L R D : Arc) (hL : (L : Set Circle) ⊆ (H.terminal : Set Circle))
    (hR : (R : Set Circle) ⊆ (H.terminal : Set Circle))
    (hdis : Disjoint (L : Set Circle) (R : Set Circle))
    (hGL : f^[r] '' (L : Set Circle) = (D : Set Circle))
    (hGR : f^[r] '' (R : Set Circle) = (D : Set Circle))
    (hpost : ∀ s ≤ r, ∀ x ∈ (L : Set Circle) ∪ (R : Set Circle),
      ∀ y ∈ (L : Set Circle) ∪ (R : Set Circle), dist (f^[s] x) (f^[s] y) < η) :
    Histories f η (ι × Bool) := by
  classical
  let B : Bool → Arc := fun b => if b then R else L
  have hB : ∀ b, (B b : Set Circle) ⊆ (H.terminal : Set Circle) := by
    intro b
    cases b
    · exact hL
    · exact hR
  have hBG : ∀ b, f^[r] '' (B b : Set Circle) = (D : Set Circle) := by
    intro b
    cases b
    · exact hGL
    · exact hGR
  have hBU : ∀ b, (B b : Set Circle) ⊆ (L : Set Circle) ∪ (R : Set Circle) := by
    intro b
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hBD : ∀ b c, b ≠ c → Disjoint (B b : Set Circle) (B c : Set Circle) := by
    intro b c h
    cases b <;> cases c
    · exact (h rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (h rfl).elim
  have hpull : ∀ i b, ∃ J : Arc, (J : Set Circle) ⊆ (H.domain i : Set Circle) ∧
      f^[H.time] '' (J : Set Circle) = (B b : Set Circle) := by
    intro i b
    exact exact_pullback_arc (f^[H.time]) (hf.iterate H.time)
      (H.domain i) H.terminal (H.onto i) (B b) (hB b)
  choose J hJ hGJ using hpull
  refine
    { domain := fun p => J p.1 p.2
      disjoint := ?_
      time := H.time + r
      terminal := D
      onto := ?_
      small := ?_ }
  · intro p q hpq
    apply Set.disjoint_left.mpr
    intro x hxp hxq
    by_cases hi : p.1 = q.1
    · have hb : p.2 ≠ q.2 := fun he => hpq (Prod.ext hi he)
      exact Set.disjoint_left.mp (hBD p.2 q.2 hb)
        ((hGJ p.1 p.2).subset (mem_image_of_mem _ hxp))
        ((hGJ q.1 q.2).subset (mem_image_of_mem _ hxq))
    · exact Set.disjoint_left.mp (H.disjoint p.1 q.1 hi) (hJ _ _ hxp) (hJ _ _ hxq)
  · intro p
    rw [Nat.add_comm H.time r, Function.iterate_add, Set.image_comp, hGJ, hBG]
  · intro s hs p q x hx y hy
    by_cases hsT : s ≤ H.time
    · exact H.small s hsT p.1 q.1 x (hJ _ _ hx) y (hJ _ _ hy)
    · have hTs : H.time ≤ s := by omega
      have hsr : s - H.time ≤ r := by omega
      have hsplit : s = (s - H.time) + H.time := (Nat.sub_add_cancel hTs).symm
      rw [hsplit, Function.iterate_add_apply, Function.iterate_add_apply]
      exact hpost _ hsr _ (hBU p.2 ((hGJ _ _).subset (mem_image_of_mem _ hx)))
        _ (hBU q.2 ((hGJ _ _).subset (mem_image_of_mem _ hy)))

/-- The transit ends in a proper short target arc containing both genuine
fold branches. Pull back those branches exactly, then apply the last f.
Every time through T+q+1 is controlled; the +1 is part of the construction. -/
theorem extend_transit_fold (H : Histories f η ι) (hf : Continuous f)
    (B E L R D : Arc) (q : ℕ)
    (hBA : (B : Set Circle) ⊆ (H.terminal : Set Circle))
    (htransit : f^[q] '' (B : Set Circle) = (E : Set Circle))
    (hLE : (L : Set Circle) ⊆ (E : Set Circle))
    (hRE : (R : Set Circle) ⊆ (E : Set Circle))
    (hdis : Disjoint (L : Set Circle) (R : Set Circle))
    (hFL : f '' (L : Set Circle) = (D : Set Circle))
    (hFR : f '' (R : Set Circle) = (D : Set Circle))
    (hsmall : ∀ s ≤ q + 1, ∀ x ∈ (B : Set Circle),
      ∀ y ∈ (B : Set Circle), dist (f^[s] x) (f^[s] y) < η) :
    ∃ H' : Histories f η (ι × Bool), H'.time = H.time + q + 1 := by
  obtain ⟨L', hLB, hL'⟩ := exact_pullback_arc (f^[q]) (hf.iterate q) B E htransit L hLE
  obtain ⟨R', hRB, hR'⟩ := exact_pullback_arc (f^[q]) (hf.iterate q) B E htransit R hRE
  have hdis' : Disjoint (L' : Set Circle) (R' : Set Circle) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hdis
      (hL'.subset (mem_image_of_mem _ hx)) (hR'.subset (mem_image_of_mem _ hy))
  have hlast : ∀ (J I : Arc), f^[q] '' (J : Set Circle) = (I : Set Circle) →
      f '' (I : Set Circle) = (D : Set Circle) →
      f^[q + 1] '' (J : Set Circle) = (D : Set Circle) := by
    intro J I hJI hID
    simpa only [Function.iterate_succ', Set.image_comp, hJI] using hID
  have hp : ∀ s ≤ q + 1, ∀ x ∈ (L' : Set Circle) ∪ (R' : Set Circle),
      ∀ y ∈ (L' : Set Circle) ∪ (R' : Set Circle), dist (f^[s] x) (f^[s] y) < η := by
    intro s hs x hx y hy
    exact hsmall s hs x ((union_subset hLB hRB) hx) y ((union_subset hLB hRB) hy)
  refine ⟨H.double hf L' R' D (hLB.trans hBA) (hRB.trans hBA) hdis'
    (hlast L' L hL' hFL) (hlast R' R hR' hFR) hp, ?_⟩
  exact Nat.add_assoc _ _ _ |>.symm

/-- Terminal equality supplies the entire infinite tail using the shared
metric-general interval API. No finite-time check is substituted for it. -/
theorem card_le [Fintype ι] [Nonempty ι] (H : Histories f η ι)
    {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hηε : η ≤ ε)
    (hB : ForwardBowenBound f univ ε N) : Fintype.card ι ≤ N := by
  classical
  obtain ⟨z, hz⟩ := H.terminal.infinite.nonempty
  have hpre : ∀ i, ∃ x ∈ (H.domain i : Set Circle), f^[H.time] x = z :=
    fun i => (H.onto i).symm.subset hz
  choose x hx hT using hpre
  have hxi : Injective x := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (H.disjoint i j hne) (hx i) (hij.symm ▸ hx j)
  by_contra! hm
  let e := (Fintype.equivFin ι).symm
  apply no_coalescing_witnesses hB hε hm (fun i => x (e i))
    (hxi.comp e.injective) (fun _ => mem_univ _)
  · intro i j s hs
    exact (H.small s hs (e i) (e j) _ (hx (e i)) _ (hx (e j))).trans_le hηε
  · intro i j
    exact (hT (e i)).trans (hT (e j)).symm

end Histories

/-- An actual lifted strict turn gives separated common-image circle arcs.
The target-chart bound is proved from continuity, not a monotone-branch
assumption. This is the fold construction, prior to the accessibility step. -/
theorem fold_of_lifted_strict_turn (A : Arc) {f : Circle → Circle}
    {G : ℝ → ℝ} (hG : Continuous G)
    (hlift : ∀ t, project (G t) = f (project t))
    {c δ : ℝ} (hc : c ∈ Ioo A.segment.left A.segment.right) (hδ : 0 < δ)
    (hturn : (∀ y, dist y c < δ → y ≠ c → G y < G c) ∨
      (∀ y, dist y c < δ → y ≠ c → G c < G y)) :
    ∃ L R D : Arc, (L : Set Circle) ⊆ (A : Set Circle) ∧
      (R : Set Circle) ⊆ (A : Set Circle) ∧
      Disjoint (L : Set Circle) (R : Set Circle) ∧
      f '' (L : Set Circle) = (D : Set Circle) ∧
      f '' (R : Set Circle) = (D : Set Circle) := by
  obtain ⟨γ, hγ, hg⟩ := Metric.continuousAt_iff.mp (hG.continuousAt : ContinuousAt G c)
    (1 / 8) (by norm_num)
  have hm : 0 < min δ (min γ (min (c - A.segment.left) (A.segment.right - c))) :=
    lt_min hδ (lt_min hγ (lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)))
  obtain ⟨h, hh, hsmall⟩ := exists_between hm
  have hhδ : h < δ := hsmall.trans_le (min_le_left _ _)
  have hhγ : h < γ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhl : h < c - A.segment.left := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhr : h < A.segment.right - c := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have huc : c - h < c := by linarith
  have hcv : c < c + h := by linarith
  have hBA : Icc (c - h) (c + h) ⊆ (A.segment : Set ℝ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hdist : ∀ t ∈ Icc (c - h) (c + h), dist t c ≤ h := by
    intro t ht
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hleft : dist (c - h) c < δ := (hdist _ ⟨le_rfl, by linarith⟩).trans_lt hhδ
  have hright : dist (c + h) c < δ := (hdist _ ⟨by linarith, le_rfl⟩).trans_lt hhδ
  have hfold : ∃ L R D : Segment, (L : Set ℝ) ⊆ Icc (c - h) c ∧
      (R : Set ℝ) ⊆ Icc c (c + h) ∧ Disjoint (L : Set ℝ) (R : Set ℝ) ∧
      G '' (L : Set ℝ) = (D : Set ℝ) ∧ G '' (R : Set ℝ) = (D : Set ℝ) := by
    rcases hturn with hp | ht
    · exact disjoint_fold_of_peak huc hcv hG.continuousOn
        (hp _ hleft (by linarith)) (hp _ hright (by linarith))
    · exact disjoint_fold_of_trough huc hcv hG.continuousOn
        (ht _ hleft (by linarith)) (ht _ hright (by linarith))
  obtain ⟨L, R, D, hL, hR, hd, hGL, hGR⟩ := hfold
  have hLA : (L : Set ℝ) ⊆ (A.segment : Set ℝ) :=
    (hL.trans (Icc_subset_Icc le_rfl hcv.le)).trans hBA
  have hRA : (R : Set ℝ) ⊆ (A.segment : Set ℝ) :=
    (hR.trans (Icc_subset_Icc huc.le le_rfl)).trans hBA
  have hDsmall : ∀ t ∈ (D : Set ℝ), dist t (G c) < 1 / 8 := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := hGL.symm.subset ht
    apply hg
    exact (hdist u ((hL.trans (Icc_subset_Icc le_rfl hcv.le)) hu)).trans_lt hhγ
  have hl := hDsmall D.left ⟨le_rfl, D.proper.le⟩
  have hr := hDsmall D.right ⟨D.proper.le, le_rfl⟩
  have hDlen : D.right - D.left < 1 := by
    rw [Real.dist_eq, abs_lt] at hl hr
    linarith [hl.1, hl.2, hr.1, hr.2]
  let L' := A.subarc L hLA
  let R' := A.subarc R hRA
  let D' : Arc := ⟨D, hDlen⟩
  have heq : ∀ J : Segment, G '' (J : Set ℝ) = (D : Set ℝ) →
      f '' (project '' (J : Set ℝ)) = (D' : Set Circle) := by
    intro J hJ
    ext x
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [← hlift]
      exact mem_image_of_mem project (hJ.subset (mem_image_of_mem _ hu))
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, huG⟩ := hJ.symm.subset hv
      exact ⟨project u, ⟨u, hu, rfl⟩, (hlift u).symm.trans (congrArg project huG)⟩
  refine ⟨L', R', D', A.subarc_subset L hLA, A.subarc_subset R hRA,
    Set.disjoint_left.mpr ?_, heq L hGL, heq R hGR⟩
  rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
  have huv : u = v := A.project_injOn (hLA hu) (hRA hv) (hux.trans hvx.symm)
  exact Set.disjoint_left.mp hd hu (huv.symm ▸ hv)


/-- A genuine turn supplies exact fold branches inside every open circle
neighborhood of its actual projected point. This avoids identifying different
real representatives of a turn by an unproved chart or metric convention. -/
theorem fold_in_open_neighborhood {f : Circle → Circle} {F : ℝ → ℝ}
    (hF : Continuous F) (hlift : ∀ t, project (F t) = f (project t))
    {c : ℝ} (hturn : LiftedTurn F c) {U : Set Circle}
    (hU : IsOpen U) (hcU : project c ∈ U) :
    ∃ L R D : Arc, (L : Set Circle) ⊆ U ∧ (R : Set Circle) ⊆ U ∧
      Disjoint (L : Set Circle) (R : Set Circle) ∧
      f '' (L : Set Circle) = (D : Set Circle) ∧
      f '' (R : Set Circle) = (D : Set Circle) := by
  have hpre : project ⁻¹' U ∈ 𝓝 c :=
    (hU.preimage (AddCircle.continuous_mk' (1 : ℝ))).mem_nhds hcU
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  let h := min (r / 2) (1 / 4)
  have hh : 0 < h := lt_min (by positivity) (by norm_num)
  have hhr : h < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hh4 : h ≤ 1 / 4 := min_le_right _ _
  let A : Arc := ⟨⟨c - h, c + h, by linarith⟩, by dsimp; linarith⟩
  have hAU : (A : Set Circle) ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    apply hsub
    change dist t c < r
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨δ, hδ, hc⟩ := hturn
  obtain ⟨L, R, D, hL, hR, hd, hFL, hFR⟩ := fold_of_lifted_strict_turn A hF hlift
    (c := c) (by change c - h < c ∧ c < c + h; constructor <;> linarith) hδ hc
  exact ⟨L, R, D, hL.trans hAU, hR.trans hAU, hd, hFL, hFR⟩

/-- Concrete transit and fold assembly. A supplied actual lifted crossing
is shrunk with every time through q+1 controlled. Its image is proved proper
using an explicit antipode, then classified as an actual arc. Genuine fold
branches are selected inside that image and pulled back exactly. The
global two-target bridge supplies this crossing under the original hypotheses
in `Histories.extend` below. -/
theorem Histories.extend_crossing_turn {f : Circle → Circle} {η ε : ℝ}
    {ι : Type*} {N q : ℕ} (H : Histories f η ι) (hf : Continuous f)
    (hε : 0 < ε) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hB : ForwardBowenBound f univ ε N) {G F : ℝ → ℝ}
    (hG : Continuous G) (hGf : ∀ t, project (G t) = f^[q] (project t))
    (hF : Continuous F) (hFf : ∀ t, project (F t) = f (project t))
    {v c : ℝ} (hvc : project c = project v) (hturn : LiftedTurn F c)
    (hbelow : ∃ u ∈ (H.terminal.segment : Set ℝ), G u < v)
    (habove : ∃ w ∈ (H.terminal.segment : Set ℝ), v < G w) :
    ∃ H' : Histories f η (ι × Bool), H'.time = H.time + q + 1 := by
  obtain ⟨B, hBA, hc, hsmall⟩ :=
    small_circle_crossing hf hε hη hB H.terminal hG hGf hbelow habove
  have hproper : f^[q] '' (B : Set Circle) ≠ univ := by
    intro hfull
    obtain ⟨x, hx⟩ := B.infinite.nonempty
    let a := project (coordinate 0 (f^[q] x) + 1 / 2)
    obtain ⟨y, hy, he⟩ := hfull.symm.subset (mem_univ a)
    have hd := hsmall q (by omega) y hy x hx
    have hedist : dist (f^[q] y) (f^[q] x) = 1 / 2 := by
      rw [he]
      exact antipode_distance _
    rw [hedist] at hd
    linarith
  have hinf : (f^[q] '' (B : Set Circle)).Infinite :=
    infinite_iterate_image (mapsTo_univ f univ) (finite_fibres isCompact_univ hB hε)
      (subset_univ _) B.infinite q
  obtain ⟨E, hE⟩ := arc_of_compact_connected (B.compact.image (hf.iterate q))
    (B.connected.image (f^[q]) (hf.iterate q).continuousOn) hinf hproper
  have hcE : project c ∈ interior (E : Set Circle) := by
    rw [hvc, ← hE]
    exact hc
  obtain ⟨L, R, D, hL, hR, hd, hFL, hFR⟩ :=
    fold_in_open_neighborhood hF hFf hturn isOpen_interior hcE
  exact H.extend_transit_fold hf B E L R D q hBA hE
    (hL.trans interior_subset) (hR.trans interior_subset) hd hFL hFR hsmall

/-- The full-image branch genuinely uses the two distinct turns: a one-turn
seam may be inaccessible even when the image is the whole circle. No specified
turn is incorrectly inferred to be crossed. This is a single proved extension
step in this branch, not an assumed global ability to extend histories. -/
theorem Histories.extend_of_full_image {f : Circle → Circle} {η : ℝ} {ι : Type*}
    (H : Histories f η ι) (hf : Continuous f) (hfin : FinitelyPositiveExpansive f)
    (hloc : ¬IsLocallyInjective f) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    {q : ℕ} (hfull : f^[q] '' (H.terminal : Set Circle) = univ) :
    ∃ H' : Histories f η (ι × Bool), H'.time = H.time + q + 1 := by
  obtain ⟨F, hF, hFf, c, d, hcd, hc, hd⟩ := two_distinct_lifted_turns hf hfin hloc
  obtain ⟨G, hG, hGf, v, hv, hbelow, habove⟩ :=
    two_target_crossing_of_full_image (hf.iterate q) H.terminal hfull
      (project c) (project d) hcd
  obtain ⟨ε, hε, N, _, hB⟩ := id hfin
  rcases hv with hv | hv
  · exact H.extend_crossing_turn hf hε hη hη8 hB hG hGf hF hFf
      hv.symm hc hbelow habove
  · exact H.extend_crossing_turn hf hε hη hη8 hB hG hGf hF hFf
      hv.symm hd hbelow habove

/-- Under precisely the original hypotheses and failure of local injectivity,
one of the two genuine turns is accessible from the current terminal arc.
The actual crossing construction doubles the histories, including its final
coalescing application of f at time T+q+1. -/
theorem Histories.extend {f : Circle → Circle} {η : ℝ} {ι : Type*}
    (H : Histories f η ι) (hf : Continuous f) (hfin : FinitelyPositiveExpansive f)
    (hloc : ¬IsLocallyInjective f) (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∃ q : ℕ, ∃ H' : Histories f η (ι × Bool), H'.time = H.time + q + 1 := by
  obtain ⟨F, hF, hFf, c, d, hcd, hc, hd⟩ := two_distinct_lifted_turns hf hfin hloc
  obtain ⟨q, G, hG, hGf, v, hv, hbelow, habove⟩ :=
    two_target_crossing hf hfin H.terminal (project c) (project d) hcd
  obtain ⟨ε, hε, N, _, hB⟩ := id hfin
  rcases hv with hv | hv
  · exact ⟨q, H.extend_crossing_turn hf hε hη hη8 hB hG hGf hF hFf
      hv.symm hc hbelow habove⟩
  · exact ⟨q, H.extend_crossing_turn hf hε hη hη8 hB hG hGf hF hFf
      hv.symm hd hbelow habove⟩

/-- Actual 2^k disjoint circle histories, obtained by iterating the proved
two-target bridge. The conclusion contains the original Histories structure
with exact terminal equality and its full finite-horizon metric estimates. -/
theorem arbitrarily_many_circle_histories {f : Circle → Circle} (hf : Continuous f)
    (hfin : FinitelyPositiveExpansive f) (hloc : ¬IsLocallyInjective f)
    {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (k : ℕ) :
    ∃ (ι : Type) (hι : Fintype ι) (_ : Nonempty ι),
      ∃ H : Histories f η ι, @Fintype.card ι hι = 2 ^ k := by
  classical
  induction k with
  | zero =>
    exact ⟨Unit, inferInstance, inferInstance, Histories.initial f hη, by simp⟩
  | succ k ih =>
    obtain ⟨ι, hι, hne, H, hcard⟩ := ih
    letI := hι
    letI := hne
    obtain ⟨q, H', _⟩ := H.extend hf hfin hloc hη hη8
    refine ⟨ι × Bool, inferInstance, inferInstance, H', ?_⟩
    simpa only [Fintype.card_prod, Fintype.card_bool, pow_succ, hcard]

/-- Local injectivity is a consequence of the original uniform finite bound.
The 2^N actual histories yield distinct coalescing witnesses whose entire
infinite tails coincide, contradicting that same N and strict Bowen scale. -/
theorem isLocallyInjective_of_finitelyPositiveExpansive {f : Circle → Circle}
    (hf : Continuous f) (hfin : FinitelyPositiveExpansive f) : IsLocallyInjective f := by
  classical
  by_contra hloc
  obtain ⟨ε, hε, N, _, hB⟩ := id hfin
  let η := min ε (1 / 8)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hη8 : η ≤ 1 / 8 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  obtain ⟨ι, hι, hne, H, hcard⟩ :=
    arbitrarily_many_circle_histories hf hfin hloc hη hη8 N
  letI := hι
  letI := hne
  have hle := H.card_le hε hηε hB
  rw [hcard] at hle
  exact (not_le_of_gt N.lt_two_pow_self) hle

/-- Under the original hypotheses the actual circle map is onto. The image
is infinite by finite fibres and is a proper arc if it is not the whole circle;
its forward invariance then contradicts the subtype interval theorem. -/
theorem surjective (f : Circle → Circle) (hf : Continuous f)
    (hfin : FinitelyPositiveExpansive f) : Surjective f := by
  obtain ⟨ε, hε, N, hN, hB⟩ := id hfin
  have hfib := finite_fibres isCompact_univ hB hε
  let J : Arc := ⟨⟨0, 1 / 4, by norm_num⟩, by norm_num⟩
  have hinf : (range f).Infinite := by
    apply (infinite_iterate_image (mapsTo_univ f univ) hfib
      (subset_univ (J : Set Circle)) J.infinite 1).mono
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, by simp⟩
  by_contra hsurj
  have hproper : range f ≠ univ := by
    intro he
    apply hsurj
    intro y
    exact he.symm.subset (mem_univ y)
  have hcompact : IsCompact (range f) := by simpa using isCompact_univ.image hf
  have hconnected : IsConnected (range f) := by
    simpa using (isConnected_univ : IsConnected (univ : Set Circle)).image f hf.continuousOn
  obtain ⟨A, hA⟩ := arc_of_compact_connected hcompact hconnected hinf hproper
  apply no_periodic_trapping_arc hf hε hB hN (p := 1) (by omega) A
  rw [← hA]
  intro x hx
  exact ⟨x, by simp⟩

/-- Every actual arc has arbitrarily late images with macroscopic separation.
The image is classified as either the whole circle or a genuine proper arc;
the separation scale is the original strict all-time Bowen bound's scale. -/
theorem arbitrarily_late_macroscopic_arc {f : Circle → Circle} (hf : Continuous f)
    {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hB : ForwardBowenBound f univ ε N)
    (A : Arc) (M : ℕ) :
    ∃ n ≥ M, f^[n] '' (A : Set Circle) = univ ∨
      ∃ B : Arc, f^[n] '' (A : Set Circle) = (B : Set Circle) ∧
        ∃ x ∈ (B : Set Circle), ∃ y ∈ (B : Set Circle), ε ≤ dist x y := by
  have hfib := finite_fibres isCompact_univ hB hε
  obtain ⟨n, hn, x, hx, y, hy, hsep⟩ := arbitrarily_late_separation hB
    (mapsTo_univ f univ) hε hfib (subset_univ _) A.infinite M
  refine ⟨n, hn, ?_⟩
  by_cases hfull : f^[n] '' (A : Set Circle) = univ
  · exact Or.inl hfull
  · have hinf := infinite_iterate_image (mapsTo_univ f univ) hfib
      (subset_univ _) A.infinite n
    obtain ⟨B, hBA⟩ := arc_of_compact_connected (A.compact.image (hf.iterate n))
      (A.connected.image (f^[n]) (hf.iterate n).continuousOn) hinf hfull
    exact Or.inr ⟨B, hBA, f^[n] x, hBA.subset (mem_image_of_mem _ hx),
      f^[n] y, hBA.subset (mem_image_of_mem _ hy), hsep⟩

/-- Compactness turns actual local injectivity into one uniform radius.
This supplies a geometric scale, not an additional assumption in the original
circle target. Local injectivity is established above from its original hypotheses. -/
private theorem uniform_injective_balls {f : Circle → Circle}
    (hloc : IsLocallyInjective f) :
    ∃ scale > 0, ∀ x, InjOn f (Metric.ball x scale) := by
  classical
  choose U hU hxU hiU using hloc
  have hcover : (univ : Set Circle) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨scale, hscale, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  refine ⟨scale, hscale, fun x => ?_⟩
  obtain ⟨z, hz⟩ := hball x (mem_univ _)
  exact (hiU z).mono hz

/-- The short-arc argument, with every iterate and the full infinite Bowen
condition. This intermediate result discharges the last section of the sealed
proof once local injectivity is proved from its original hypotheses. -/
theorem positivelyExpansive_of_locallyInjective (f : Circle → Circle) (hf : Continuous f)
    (hfin : FinitelyPositiveExpansive f) (hloc : IsLocallyInjective f) :
    PositivelyExpansive f := by
  obtain ⟨ε, hε, N, _, hB⟩ := id hfin
  obtain ⟨scale, hscale, hscalei⟩ := uniform_injective_balls hloc
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) (1 / 8) (by norm_num)
  let e := min ε (min scale (min δ (1 / 8)))
  have he : 0 < e := lt_min hε (lt_min hscale (lt_min hδ (by norm_num)))
  have heε : e ≤ ε := min_le_left _ _
  have hescale : e ≤ scale := (min_le_right _ _).trans (min_le_left _ _)
  have heδ : e ≤ δ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  refine ⟨e, he, fun x y hxy => ?_⟩
  have hstep : ∀ n : ℕ,
      f '' shortArc (f^[n] x) (f^[n] y) =
        shortArc (f^[n + 1] x) (f^[n + 1] y) := by
    intro n
    have hsub : shortArc (f^[n] x) (f^[n] y) ⊆ Metric.ball (f^[n] x) scale := by
      intro z hz
      exact (shortArc_dist_le hz).trans_lt ((hxy n).trans_le hescale)
    have hi := (hscalei (f^[n] x)).mono hsub
    have hsmall : ∀ z ∈ shortArc (f^[n] x) (f^[n] y),
        dist (f z) (f (f^[n] x)) < 1 / 8 := by
      intro z hz
      exact hd ((shortArc_dist_le hz).trans_lt ((hxy n).trans_le heδ))
    simpa only [Function.iterate_succ_apply'] using
      image_shortArc f hf (f^[n] x) (f^[n] y) hi hsmall
  have himages : ∀ n : ℕ, f^[n] '' shortArc x y = shortArc (f^[n] x) (f^[n] y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ', Set.image_comp, ih]
      simpa only [Function.iterate_succ', Function.comp_apply] using hstep n
  by_contra hne
  apply shortArc_infinite hne
  apply finite_of_all_times_small hB (subset_univ _) x (shortArc_left x y)
  intro z hz n
  have hz' : f^[n] z ∈ shortArc (f^[n] x) (f^[n] y) :=
    (himages n).subset (mem_image_of_mem _ hz)
  rw [dist_comm]
  exact (shortArc_dist_le hz').trans_lt ((hxy n).trans_le heε)

/-- The original circle theorem, with no additional dynamical or local
injectivity premise. -/
theorem positivelyExpansive_of_finitelyPositiveExpansive
    (f : AddCircle (1 : ℝ) → AddCircle (1 : ℝ)) (hf : Continuous f)
    (hfin : FinitelyPositiveExpansive f) : PositivelyExpansive f := by
  exact positivelyExpansive_of_locallyInjective f hf hfin
    (isLocallyInjective_of_finitelyPositiveExpansive hf hfin)

end D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness
