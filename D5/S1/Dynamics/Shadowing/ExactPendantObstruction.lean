/- GID: D5/S1/Dynamics/Shadowing/ExactPendantObstruction
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ExactPendantObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact pendant-arc dynamics gives arbitrarily large coalescing Bowen families. -/

import D5.S1.Dynamics.Shadowing.IntervalObstruction.Basic

/-!
The leaf hit supplies two pointwise lifts of each witness in a smaller open subarc.
The forward Bowen obstruction uses the coalescence principle of
Gangloff–Guillon–Oprocha, arXiv:2310.17241v1, Remark 3.4.
-/

open Set Function Topology

namespace D5.S1.Dynamics.Shadowing

/-- A unit interval attached at its zero endpoint, with the rest of the arc open in the carrier. -/
structure PendantArc (X : Type*) [TopologicalSpace X] where
  param : Icc (0 : ℝ) 1 → X
  continuous_param : Continuous param
  injective_param : Injective param
  isOpen_tip : IsOpen (param '' {t | 0 < (t : ℝ)})

namespace PendantArc

variable {X : Type*} [MetricSpace X]

private noncomputable def point (P : PendantArc X) (t : ℝ) : X :=
  P.param (projIcc 0 1 zero_le_one t)

/-- The points with coordinates strictly between the two real bounds. -/
def subarc (P : PendantArc X) (a b : ℝ) : Set X :=
  P.param '' (Subtype.val ⁻¹' Ioo a b)

/-- The free endpoint of the pendant arc. -/
def leaf (P : PendantArc X) : X :=
  P.param ⟨1, zero_le_one, le_rfl⟩

private theorem continuous_point (P : PendantArc X) : Continuous P.point :=
  P.continuous_param.comp continuous_projIcc

private theorem injOn_point (P : PendantArc X) : InjOn P.point (Icc (0 : ℝ) 1) := by
  intro s hs t ht he
  have he' := P.injective_param he
  rw [projIcc_of_mem zero_le_one hs, projIcc_of_mem zero_le_one ht] at he'
  exact congrArg Subtype.val he'

private theorem subarc_eq_image (P : PendantArc X) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    P.subarc a b = P.point '' Ioo a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by rw [point, projIcc_of_mem zero_le_one t.property]⟩
  · rintro ⟨t, ht, rfl⟩
    have h : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩
    exact ⟨⟨t, h⟩, ht, by rw [point, projIcc_of_mem zero_le_one h]⟩

private theorem isOpen_subarc (P : PendantArc X) {a b : ℝ} (ha : 0 ≤ a) :
    IsOpen (P.subarc a b) := by
  have he := (P.continuous_param.isClosedEmbedding P.injective_param).isEmbedding
  obtain ⟨U, hU, hEq⟩ := he.isInducing.isOpen_iff.mp
    (continuous_subtype_val.isOpen_preimage (Ioo a b) isOpen_Ioo)
  have hs : P.subarc a b = U ∩ P.param '' {t | 0 < (t : ℝ)} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨show t ∈ P.param ⁻¹' U from hEq.symm ▸ ht,
        mem_image_of_mem _ (ha.trans_lt ht.1)⟩
    · rintro ⟨hxU, t, _, rfl⟩
      exact ⟨t, hEq ▸ (show t ∈ P.param ⁻¹' U from hxU), rfl⟩
  rw [hs]
  exact hU.inter P.isOpen_tip

private noncomputable def coord (P : PendantArc X) (x : X) : ℝ := by
  classical
  exact if h : x ∈ range P.param then
    ((P.continuous_param.isClosedEmbedding P.injective_param).isEmbedding.toHomeomorph.symm
      ⟨x, h⟩ : ℝ)
  else 0

private theorem continuousOn_coord (P : PendantArc X) : ContinuousOn P.coord (range P.param) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let e := (P.continuous_param.isClosedEmbedding P.injective_param).isEmbedding.toHomeomorph
  have h : (range P.param).domRestrict P.coord = Subtype.val ∘ e.symm := by
    funext x
    simp only [Set.domRestrict, coord, dif_pos x.property, Function.comp_apply, e]
  rw [h]
  exact continuous_subtype_val.comp e.symm.continuous

private theorem coord_param (P : PendantArc X) (t : Icc (0 : ℝ) 1) :
    P.coord (P.param t) = t := by
  simp [coord]

private theorem point_coord (P : PendantArc X) {x : X} (hx : x ∈ range P.param) :
    P.point (P.coord x) = x := by
  obtain ⟨t, rfl⟩ := hx
  rw [coord_param, point, projIcc_of_mem zero_le_one t.property]

private theorem coord_mem (P : PendantArc X) {x : X}
    (hx : x ∈ P.param '' {t | 0 < (t : ℝ)}) : P.coord x ∈ Ioc (0 : ℝ) 1 := by
  obtain ⟨t, ht, rfl⟩ := hx
  rw [coord_param]
  exact ⟨ht, t.property.2⟩

private theorem leaf_mem_tip (P : PendantArc X) : P.leaf ∈ P.param '' {t | 0 < (t : ℝ)} :=
  ⟨⟨1, zero_le_one, le_rfl⟩, show (0 : ℝ) < 1 from zero_lt_one, rfl⟩

end PendantArc

namespace ExactPendantObstruction

open IntervalObstruction

variable {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → X}

/-- Every nonempty ambient open set maps onto the carrier at a positive time. -/
def TopologicallyExact (f : X → X) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → ∃ r : ℕ, 0 < r ∧ f^[r] '' U = univ

private theorem one_hit_fold (P : PendantArc X) (hf : Continuous f) (hex : TopologicallyExact f)
    (hfib : ∀ r : ℕ, ((f^[r]) ⁻¹' {P.leaf}).Finite)
    {ε a b : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ r : ℕ, 0 < r ∧ ∃ a' b' : ℝ, 0 ≤ a' ∧ a' < b' ∧ b' ≤ 1 ∧
      ∃ L R : Set X, L ∪ R ⊆ P.subarc a b ∧ Disjoint L R ∧
        P.subarc a' b' ⊆ f^[r] '' L ∧ P.subarc a' b' ⊆ f^[r] '' R ∧
        ∀ s ≤ r, ∀ x ∈ L ∪ R, ∀ y ∈ L ∪ R, dist (f^[s] x) (f^[s] y) < ε := by
  have hU : (P.subarc a b).Nonempty := by
    rw [P.subarc_eq_image ha hb]
    exact (nonempty_Ioo.mpr hab).image _
  obtain ⟨r, hr, honto⟩ := hex _ (P.isOpen_subarc ha) hU
  obtain ⟨x, hx, hleaf⟩ := honto.symm.subset (mem_univ P.leaf)
  rw [P.subarc_eq_image ha hb] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨δ, hδ, hscale⟩ := finite_block_scale isCompact_univ hf.continuousOn
    (mapsTo_univ f univ) hε (r + 1)
  let H : ℝ → X := (f^[r]) ∘ P.point
  have hH : Continuous H := (hf.iterate r).comp P.continuous_point
  let S := (f^[r]) ⁻¹' {P.leaf} \ {P.point c}
  have hS : S.Finite := (hfib r).sdiff
  let V := Metric.ball (P.point c) (δ / 3) ∩ Sᶜ
  have hV : IsOpen V := Metric.isOpen_ball.inter hS.isClosed.isOpen_compl
  let W := Ioo a b ∩ P.point ⁻¹' V ∩ H ⁻¹' (P.param '' {t | 0 < (t : ℝ)})
  have hW : IsOpen W := (isOpen_Ioo.inter (hV.preimage P.continuous_point)).inter
    (P.isOpen_tip.preimage hH)
  have hcW : c ∈ W := by
    refine ⟨⟨hc, Metric.mem_ball_self (by positivity), ?_⟩, ?_⟩
    · simp [S]
    · change H c ∈ P.param '' {t | 0 < (t : ℝ)}
      rw [show H c = P.leaf from hleaf]
      exact P.leaf_mem_tip
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hcW)
  let u := c - ρ / 2
  let v := c + ρ / 2
  have huc : u < c := by dsimp [u]; linarith
  have hcv : c < v := by dsimp [v]; linarith
  have huvW : Icc u v ⊆ W := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hlu : c - ρ / 2 ≤ t := ht.1
    have hrv : t ≤ c + ρ / 2 := ht.2
    constructor <;> linarith
  have huW := huvW (left_mem_Icc.mpr (huc.trans hcv).le)
  have hvW := huvW (right_mem_Icc.mpr (huc.trans hcv).le)
  have point_ne {t : ℝ} (ht : t ∈ W) (hne : t ≠ c) : P.point t ≠ P.point c := by
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1.1.1.le, ht.1.1.2.le.trans hb⟩
    have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hc.1.le, hc.2.le.trans hb⟩
    exact fun he => hne (P.injOn_point htI hcI he)
  have no_leaf {t : ℝ} (ht : t ∈ W) (hne : t ≠ c) : H t ≠ P.leaf := by
    intro he
    exact ht.1.2.2 ⟨he, point_ne ht hne⟩
  let G := P.coord ∘ H
  have hG : ContinuousOn G (Icc u v) := P.continuousOn_coord.comp hH.continuousOn
    (fun t ht => image_subset_range _ _ (huvW ht).2)
  have hGc : G c = 1 := by
    change P.coord (H c) = 1
    rw [show H c = P.leaf from hleaf]
    exact P.coord_param _
  have coord_lt_one {t : ℝ} (ht : t ∈ W) (hne : t ≠ c) : G t < 1 := by
    refine lt_of_le_of_ne (P.coord_mem ht.2).2 (fun he => no_leaf ht hne ?_)
    rw [← P.point_coord (image_subset_range _ _ ht.2), show P.coord (H t) = 1 from he]
    exact congrArg P.param (projIcc_right zero_le_one)
  let a' := max (G u) (G v)
  have ha' : 0 ≤ a' := (P.coord_mem huW.2).1.le.trans (le_max_left _ _)
  have ha'1 : a' < 1 := max_lt (coord_lt_one huW huc.ne) (coord_lt_one hvW hcv.ne')
  let L := P.point '' Ico u c
  let R := P.point '' Ioc c v
  have hL : Ico u c ⊆ Icc u v := fun _ ht => ⟨ht.1, ht.2.le.trans hcv.le⟩
  have hR : Ioc c v ⊆ Icc u v := fun _ ht => ⟨huc.le.trans ht.1.le, ht.2⟩
  have hinside : L ∪ R ⊆ P.point '' W :=
    union_subset (image_mono (hL.trans huvW)) (image_mono (hR.trans huvW))
  refine ⟨r, hr, a', 1, ha', ha'1, le_rfl, L, R, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P.subarc_eq_image ha hb]
    exact hinside.trans (image_mono (fun _ ht => ht.1.1))
  · refine disjoint_left.mpr ?_
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
    have hsW := huvW (hL hs)
    have htW := huvW (hR ht)
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hsW.1.1.1.le, hsW.1.1.2.le.trans hb⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans htW.1.1.1.le, htW.1.1.2.le.trans hb⟩
    exact (hs.2.trans ht.1).ne' (P.injOn_point htI hsI he)
  · rw [P.subarc_eq_image ha' le_rfl]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Icc (G u) (G c) := ⟨(le_max_left _ _).trans hy.1.le, hGc ▸ hy.2.le⟩
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc huc.le
      (hG.mono (Icc_subset_Icc le_rfl hcv.le)) hy'
    have htc : t < c := lt_of_le_of_ne ht.2 (by rintro rfl; exact hy.2.ne (he.symm.trans hGc))
    have htW := huvW (Icc_subset_Icc le_rfl hcv.le ht)
    exact ⟨P.point t, ⟨t, ⟨ht.1, htc⟩, rfl⟩,
      (P.point_coord (image_subset_range _ _ htW.2)).symm.trans (congrArg P.point he)⟩
  · rw [P.subarc_eq_image ha' le_rfl]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Icc (G v) (G c) := ⟨(le_max_right _ _).trans hy.1.le, hGc ▸ hy.2.le⟩
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hcv.le
      (hG.mono (Icc_subset_Icc huc.le le_rfl)) hy'
    have hct : c < t := lt_of_le_of_ne ht.1 (by rintro rfl; exact hy.2.ne (he.symm.trans hGc))
    have htW := huvW (Icc_subset_Icc huc.le le_rfl ht)
    exact ⟨P.point t, ⟨t, ⟨hct, ht.2⟩, rfl⟩,
      (P.point_coord (image_subset_range _ _ htW.2)).symm.trans (congrArg P.point he)⟩
  · intro s hs x hx y hy
    obtain ⟨tx, htx, rfl⟩ := hinside hx
    obtain ⟨ty, hty, rfl⟩ := hinside hy
    have hx' : dist (P.point tx) (P.point c) < δ / 3 := htx.1.2.1
    have hy' : dist (P.point c) (P.point ty) < δ / 3 := by
      rw [dist_comm]
      exact hty.1.2.1
    exact hscale s (Nat.lt_succ_of_le hs) _ (mem_univ _) _ (mem_univ _)
      (by linarith [dist_triangle (P.point tx) (P.point c) (P.point ty)])

/-- With finite iterate fibres over the leaf, every interior subarc contains
`2 ^ k` distinct witnesses that stay strictly close and coalesce. -/
theorem local_coalescing_witnesses (P : PendantArc X) (hf : Continuous f)
    (hex : TopologicallyExact f) (hfib : ∀ r : ℕ, ((f^[r]) ⁻¹' {P.leaf}).Finite)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ T : ℕ, ∃ x : Fin (2 ^ k) → X, Injective x ∧ (∀ i, x i ∈ P.subarc a b) ∧
      (∀ i j t, dist (f^[t] (x i)) (f^[t] (x j)) < ε) ∧
      ∀ i j, f^[T] (x i) = f^[T] (x j) := by
  classical
  induction k generalizing a b with
  | zero =>
    obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hab
    have hx : P.point c ∈ P.subarc a b := by
      rw [P.subarc_eq_image ha hb]
      exact mem_image_of_mem _ hc
    haveI : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨0, fun _ => P.point c, fun _ _ _ => Subsingleton.elim _ _, fun _ => hx,
      fun _ _ _ => by simpa, fun _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨r, _, a', b', ha', hab', hb', L, R, hsub, hdis, hL, hR, hprefix⟩ :=
      one_hit_fold P hf hex hfib hε ha hab hb
    obtain ⟨T, x, hxi, hx, hclose, hterm⟩ := ih ha' hab' hb'
    choose left hl hlx using fun i => hL (hx i)
    choose right hr hrx using fun i => hR (hx i)
    let lift : Fin (2 ^ k) × Fin 2 → X := fun (i, side) => if side = 0 then left i else right i
    have hLift (i : Fin (2 ^ k) × Fin 2) : f^[r] (lift i) = x i.1 := by
      by_cases hi : i.2 = 0
      · simpa [lift, hi] using hlx i.1
      · simpa [lift, hi] using hrx i.1
    have hside (i : Fin (2 ^ k) × Fin 2) :
        lift i ∈ if i.2 = 0 then L else R := by
      by_cases hi : i.2 = 0
      · simpa [lift, hi] using hl i.1
      · simpa [lift, hi] using hr i.1
    have hmem (i : Fin (2 ^ k) × Fin 2) : lift i ∈ L ∪ R := by
      by_cases hi : i.2 = 0
      · exact Or.inl (by simpa [hi] using hside i)
      · exact Or.inr (by simpa [hi] using hside i)
    have hinj : Injective lift := by
      intro i j he
      have hij := hxi ((hLift i).symm.trans ((congrArg (f^[r]) he).trans (hLift j)))
      refine Prod.ext hij ?_
      have hjmem : lift i ∈ if j.2 = 0 then L else R := he ▸ hside j
      by_cases hi : i.2 = 0 <;> by_cases hj : j.2 = 0
      · exact hi.trans hj.symm
      · exact (disjoint_left.mp hdis (by simpa [hi] using hside i)
          (by simpa [hj] using hjmem)).elim
      · exact (disjoint_left.mp hdis (by simpa [hj] using hjmem)
          (by simpa [hi] using hside i)).elim
      · exact (Fin.eq_one_of_ne_zero _ hi).trans (Fin.eq_one_of_ne_zero _ hj).symm
    let e : Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k) × Fin 2 :=
      (finCongr (pow_succ 2 k)).trans finProdFinEquiv.symm
    refine ⟨T + r, lift ∘ e, hinj.comp e.injective, fun i => hsub (hmem (e i)), ?_, ?_⟩
    · intro i j t
      by_cases ht : t ≤ r
      · exact hprefix t ht _ (hmem (e i)) _ (hmem (e j))
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge ht)
        rw [Nat.add_comm r s, Function.comp_apply, Function.comp_apply,
          Function.iterate_add_apply, Function.iterate_add_apply, hLift, hLift]
        exact hclose _ _ _
    · intro i j
      simp only [Function.comp_apply, Function.iterate_add_apply, hLift]
      exact hterm _ _

private theorem witnesses_of_infinite_fibre {z : X} (hz : (f ⁻¹' {z}).Infinite)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ x : Fin m → X, Injective x ∧ (∀ i j t, dist (f^[t] (x i)) (f^[t] (x j)) < ε) ∧
      ∀ i j, f (x i) = f (x j) := by
  obtain ⟨C, _, hC, hcover⟩ := (isCompact_univ : IsCompact (univ : Set X)).finite_cover_balls
    (show 0 < ε / 3 by positivity)
  obtain ⟨c, hc⟩ : ∃ c ∈ C, (Metric.ball c (ε / 3) ∩ f ⁻¹' {z}).Infinite := by
    by_contra! h
    apply hz
    apply (hC.biUnion h).subset
    intro y hy
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp (hcover (mem_univ y))
    exact mem_iUnion₂.mpr ⟨c, hc, hyc, hy⟩
  have hm : (m : ℕ∞) ≤ (Metric.ball c (ε / 3) ∩ f ⁻¹' {z}).encard := by
    rw [hc.2.encard_eq]
    exact le_top
  obtain ⟨x, hx, hxi⟩ := (Set.le_encard_iff_exists_fin_injective _ _).mp hm
  have hterm (i j : Fin m) : f (x i) = f (x j) := (hx i).2.trans (hx j).2.symm
  refine ⟨x, hxi, fun i j t => ?_, hterm⟩
  apply mem_forwardBowen_of_terminal_eq hε (T := 1)
    (by simpa only [Function.iterate_one] using hterm i j) _ t
  intro s hs
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · have hi : dist (x i) c < ε / 3 := (hx i).1
    have hj : dist c (x j) < ε / 3 := by
      rw [dist_comm]
      exact (hx j).1
    simpa only [Function.iterate_zero_apply] using
      (show dist (x i) (x j) < ε by linarith [dist_triangle (x i) c (x j)])
  · simpa only [Function.iterate_one, hterm i j, dist_self] using hε

/-- At every positive scale and for every finite cardinality there are distinct
points strictly close at all forward times, with a common terminal time. -/
theorem coalescing_witnesses (P : PendantArc X) (hf : Continuous f)
    (hex : TopologicallyExact f) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ T : ℕ, ∃ x : Fin m → X, Injective x ∧
      (∀ i j t, dist (f^[t] (x i)) (f^[t] (x j)) < ε) ∧
      ∀ i j, f^[T] (x i) = f^[T] (x j) := by
  by_cases hfin : ∀ z : X, (f ⁻¹' {z}).Finite
  · have hfib (r : ℕ) : ((f^[r]) ⁻¹' {P.leaf}).Finite := by
      simpa only [univ_inter] using finite_iterate_fibres (mapsTo_univ f univ)
        (fun z => by simpa only [univ_inter] using hfin z) r P.leaf
    obtain ⟨T, x, hxi, _, hclose, hterm⟩ := local_coalescing_witnesses
      P hf hex hfib hε m le_rfl zero_lt_one le_rfl
    let e := Fin.castLEEmb m.lt_two_pow_self.le
    exact ⟨T, x ∘ e, hxi.comp e.injective, fun i j => hclose (e i) (e j),
      fun i j => hterm (e i) (e j)⟩
  · push Not at hfin
    obtain ⟨z, hz⟩ := hfin
    obtain ⟨x, hxi, hclose, hterm⟩ := witnesses_of_infinite_fibre hz hε m
    exact ⟨1, x, hxi, hclose, by simpa only [Function.iterate_one] using hterm⟩

/-- Exact selfmaps of compact metric spaces with a pendant arc fail finite positive expansivity. -/
theorem not_finitelyPositiveExpansive (P : PendantArc X) (hf : Continuous f)
    (hex : TopologicallyExact f) : ¬ FinitelyPositiveExpansive f := by
  rintro ⟨ε, hε, N, _, hB⟩
  obtain ⟨C, hC⟩ := uniform_fibre_bound isCompact_univ hB hε
  have hfib (r : ℕ) : ((f^[r]) ⁻¹' {P.leaf}).Finite := by
    have h := uniform_iterate_fibre_bound (mapsTo_univ f univ) hC r P.leaf
    exact finite_of_encard_le_coe (by simpa only [univ_inter] using h)
  obtain ⟨T, x, hxi, _, hclose, hterm⟩ := local_coalescing_witnesses
    P hf hex hfib hε N le_rfl zero_lt_one le_rfl
  exact no_coalescing_witnesses hB hε N.lt_two_pow_self x hxi (fun _ => mem_univ _)
    (fun i j t _ => hclose i j t) hterm

end ExactPendantObstruction

end D5.S1.Dynamics.Shadowing
