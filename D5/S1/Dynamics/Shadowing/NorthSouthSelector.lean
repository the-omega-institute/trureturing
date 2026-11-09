/- GID: D5/S1/Dynamics/Shadowing/NorthSouthSelector
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/NorthSouthSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.LocallyFinite]
   utility: none
   digest: Full closed integer crossing selectors for literal pointwise north-south dynamics. -/

import D5.S1.Dynamics.Shadowing.NorthSouthOrbitClock
import D5.S1.Dynamics.Shadowing.LocalEquiconnection

/-! Compact separation and finite closed pasting retain the entire original domain. -/

noncomputable section
open Set Filter Function Topology

namespace D5.S1.Dynamics.Shadowing.PointwiseNorthSouth

open VerticalSuspensionSelector (LocalEquiconnection Crossing ForwardSign nonnegative_after
  positive_after negative_before crossing_classification crossing_separation crossing_local_range)

variable {M : Type*} [MetricSpace M] [CompactSpace M] {f : M ≃ₜ M} {N S : M}

private theorem open_forall_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] {V : Set (X × Y)} (hV : IsOpen V) :
    IsOpen {x | ∀ y, (x, y) ∈ V} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨A, B, hA, hB, hxA, hYB, hAB⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := x)) isCompact_univ hV (by
      rintro ⟨z, y⟩ ⟨hz, hy⟩
      have hz' : z = x := hz
      simpa only [hz'] using hx y)
  exact ⟨A, fun z hz y => hAB ⟨hz, hYB (mem_univ y)⟩, hA, hxA (mem_singleton x)⟩

private theorem height_positive (h : Pointwise f N S) (v : StrictHeight f N S)
    (p : M) (hp : 0 ≤ v.value p) : 0 < v.value (f p) := by
  by_cases hpN : p = N
  · subst p
    rw [v.north] at hp
    linarith
  by_cases hpS : p = S
  · subst p
    rw [h.south_fixed, v.south]
    norm_num
  exact lt_of_le_of_lt hp (v.strict p hpN hpS)

private structure ControlledCrossing (H : LocalEquiconnection M) (v : M → ℝ)
    (β : ℝ) (p q : M) : Prop where
  pair : (p, f.symm q) ∈ H.domain
  band : ∀ s : Icc (0 : ℝ) 1,
    |v (H.connect (⟨(p, f.symm q), pair⟩, s))| < β

private theorem crossing_tolerance (h : Pointwise f N S) (v : StrictHeight f N S)
    (H : LocalEquiconnection M) :
    ∃ δ > 0, ∃ β ∈ Ioo (0 : ℝ) 1, ∃ κ > 0,
      ∀ p q, dist q (f p) ≤ δ →
        (0 ≤ v.value p → 0 < v.value q) ∧
        (v.value p ≤ 0 → 0 ≤ v.value q →
          ControlledCrossing (f := f) H v.value β p q ∧ κ ≤ v.value q - v.value p) := by
  classical
  let C : Set M := {p | v.value p ≤ 0 ∧ 0 ≤ v.value (f p)}
  have hC : IsCompact C := ((isClosed_le v.continuous_value continuous_const).inter
    (isClosed_le continuous_const (v.continuous_value.comp f.continuous))).isCompact
  obtain ⟨a, ha, hgap⟩ := hC.exists_forall_le' (f := fun p => (1 : ℝ) - |v.value p|)
    (continuous_const.sub v.continuous_value.abs).continuousOn (a := (0 : ℝ)) (by
      intro p hp
      have hpN : p ≠ N := by
        intro hh
        have hh' := hp.2
        rw [hh, h.north_fixed, v.north] at hh'
        linarith
      have hpS : p ≠ S := by
        intro hh
        have hh' := hp.1
        rw [hh, v.south] at hh'
        linarith
      have hl : -1 < v.value p := lt_of_le_of_ne (v.range p).1 (by
        intro hh
        exact hpN ((v.eq_north p).mp hh.symm))
      have hu : v.value p < 1 := lt_of_le_of_ne (v.range p).2 (by
        intro hh
        exact hpS ((v.eq_south p).mp hh))
      linarith [abs_lt.mpr (show -1 < v.value p ∧ v.value p < 1 from ⟨hl, hu⟩)])
  let β : ℝ := 1 - min a 1 / 2
  have hβ0 : 0 < β := by dsimp [β]; linarith [min_le_right a 1]
  have hβ1 : β < 1 := by dsimp [β]; have := lt_min ha (by norm_num : (0 : ℝ) < 1); linarith
  have hCβ (p : M) (hp : p ∈ C) : |v.value p| < β := by
    have := hgap p hp
    have := min_le_left a (1 : ℝ)
    have hh := lt_min ha (by norm_num : (0 : ℝ) < 1)
    dsimp [β]
    linarith
  let W : Set (M × M) := {p | (p.1, f.symm p.2) ∈ H.domain}
  have hW : IsOpen W := H.isOpen_domain.preimage
    (continuous_fst.prodMk (f.symm.continuous.comp continuous_snd))
  let pull : W → H.domain := fun p => ⟨(p.1.1, f.symm p.1.2), p.2⟩
  have hpull : Continuous pull :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (f.symm.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  let A : W × Icc (0 : ℝ) 1 → M := fun z => H.connect (pull z.1, z.2)
  have hA : Continuous A := H.continuous_connect.comp
    ((hpull.comp continuous_fst).prodMk continuous_snd)
  let B : Set W := {p | ∀ s : Icc (0 : ℝ) 1, |v.value (A (p, s))| < β}
  have hB : IsOpen B := open_forall_compact
    (isOpen_lt (v.continuous_value.comp hA |>.abs) continuous_const)
  let O : Set (M × M) := Subtype.val '' B
  have hO : IsOpen O := hW.isOpenMap_subtype_val B hB
  have hOcontrol (p q : M) (hpq : (p, q) ∈ O) :
      ControlledCrossing (f := f) H v.value β p q := by
    obtain ⟨z, hz, he⟩ := hpq
    have hzW : (p, f.symm q) ∈ H.domain := by
      have hh := z.2
      rw [he] at hh
      exact hh
    refine ⟨hzW, ?_⟩
    intro s
    have hh := hz s
    simpa only [A, pull, he] using hh
  have hgraphO (p : M) (hp : p ∈ C) : (p, f p) ∈ O := by
    have hpW : (p, f p) ∈ W := by
      change (p, f.symm (f p)) ∈ H.domain
      rw [f.symm_apply_apply]
      exact H.diagonal p
    refine ⟨⟨(p, f p), hpW⟩, ?_, rfl⟩
    intro s
    have hdiag : pull ⟨(p, f p), hpW⟩ = ⟨(p, p), H.diagonal p⟩ := by
      apply Subtype.ext
      simp only [pull, f.symm_apply_apply]
    change |v.value (H.connect (pull ⟨(p, f p), hpW⟩, s))| < β
    rw [hdiag, H.refl]
    exact hCβ p hp
  let G : Set (M × M) := {p |
    (v.value p.1 < 0 ∨ 0 < v.value p.2) ∧
    (0 < v.value p.1 ∨ v.value p.2 < 0 ∨ p ∈ O)}
  have hc1 := v.continuous_value.comp (continuous_fst : Continuous (Prod.fst : M × M → M))
  have hc2 := v.continuous_value.comp (continuous_snd : Continuous (Prod.snd : M × M → M))
  have hG : IsOpen G :=
    ((isOpen_lt hc1 continuous_const).union (isOpen_lt continuous_const hc2)).inter
      ((isOpen_lt continuous_const hc1).union ((isOpen_lt hc2 continuous_const).union hO))
  have hgraph (p : M) : (p, f p) ∈ G := by
    constructor
    · rcases lt_or_ge (v.value p) 0 with hp | hp
      · exact Or.inl hp
      · exact Or.inr (height_positive h v p hp)
    · rcases lt_or_ge 0 (v.value p) with hp | hp
      · exact Or.inl hp
      right
      rcases lt_or_ge (v.value (f p)) 0 with hfp | hfp
      · exact Or.inl hfp
      · exact Or.inr (hgraphO p ⟨hp, hfp⟩)
  have herr : Continuous (fun p : M × M => dist p.2 (f p.1)) :=
    continuous_snd.dist (f.continuous.comp continuous_fst)
  obtain ⟨ε, hε, hεbound⟩ := hG.isClosed_compl.isCompact.exists_forall_le'
    herr.continuousOn (a := (0 : ℝ)) (by
      intro p hp
      apply dist_pos.mpr
      intro he
      apply hp
      have he' : (p.1, f p.1) = p := Prod.ext rfl he.symm
      exact he' ▸ hgraph p.1)
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hgood (p q : M) (hpq : dist q (f p) ≤ δ) : (p, q) ∈ G := by
    by_contra hh
    have := hεbound (p, q) hh
    dsimp [δ] at hpq
    linarith
  let E : Set (M × M) := {p | dist p.2 (f p.1) ≤ δ ∧ v.value p.1 ≤ 0 ∧ 0 ≤ v.value p.2}
  have hE : IsCompact E := ((isClosed_le herr continuous_const).inter
    ((isClosed_le hc1 continuous_const).inter (isClosed_le continuous_const hc2))).isCompact
  obtain ⟨κ, hκ, hκbound⟩ := hE.exists_forall_le' (hc2.sub hc1).continuousOn (a := (0 : ℝ)) (by
    intro p hp
    have hg := hgood p.1 p.2 hp.1
    change 0 < v.value p.2 - v.value p.1
    have hpneg : v.value p.1 ≤ 0 := hp.2.1
    have hppos : 0 ≤ v.value p.2 := hp.2.2
    rcases hg.1 with hn | hs
    · linarith
    · linarith)
  refine ⟨δ, hδ, β, ⟨hβ0, hβ1⟩, κ, hκ, fun p q hpq => ?_⟩
  have hg := hgood p q hpq
  constructor
  · intro hp
    rcases hg.1 with hn | hs
    · linarith
    · exact hs
  · intro hp hq
    refine ⟨hOcontrol p q ?_, hκbound (p, q) ⟨hpq, hp, hq⟩⟩
    rcases hg.2 with hpos | hneg | ho
    · linarith
    · linarith
    · exact ho

private structure Control (v : StrictHeight f N S) (H : LocalEquiconnection M) where
  delta : ℝ
  delta_pos : 0 < delta
  beta : ℝ
  beta_mem : beta ∈ Ioo (0 : ℝ) 1
  kappa : ℝ
  kappa_pos : 0 < kappa
  good : ∀ p q, dist q (f p) ≤ delta →
    (0 ≤ v.value p → 0 < v.value q) ∧
    (v.value p ≤ 0 → 0 ≤ v.value q →
      ControlledCrossing (f := f) H v.value beta p q ∧ kappa ≤ v.value q - v.value p)

variable {v : StrictHeight f N S} {H : LocalEquiconnection M}

private abbrev History (c : Control v H) := CompactSelector.Space f c.delta

private def heights (c : Control v H) (x : History c) (j : ℤ) : ℝ := v.value (x.1 j)

private theorem sign_rule (c : Control v H) (x : History c) : ForwardSign (heights c x) :=
  fun j hj => (c.good _ _ (x.2 j)).1 hj

private theorem crossing_control (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) :
    ControlledCrossing (f := f) H v.value c.beta (x.1 j) (x.1 (j + 1)) ∧
      c.kappa ≤ heights c x (j + 1) - heights c x j :=
  (c.good _ _ (x.2 j)).2 hj.1 hj.2

private def fraction (c : Control v H) (x : History c) (j : ℤ) : ℝ :=
  -heights c x j / (heights c x (j + 1) - heights c x j)

private theorem denominator_pos (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) : 0 < heights c x (j + 1) - heights c x j :=
  c.kappa_pos.trans_le (crossing_control c x j hj).2

private theorem fraction_mem (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) : fraction c x j ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (neg_nonneg.mpr hj.1) (denominator_pos c x j hj).le
  · apply (div_le_iff₀ (denominator_pos c x j hj)).mpr
    linarith [hj.2]

private def anchor (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) : M :=
  H.connect (⟨(x.1 j, f.symm (x.1 (j + 1))), (crossing_control c x j hj).1.pair⟩,
    ⟨fraction c x j, fraction_mem c x j hj⟩)

private def chart (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) : M := (f ^ (-j)) (anchor c x j hj)

private theorem anchor_band (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) : |v.value (anchor c x j hj)| ≤ c.beta :=
  ((crossing_control c x j hj).1.band _).le

private theorem chart_adjacent (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) (hj' : Crossing (heights c x) (j + 1))
    (hz : heights c x (j + 1) = 0) : chart c x j hj = chart c x (j + 1) hj' := by
  have hs : fraction c x j = 1 := by
    dsimp [fraction]
    apply (div_eq_one_iff_eq (ne_of_gt (denominator_pos c x j hj))).mpr
    rw [hz]
    ring
  have hs' : fraction c x (j + 1) = 0 := by simp [fraction, hz]
  have ha : anchor c x j hj = f.symm (x.1 (j + 1)) := by
    unfold anchor
    have he : (⟨fraction c x j, fraction_mem c x j hj⟩ : Icc (0 : ℝ) 1) =
        ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hs
    rw [he, H.right]
  have ha' : anchor c x (j + 1) hj' = x.1 (j + 1) := by
    unfold anchor
    have he : (⟨fraction c x (j + 1), fraction_mem c x (j + 1) hj'⟩ : Icc (0 : ℝ) 1) =
        ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hs'
    rw [he, H.left]
  unfold chart
  rw [ha, ha']
  have hf : f.symm = f ^ (-1 : ℤ) := by rw [zpow_neg_one]; rfl
  rw [hf, ← Homeomorph.mul_apply, ← zpow_add]
  congr 2
  omega

private theorem chart_independent (c : Control v H) (x : History c) (i j : ℤ)
    (hi : Crossing (heights c x) i) (hj : Crossing (heights c x) j) :
    chart c x i hi = chart c x j hj := by
  rcases crossing_separation (sign_rule c x) hi hj with he | ⟨he, hz⟩ | ⟨he, hz⟩
  · subst j; rfl
  · subst j; exact chart_adjacent c x i hi hj hz
  · subst i; exact (chart_adjacent c x j hj hi hz).symm

private def selector (c : Control v H) (x : History c) : M := by
  classical
  exact if hx : ∃ j, Crossing (heights c x) j then chart c x hx.choose hx.choose_spec
    else if ∀ j, heights c x j < 0 then N else S

private theorem selector_at_crossing (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) : selector c x = chart c x j hj := by
  classical
  unfold selector
  rw [dif_pos ⟨j, hj⟩]
  exact chart_independent _ _ _ _ _ _

private theorem selector_negative (c : Control v H) (x : History c)
    (hx : ∀ j, heights c x j < 0) : selector c x = N := by
  classical
  have hn : ¬ ∃ j, Crossing (heights c x) j := by
    rintro ⟨j, hj⟩
    linarith [hx (j + 1), hj.2]
  simp only [selector, dif_neg hn, if_pos hx]

private theorem selector_positive (c : Control v H) (x : History c)
    (hx : ∀ j, 0 < heights c x j) : selector c x = S := by
  classical
  have hn : ¬ ∃ j, Crossing (heights c x) j := by
    rintro ⟨j, hj⟩
    linarith [hx j, hj.1]
  have hnn : ¬ ∀ j, heights c x j < 0 := by
    intro hh
    linarith [hx 0, hh 0]
  simp only [selector, dif_neg hn, if_neg hnn]

private theorem continuous_heights (c : Control v H) (j : ℤ) :
    Continuous (fun x : History c => heights c x j) :=
  v.continuous_value.comp ((continuous_apply j).comp continuous_subtype_val)

private abbrev Chart (c : Control v H) (j : ℤ) :=
  {x : History c // Crossing (heights c x) j}

private theorem continuous_chart (c : Control v H) (j : ℤ) :
    Continuous (fun x : Chart c j => chart c x.1 j x.2) := by
  have hev (i : ℤ) : Continuous (fun x : Chart c j => x.1.1 i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hvv (i : ℤ) := v.continuous_value.comp (hev i)
  have hfrac : Continuous (fun x : Chart c j => fraction c x.1 j) :=
    (hvv j).neg.div ((hvv (j + 1)).sub (hvv j))
      (fun x => ne_of_gt (denominator_pos c x.1 j x.2))
  have hpair : Continuous (fun x : Chart c j =>
      (⟨(x.1.1 j, f.symm (x.1.1 (j + 1))), (crossing_control c x.1 j x.2).1.pair⟩ : H.domain)) :=
    ((hev j).prodMk (f.symm.continuous.comp (hev (j + 1)))).subtype_mk _
  exact (f ^ (-j)).continuous.comp (H.continuous_connect.comp
    (hpair.prodMk (hfrac.subtype_mk _)))

private theorem continuousAt_crossing (c : Control v H) (x : History c) (j : ℤ)
    (hj : Crossing (heights c x) j) : ContinuousAt (selector c) x := by
  classical
  let U : Set (History c) := {y | heights c y (j - 1) < 0 ∧ 0 < heights c y (j + 2)}
  have hU : IsOpen U :=
    (isOpen_lt (continuous_heights c _) continuous_const).inter
      (isOpen_lt continuous_const (continuous_heights c _))
  have hx : x ∈ U := ⟨negative_before (sign_rule c x) (by omega) hj.1,
    positive_after (sign_rule c x) (by omega) hj.2⟩
  let C : Icc (j - 1) (j + 1) → Set U := fun k => {y | Crossing (heights c y.1) k}
  have hcover : (⋃ k, C k) = univ := by
    apply eq_univ_of_forall
    intro y
    rcases crossing_classification (sign_rule c y.1) with hn | hp | ⟨k, hk⟩
    · exact (not_lt_of_ge (hn (j + 2)).le y.2.2).elim
    · exact (not_lt_of_ge (hp (j - 1)).le y.2.1).elim
    · have hb := crossing_local_range (sign_rule c y.1) y.2.1 y.2.2 hk
      exact mem_iUnion.mpr ⟨⟨k, hb.1, by omega⟩, hk⟩
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    exact (isClosed_le ((continuous_heights c k).comp continuous_subtype_val)
      continuous_const).inter (isClosed_le continuous_const
        ((continuous_heights c (k + 1)).comp continuous_subtype_val))
  have hcontinuous : ∀ k, ContinuousOn (fun y : U => selector c y.1) (C k) := by
    intro k
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hm : Continuous (fun y : C k => (⟨y.1.1, y.2⟩ : Chart c k)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    apply ((continuous_chart c k).comp hm).congr
    intro y
    exact (selector_at_crossing c y.1.1 k y.2).symm
  have hc : Continuous (fun y : U => selector c y.1) :=
    (locallyFinite_of_finite C).continuous hcover hclosed hcontinuous
  exact (continuousOn_iff_continuous_domRestrict.mpr hc x hx).continuousAt (hU.mem_nhds hx)

private def anchorBand (c : Control v H) : Set M := {p | |v.value p| ≤ c.beta}

private theorem compact_anchorBand (c : Control v H) : IsCompact (anchorBand c) :=
  (isClosed_le v.continuous_value.abs continuous_const).isCompact

private theorem north_not_anchorBand (c : Control v H) : N ∉ anchorBand c := by
  intro hh
  have hh' : |v.value N| ≤ c.beta := hh
  rw [v.north, abs_neg, abs_one] at hh'
  linarith [c.beta_mem.2]

private theorem south_not_anchorBand (c : Control v H) : S ∉ anchorBand c := by
  intro hh
  have hh' : |v.value S| ≤ c.beta := hh
  rw [v.south, abs_one] at hh'
  linarith [c.beta_mem.2]

private theorem continuousAt_negative (h : Pointwise f N S) (c : Control v H) (x : History c)
    (hx : ∀ j, heights c x j < 0) : ContinuousAt (selector c) x := by
  rw [ContinuousAt, selector_negative c x hx]
  apply tendsto_nhds.mpr
  intro O hO hN
  obtain ⟨T, hT⟩ := (stability_and_compact_uniformity h).2.2.2
    (anchorBand c) (compact_anchorBand c) (south_not_anchorBand c) O (hO.mem_nhds hN)
  have hnb : ∀ᶠ y in 𝓝 x, heights c y (T : ℤ) < 0 :=
    (isOpen_lt (continuous_heights c _) continuous_const).mem_nhds (hx _)
  apply hnb.mono
  intro y hy
  rcases crossing_classification (sign_rule c y) with hn | hp | ⟨j, hj⟩
  · simpa only [selector_negative c y hn] using hN
  · exact (not_lt_of_ge (hp T).le hy).elim
  · rw [selector_at_crossing c y j hj]
    have hjT : (T : ℤ) ≤ j := by
      by_contra hh
      have hh' := nonnegative_after (sign_rule c y) (show j + 1 ≤ (T : ℤ) by omega) hj.2
      linarith
    have hj0 : 0 ≤ j := by omega
    have hjnat : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
    have he : f ^ (-j) = f.symm ^ j.toNat := by
      rw [← hjnat, zpow_neg, zpow_natCast]
      exact (inv_pow f _).symm
    unfold chart
    rw [he]
    exact hT j.toNat (by omega) ⟨anchor c y j hj, anchor_band c y j hj, rfl⟩

private theorem continuousAt_positive (h : Pointwise f N S) (c : Control v H) (x : History c)
    (hx : ∀ j, 0 < heights c x j) : ContinuousAt (selector c) x := by
  rw [ContinuousAt, selector_positive c x hx]
  apply tendsto_nhds.mpr
  intro O hO hS
  obtain ⟨T, hT⟩ := (stability_and_compact_uniformity h).2.2.1
    (anchorBand c) (compact_anchorBand c) (north_not_anchorBand c) O (hO.mem_nhds hS)
  have hnb : ∀ᶠ y in 𝓝 x, 0 < heights c y (-(T : ℤ)) :=
    (isOpen_lt continuous_const (continuous_heights c _)).mem_nhds (hx _)
  apply hnb.mono
  intro y hy
  rcases crossing_classification (sign_rule c y) with hn | hp | ⟨j, hj⟩
  · exact (not_lt_of_ge (hn (-(T : ℤ))).le hy).elim
  · simpa only [selector_positive c y hp] using hS
  · rw [selector_at_crossing c y j hj]
    have hjT : j < -(T : ℤ) := by
      by_contra hh
      rcases eq_or_lt_of_le (le_of_not_gt hh) with he | he
      · have hh' : 0 < heights c y j := he ▸ hy
        linarith [hj.1]
      · have hh' := positive_after (sign_rule c y) he hy.le
        linarith [hj.1]
    have hjnat : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
    unfold chart
    rw [← hjnat, zpow_natCast]
    exact hT (-j).toNat (by omega) ⟨anchor c y j hj, anchor_band c y j hj, rfl⟩

private theorem continuous_selector (h : Pointwise f N S) (c : Control v H) :
    Continuous (selector c) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases crossing_classification (sign_rule c x) with hn | hp | ⟨j, hj⟩
  · exact continuousAt_negative h c x hn
  · exact continuousAt_positive h c x hp
  · exact continuousAt_crossing c x j hj

private theorem selector_orbit (h : Pointwise f N S) (c : Control v H) (p : M) :
    selector c (CompactSelector.trueOrbit f c.delta_pos.le p) = p := by
  let x := CompactSelector.trueOrbit f c.delta_pos.le p
  by_cases hpN : p = N
  · subst p
    apply selector_negative c x
    intro j
    change v.value ((f ^ j) N) < 0
    rw [zpow_fixed h.north_fixed, v.north]
    norm_num
  by_cases hpS : p = S
  · subst p
    apply selector_positive c x
    intro j
    change 0 < v.value ((f ^ j) S)
    rw [zpow_fixed h.south_fixed, v.south]
    norm_num
  have hforward : Tendsto (fun n : ℕ => heights c x (n : ℤ)) atTop (𝓝 (1 : ℝ)) := by
    have hh := v.continuous_value.continuousAt.tendsto.comp (h.forward p hpN hpS)
    change Tendsto (fun n : ℕ => v.value ((f ^ (n : ℤ)) p)) atTop (𝓝 (1 : ℝ))
    simp only [zpow_natCast]
    simpa only [Function.comp_def, v.south] using hh
  have hbackward : Tendsto (fun n : ℕ => heights c x (-(n : ℤ))) atTop (𝓝 (-1 : ℝ)) := by
    have hh := v.continuous_value.continuousAt.tendsto.comp (h.backward p hpN hpS)
    have he (n : ℕ) : f ^ (-(n : ℤ)) = f.symm ^ n := by
      rw [zpow_neg, zpow_natCast]
      exact (inv_pow f n).symm
    change Tendsto (fun n : ℕ => v.value ((f ^ (-(n : ℤ))) p)) atTop (𝓝 (-1 : ℝ))
    simp only [he]
    simpa only [Function.comp_def, v.north] using hh
  have hc : ∃ j, Crossing (heights c x) j := by
    rcases crossing_classification (sign_rule c x) with hn | hp | hx
    · have hh : (1 : ℝ) ≤ 0 := le_of_tendsto hforward (Eventually.of_forall fun n => (hn n).le)
      norm_num at hh
    · have hh : (0 : ℝ) ≤ -1 := ge_of_tendsto hbackward (Eventually.of_forall fun n => (hp (-n)).le)
      norm_num at hh
    · exact hx
  obtain ⟨j, hj⟩ := hc
  rw [selector_at_crossing c x j hj]
  have he : f.symm (x.1 (j + 1)) = x.1 j := by
    change f.symm (CompactSelector.orbit f p (j + 1)) = CompactSelector.orbit f p j
    rw [CompactSelector.orbit_step, f.symm_apply_apply]
  have ha : anchor c x j hj = x.1 j := by
    have hdiag : (⟨(x.1 j, f.symm (x.1 (j + 1))),
        (crossing_control c x j hj).1.pair⟩ : H.domain) =
        ⟨(x.1 j, x.1 j), H.diagonal (x.1 j)⟩ := Subtype.ext (by simp only [he])
    unfold anchor
    rw [hdiag, H.refl]
  unfold chart
  rw [ha]
  change (f ^ (-j)) ((f ^ j) p) = p
  rw [← Homeomorph.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Homeomorph.one_apply]

private theorem selector_shift (h : Pointwise f N S) (c : Control v H) (k : ℤ) (x : History c) :
    selector c (CompactSelector.shift f k x) = (f ^ k) (selector c x) := by
  let y := CompactSelector.shift f k x
  have hv (i : ℤ) : heights c y i = heights c x (k + i) := rfl
  rcases crossing_classification (sign_rule c x) with hn | hp | ⟨j, hj⟩
  · have hy : ∀ i, heights c y i < 0 := fun i => hn (k + i)
    rw [selector_negative c y hy, selector_negative c x hn, zpow_fixed h.north_fixed]
  · have hy : ∀ i, 0 < heights c y i := fun i => hp (k + i)
    rw [selector_positive c y hy, selector_positive c x hp, zpow_fixed h.south_fixed]
  · have heA : k + (j - k) = j := by omega
    have heB : k + (j - k + 1) = j + 1 := by omega
    have hj' : Crossing (heights c y) (j - k) := by
      simp only [Crossing, hv, heA, heB]
      exact hj
    have hs : fraction c y (j - k) = fraction c x j := by
      simp only [fraction, hv, heA, heB]
    have ha : anchor c y (j - k) hj' = anchor c x j hj := by
      simp only [anchor, y, CompactSelector.shift_apply, heA, heB, hs]
    rw [selector_at_crossing c y (j - k) hj', selector_at_crossing c x j hj]
    unfold chart
    rw [ha, ← Homeomorph.mul_apply, ← zpow_add]
    congr 2
    omega

/-- A continuous retraction of the true-orbit embedding on one entire closed
all-integer pseudoorbit domain, equivariant for every integer shift. -/
theorem pointwise_north_south_selector (h : Pointwise f N S) (H : LocalEquiconnection M) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ Q : CompactSelector.Space f δ → M,
      Continuous Q ∧
      (∀ p, Q (CompactSelector.trueOrbit f hδ.le p) = p) ∧
      ∀ (k : ℤ) (x : CompactSelector.Space f δ),
        Q (CompactSelector.shift f k x) = (f ^ k) (Q x) := by
  obtain ⟨v⟩ := exists_strictHeight h
  obtain ⟨δ, hδ, β, hβ, κ, hκ, hg⟩ := crossing_tolerance h v H
  let c : Control v H := ⟨δ, hδ, β, hβ, κ, hκ, hg⟩
  exact ⟨δ, hδ, selector c, continuous_selector h c, selector_orbit h c,
    selector_shift h c⟩

#print axioms pointwise_north_south_selector

end D5.S1.Dynamics.Shadowing.PointwiseNorthSouth
