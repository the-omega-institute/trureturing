import D5.S1.Dynamics.Shadowing.IntervalObstruction.Basic

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing

namespace IntervalObstruction

section StrictTurns

variable {G : ℝ → ℝ}

/-- A finite extremal fibre isolates a genuine strict local maximum. -/
theorem strict_peak_of_equal_endpoints (A : Segment)
    (hG : ContinuousOn G (A : Set ℝ))
    (hfib : ∀ z, ((A : Set ℝ) ∩ G ⁻¹' {z}).Finite)
    {u v w : ℝ} (hu : u ∈ (A : Set ℝ)) (hv : v ∈ (A : Set ℝ))
    (huv : u < v) (hGuGv : G u = G v) (hw : w ∈ Icc u v) (hGw : G u < G w) :
    ∃ c ∈ Ioo u v, ∃ δ > 0,
      ∀ y : ℝ, dist y c < δ → y ≠ c → G y < G c := by
  have hsub : Icc u v ⊆ (A : Set ℝ) := Icc_subset_Icc hu.1 hv.2
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr huv.le) (hG.mono hsub)
  have hwc : G w ≤ G c := isMaxOn_iff.mp hmax w hw
  have huc : u < c := by
    rcases eq_or_lt_of_le hc.1 with he | he
    · subst c
      linarith
    · exact he
  have hcv : c < v := by
    rcases eq_or_lt_of_le hc.2 with he | he
    · subst c
      linarith
    · exact he
  let R := ((A : Set ℝ) ∩ G ⁻¹' {G c}) \ {c}
  have hR : R.Finite := (hfib (G c)).sdiff
  have hcR : c ∉ R := by simp [R]
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (hR.isClosed.compl_mem_nhds hcR)
  let γ := min δ (min (c - u) (v - c))
  have hγ : 0 < γ := lt_min hδ (lt_min (sub_pos.mpr huc) (sub_pos.mpr hcv))
  refine ⟨c, ⟨huc, hcv⟩, γ, hγ, ?_⟩
  intro y hy hne
  have hdist := (abs_lt.mp (show |y - c| < γ by simpa only [Real.dist_eq] using hy))
  have hγu : γ ≤ c - u := (min_le_right δ _).trans (min_le_left _ _)
  have hγv : γ ≤ v - c := (min_le_right δ _).trans (min_le_right _ _)
  have hyuv : y ∈ Icc u v := by constructor <;> linarith [hdist.1, hdist.2]
  have hyle : G y ≤ G c := isMaxOn_iff.mp hmax y hyuv
  have hyR : y ∉ R := hd (hy.trans_le (min_le_left _ _))
  have hval : G y ≠ G c := by
    intro he
    exact hyR ⟨⟨hsub hyuv, he⟩, hne⟩
  exact lt_of_le_of_ne hyle hval

/-- Noninjectivity plus actual finite fibres gives an interior strict turn,
with no weak-fold or piecewise-monotonicity assumption. -/
theorem strict_turn (A : Segment) (hG : ContinuousOn G (A : Set ℝ))
    (hfib : ∀ z, ((A : Set ℝ) ∩ G ⁻¹' {z}).Finite)
    (hni : ¬InjOn G (A : Set ℝ)) :
    ∃ c ∈ Ioo A.left A.right, ∃ δ > 0,
      (∀ y : ℝ, dist y c < δ → y ≠ c → G y < G c) ∨
      (∀ y : ℝ, dist y c < δ → y ≠ c → G c < G y) := by
  classical
  have huv : ∃ u ∈ (A : Set ℝ), ∃ v ∈ (A : Set ℝ), u < v ∧ G u = G v := by
    simp only [Set.InjOn] at hni
    push_neg at hni
    obtain ⟨x, hx, y, hy, he, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · exact ⟨x, hx, y, hy, hxy, he⟩
    · exact ⟨y, hy, x, hx, hyx, he.symm⟩
  obtain ⟨u, hu, v, hv, huv, he⟩ := huv
  have hsub : Icc u v ⊆ (A : Set ℝ) := Icc_subset_Icc hu.1 hv.2
  have hw : ∃ w ∈ Icc u v, G w ≠ G u := by
    by_contra! hc
    apply Icc_infinite huv
    apply (hfib (G u)).subset
    intro w hw
    exact ⟨hsub hw, hc w hw⟩
  obtain ⟨w, hw, hne⟩ := hw
  rcases lt_or_gt_of_ne hne with hdown | hup
  · have hnfib : ∀ z, ((A : Set ℝ) ∩ (fun x => -G x) ⁻¹' {z}).Finite := by
      intro z
      apply (hfib (-z)).subset
      intro x hx
      exact ⟨hx.1, by change G x = -z; have he' : -G x = z := hx.2; linarith⟩
    obtain ⟨c, hc, δ, hδ, hd⟩ := strict_peak_of_equal_endpoints A hG.neg hnfib
      hu hv huv (by change -G u = -G v; rw [he]) hw (neg_lt_neg hdown)
    refine ⟨c, ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩, δ, hδ, Or.inr ?_⟩
    intro y hy hne
    exact neg_lt_neg_iff.mp (hd y hy hne)
  · obtain ⟨c, hc, δ, hδ, hd⟩ := strict_peak_of_equal_endpoints A hG hfib hu hv huv he hw hup
    exact ⟨c, ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩, δ, hδ, Or.inl hd⟩

/-- A strict peak on two sides gives two disjoint exact common-image intervals. -/
theorem disjoint_fold_of_peak {u c v : ℝ} (huc : u < c) (hcv : c < v)
    (hG : ContinuousOn G (Icc u v)) (hu : G u < G c) (hv : G v < G c) :
    ∃ L R D : Segment, (L : Set ℝ) ⊆ Icc u c ∧ (R : Set ℝ) ⊆ Icc c v ∧
      Disjoint (L : Set ℝ) (R : Set ℝ) ∧
      G '' (L : Set ℝ) = (D : Set ℝ) ∧ G '' (R : Set ℝ) = (D : Set ℝ) := by
  obtain ⟨α, hα, hαc⟩ := exists_between (max_lt hu hv)
  obtain ⟨β, hαβ, hβc⟩ := exists_between hαc
  let D : Segment := ⟨α, β, hαβ⟩
  let A₀ : Segment := ⟨u, c, huc⟩
  let A₁ : Segment := ⟨c, v, hcv⟩
  have hD₀ : (D : Set ℝ) ⊆ G '' (A₀ : Set ℝ) := by
    apply subset_trans (b := Icc (G u) (G c))
    · exact Icc_subset_Icc ((le_max_left _ _).trans hα.le) hβc.le
    · exact intermediate_value_Icc huc.le (hG.mono (Icc_subset_Icc le_rfl hcv.le))
  have hD₁ : (D : Set ℝ) ⊆ G '' (A₁ : Set ℝ) := by
    apply subset_trans (b := Icc (G v) (G c))
    · exact Icc_subset_Icc ((le_max_right _ _).trans hα.le) hβc.le
    · exact intermediate_value_Icc' hcv.le (hG.mono (Icc_subset_Icc huc.le le_rfl))
  obtain ⟨L, hL, hGL⟩ := exact_pullback A₀ D
    (hG.mono (Icc_subset_Icc le_rfl hcv.le)) hD₀
  obtain ⟨R, hR, hGR⟩ := exact_pullback A₁ D
    (hG.mono (Icc_subset_Icc huc.le le_rfl)) hD₁
  refine ⟨L, R, D, hL, hR, Set.disjoint_left.mpr ?_, hGL, hGR⟩
  intro x hxL hxR
  have he : x = c := le_antisymm (hL hxL).2 (hR hxR).1
  have hcD : G c ∈ (D : Set ℝ) := by
    rw [← hGL, ← he]
    exact mem_image_of_mem _ hxL
  exact (not_le_of_gt hβc) hcD.2

/-- Negating the target handles a strict trough without changing domain order. -/
theorem disjoint_fold_of_trough {u c v : ℝ} (huc : u < c) (hcv : c < v)
    (hG : ContinuousOn G (Icc u v)) (hu : G c < G u) (hv : G c < G v) :
    ∃ L R D : Segment, (L : Set ℝ) ⊆ Icc u c ∧ (R : Set ℝ) ⊆ Icc c v ∧
      Disjoint (L : Set ℝ) (R : Set ℝ) ∧
      G '' (L : Set ℝ) = (D : Set ℝ) ∧ G '' (R : Set ℝ) = (D : Set ℝ) := by
  obtain ⟨L, R, D, hL, hR, hdis, hGL, hGR⟩ := disjoint_fold_of_peak huc hcv
    hG.neg (neg_lt_neg hu) (neg_lt_neg hv)
  let E : Segment := ⟨-D.right, -D.left, neg_lt_neg D.proper⟩
  have hconvert : ∀ J : Segment, (fun x => -G x) '' (J : Set ℝ) = (D : Set ℝ) →
      G '' (J : Set ℝ) = (E : Set ℝ) := by
    intro J hJ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hn := hJ.subset (mem_image_of_mem (fun x => -G x) hx)
      constructor <;> linarith [hn.1, hn.2]
    · intro hy
      have hn : -y ∈ (D : Set ℝ) := by constructor <;> linarith [hy.1, hy.2]
      obtain ⟨x, hx, he⟩ := hJ.symm.subset hn
      exact ⟨x, hx, by linarith⟩
  exact ⟨L, R, E, hL, hR, hdis, hconvert L hGL, hconvert R hGR⟩

end StrictTurns

section SmallFold

variable {f : ℝ → ℝ} {I : Set ℝ} {ε η : ℝ} {N r : ℕ}

/-- The full fold iterate and every intermediate time, including its last
application of f, are controlled on both selected branches together. -/
theorem small_disjoint_fold (hI : IsCompact I) (hf : ContinuousOn f I)
    (hmap : MapsTo f I I) (hε : 0 < ε) (hB : ForwardBowenBound f I ε N)
    (hη : 0 < η) (A : Segment) (hAI : (A : Set ℝ) ⊆ I)
    (hni : ¬InjOn (f^[r]) (A : Set ℝ)) :
    ∃ L R D : Segment, (L : Set ℝ) ⊆ (A : Set ℝ) ∧
      (R : Set ℝ) ⊆ (A : Set ℝ) ∧ Disjoint (L : Set ℝ) (R : Set ℝ) ∧
      f^[r] '' (L : Set ℝ) = (D : Set ℝ) ∧ f^[r] '' (R : Set ℝ) = (D : Set ℝ) ∧
      ∀ s ≤ r, ∀ x ∈ (L : Set ℝ) ∪ (R : Set ℝ),
        ∀ y ∈ (L : Set ℝ) ∪ (R : Set ℝ), dist (f^[s] x) (f^[s] y) < η := by
  have hfib := finite_fibres hI hB hε
  have hfibr : ∀ z, ((A : Set ℝ) ∩ (f^[r]) ⁻¹' {z}).Finite := by
    intro z
    exact (finite_iterate_fibres hmap hfib r z).subset
      (inter_subset_inter_left _ hAI)
  obtain ⟨c, hc, γ, hγ, hturn⟩ := strict_turn A ((hf.iterate hmap r).mono hAI) hfibr hni
  obtain ⟨δ, hδ, hd⟩ := finite_block_scale hI hf hmap hη (r + 1)
  have hmin : 0 < min (δ / 3) (min γ (min (c - A.left) (A.right - c))) :=
    lt_min (by positivity) (lt_min hγ (lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)))
  obtain ⟨h, hh, hsmall⟩ := exists_between hmin
  have hhδ : h < δ / 3 := hsmall.trans_le (min_le_left _ _)
  have hhγ : h < γ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhl : h < c - A.left := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhr : h < A.right - c := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hbc : c - h < c := by linarith
  have hcb : c < c + h := by linarith
  have hBA : Icc (c - h) (c + h) ⊆ (A : Set ℝ) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hG : ContinuousOn (f^[r]) (Icc (c - h) (c + h)) :=
    (hf.iterate hmap r).mono (hBA.trans hAI)
  have hleft : dist (c - h) c < γ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hright : dist (c + h) c < γ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hfold : ∃ L R D : Segment,
      (L : Set ℝ) ⊆ Icc (c - h) c ∧ (R : Set ℝ) ⊆ Icc c (c + h) ∧
      Disjoint (L : Set ℝ) (R : Set ℝ) ∧
      f^[r] '' (L : Set ℝ) = (D : Set ℝ) ∧ f^[r] '' (R : Set ℝ) = (D : Set ℝ) := by
    rcases hturn with hpeak | htrough
    · exact disjoint_fold_of_peak hbc hcb hG
        (hpeak _ hleft (by linarith)) (hpeak _ hright (by linarith))
    · exact disjoint_fold_of_trough hbc hcb hG
        (htrough _ hleft (by linarith)) (htrough _ hright (by linarith))
  obtain ⟨L, R, D, hL, hR, hdis, hGL, hGR⟩ := hfold
  have hLB : (L : Set ℝ) ⊆ Icc (c - h) (c + h) :=
    hL.trans (Icc_subset_Icc le_rfl hcb.le)
  have hRB : (R : Set ℝ) ⊆ Icc (c - h) (c + h) :=
    hR.trans (Icc_subset_Icc hbc.le le_rfl)
  have hUB : (L : Set ℝ) ∪ (R : Set ℝ) ⊆ Icc (c - h) (c + h) :=
    union_subset hLB hRB
  refine ⟨L, R, D, hLB.trans hBA, hRB.trans hBA, hdis, hGL, hGR, ?_⟩
  intro s hs x hx y hy
  have hxB := hUB hx
  have hyB := hUB hy
  have hxy : dist x y < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hxB.1, hxB.2, hyB.1, hyB.2]
  exact hd s (by omega) x (hAI (hBA hxB)) y (hAI (hBA hyB)) hxy

end SmallFold

/-- An actual family of disjoint compact interval histories, with one common
terminal image and a joint bound at every time up to and including that time. -/
structure HistoryFamily (f : ℝ → ℝ) (I : Set ℝ) (η : ℝ) (ι : Type*) where
  domain : ι → Segment
  inside : ∀ i, (domain i : Set ℝ) ⊆ I
  disjoint : ∀ i j, i ≠ j → Disjoint (domain i : Set ℝ) (domain j : Set ℝ)
  time : ℕ
  terminal : Segment
  onto : ∀ i, f^[time] '' (domain i : Set ℝ) = (terminal : Set ℝ)
  small : ∀ s ≤ time, ∀ i j, ∀ x ∈ (domain i : Set ℝ),
    ∀ y ∈ (domain j : Set ℝ), dist (f^[s] x) (f^[s] y) < η

namespace HistoryFamily

variable {f : ℝ → ℝ} {I : Set ℝ} {η : ℝ} {ι : Type*}

/-- Exact selected pullbacks double the number of disjoint histories while
controlling old times, every transit time, and the terminal fold time. -/
noncomputable def double (H : HistoryFamily f I η ι)
    (hf : ContinuousOn f I) (hmap : MapsTo f I I) {r : ℕ}
    (L R D : Segment) (hL : (L : Set ℝ) ⊆ (H.terminal : Set ℝ))
    (hR : (R : Set ℝ) ⊆ (H.terminal : Set ℝ))
    (hdis : Disjoint (L : Set ℝ) (R : Set ℝ))
    (hGL : f^[r] '' (L : Set ℝ) = (D : Set ℝ))
    (hGR : f^[r] '' (R : Set ℝ) = (D : Set ℝ))
    (hpost : ∀ s ≤ r, ∀ x ∈ (L : Set ℝ) ∪ (R : Set ℝ),
      ∀ y ∈ (L : Set ℝ) ∪ (R : Set ℝ), dist (f^[s] x) (f^[s] y) < η) :
    HistoryFamily f I η (ι × Bool) := by
  classical
  let B : Bool → Segment := fun b => if b then R else L
  have hB : ∀ b, (B b : Set ℝ) ⊆ (H.terminal : Set ℝ) := by
    intro b
    cases b
    · exact hL
    · exact hR
  have hBG : ∀ b, f^[r] '' (B b : Set ℝ) = (D : Set ℝ) := by
    intro b
    cases b
    · exact hGL
    · exact hGR
  have hBU : ∀ b, (B b : Set ℝ) ⊆ (L : Set ℝ) ∪ (R : Set ℝ) := by
    intro b
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hBD : ∀ b c, b ≠ c → Disjoint (B b : Set ℝ) (B c : Set ℝ) := by
    intro b c h
    cases b <;> cases c
    · exact (h rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (h rfl).elim
  have hpull : ∀ i b, ∃ J : Segment, (J : Set ℝ) ⊆ (H.domain i : Set ℝ) ∧
      f^[H.time] '' (J : Set ℝ) = (B b : Set ℝ) := by
    intro i b
    apply exact_pullback (H.domain i) (B b)
      ((hf.iterate hmap H.time).mono (H.inside i))
    rw [H.onto i]
    exact hB b
  let J := fun i b => Classical.choose (hpull i b)
  have hJ : ∀ i b, (J i b : Set ℝ) ⊆ (H.domain i : Set ℝ) :=
    fun i b => (Classical.choose_spec (hpull i b)).1
  have hGJ : ∀ i b, f^[H.time] '' (J i b : Set ℝ) = (B b : Set ℝ) :=
    fun i b => (Classical.choose_spec (hpull i b)).2
  refine
    { domain := fun p => J p.1 p.2
      inside := fun p => (hJ p.1 p.2).trans (H.inside p.1)
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
      have hxp' := (hGJ p.1 p.2).subset (mem_image_of_mem (f^[H.time]) hxp)
      have hxq' := (hGJ q.1 q.2).subset (mem_image_of_mem (f^[H.time]) hxq)
      exact Set.disjoint_left.mp (hBD p.2 q.2 hb) hxp' hxq'
    · exact Set.disjoint_left.mp (H.disjoint p.1 q.1 hi) (hJ _ _ hxp) (hJ _ _ hxq)
  · intro p
    rw [Nat.add_comm H.time r, Function.iterate_add]
    change (fun x => f^[r] (f^[H.time] x)) '' (J p.1 p.2 : Set ℝ) = (D : Set ℝ)
    rw [← Set.image_image (f^[r]) (f^[H.time]), hGJ, hBG]
  · intro s hs p q x hx y hy
    by_cases hsT : s ≤ H.time
    · exact H.small s hsT p.1 q.1 x (hJ _ _ hx) y (hJ _ _ hy)
    · have hTs : H.time ≤ s := by omega
      have hsr : s - H.time ≤ r := by omega
      have hsplit : s = (s - H.time) + H.time := (Nat.sub_add_cancel hTs).symm
      rw [hsplit, Function.iterate_add_apply, Function.iterate_add_apply]
      apply hpost _ hsr
      · exact hBU p.2 ((hGJ p.1 p.2).subset (mem_image_of_mem _ hx))
      · exact hBU q.2 ((hGJ q.1 q.2).subset (mem_image_of_mem _ hy))

/-- Selecting one preimage of a common terminal point gives distinct points;
the cardinal comparison is for the original strict all-time Bowen set. -/
theorem card_le [Fintype ι] [Nonempty ι] (H : HistoryFamily f I η ι)
    {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hηε : η ≤ ε)
    (hB : ForwardBowenBound f I ε N) : Fintype.card ι ≤ N := by
  classical
  obtain ⟨z, hz⟩ := H.terminal.nonempty
  have hpre : ∀ i, ∃ x ∈ (H.domain i : Set ℝ), f^[H.time] x = z := by
    intro i
    exact (H.onto i).symm.subset hz
  choose x hx hT using hpre
  have hxi : Injective x := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (H.disjoint i j hne) (hx i) (hij.symm ▸ hx j)
  by_contra! hm
  let e := (Fintype.equivFin ι).symm
  apply no_coalescing_witnesses hB hε hm (fun i => x (e i)) (hxi.comp e.injective)
    (fun i => H.inside (e i) (hx (e i)))
  · intro i j s hs
    exact (H.small s hs (e i) (e j) _ (hx (e i)) _ (hx (e j))).trans_le hηε
  · intro i j
    exact (hT (e i)).trans (hT (e j)).symm

/-- One inductive extension at an actual noninjective full iterate. -/
theorem exists_extension (H : HistoryFamily f I η ι) [Nonempty ι]
    (hI : IsCompact I) (hf : ContinuousOn f I) (hmap : MapsTo f I I)
    {ε : ℝ} {N r : ℕ} (hε : 0 < ε) (hη : 0 < η)
    (hB : ForwardBowenBound f I ε N)
    (hni : ¬InjOn (f^[r]) (H.terminal : Set ℝ)) :
    ∃ H' : HistoryFamily f I η (ι × Bool), H'.time = H.time + r := by
  have hAI : (H.terminal : Set ℝ) ⊆ I := by
    let i : ι := Classical.choice inferInstance
    rw [← H.onto i]
    rintro _ ⟨x, hx, rfl⟩
    exact hmap.iterate H.time (H.inside i hx)
  obtain ⟨L, R, D, hL, hR, hdis, hGL, hGR, hpost⟩ :=
    small_disjoint_fold hI hf hmap hε hB hη H.terminal hAI hni
  exact ⟨H.double hf hmap L R D hL hR hdis hGL hGR hpost, rfl⟩

end HistoryFamily

section MacroscopicOverlap

variable {f : ℝ → ℝ} {I : Set ℝ} {ε : ℝ} {N : ℕ}

/-- The continuous image of a segment with infinite image is again a segment. -/
theorem image_segment {G : ℝ → ℝ} (A : Segment)
    (hG : ContinuousOn G (A : Set ℝ)) (hi : (G '' (A : Set ℝ)).Infinite) :
    ∃ B : Segment, G '' (A : Set ℝ) = (B : Set ℝ) := by
  have he := hG.image_Icc A.proper.le
  have hp : sInf (G '' (A : Set ℝ)) < sSup (G '' (A : Set ℝ)) := by
    by_contra! hn
    apply hi
    apply (Set.finite_singleton (sInf (G '' (A : Set ℝ)))).subset
    intro x hx
    have hx' := he.subset hx
    exact le_antisymm (hx'.2.trans hn) hx'.1
  exact ⟨⟨_, _, hp⟩, he⟩

/-- Each actual iterate image is represented by a nondegenerate interval. -/
theorem iterate_image_segment (hI : IsCompact I) (hf : ContinuousOn f I)
    (hmap : MapsTo f I I) (hε : 0 < ε) (hB : ForwardBowenBound f I ε N)
    (J : Segment) (hJI : (J : Set ℝ) ⊆ I) (n : ℕ) :
    ∃ A : Segment, f^[n] '' (J : Set ℝ) = (A : Set ℝ) := by
  exact image_segment J ((hf.iterate hmap n).mono hJI)
    (infinite_iterate_image hmap (finite_fibres hI hB hε) hJI J.infinite n)

/-- The macroscopic images contain a genuine common nondegenerate interval.
Finite pigeonhole is applied to nearby left endpoints, not to finite-time Bowen sets. -/
theorem iterate_images_overlap (hI : IsCompact I) (hf : ContinuousOn f I)
    (hmap : MapsTo f I I) (hε : 0 < ε) (hB : ForwardBowenBound f I ε N)
    (J : Segment) (hJI : (J : Set ℝ) ⊆ I) (A : ℕ → Segment)
    (hA : ∀ n, f^[n] '' (J : Set ℝ) = (A n : Set ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ H : Segment,
      (H : Set ℝ) ⊆ (A i : Set ℝ) ∧ (H : Set ℝ) ⊆ (A j : Set ℝ) := by
  classical
  have hAI : ∀ n, (A n : Set ℝ) ⊆ I := by
    intro n
    rw [← hA n]
    rintro _ ⟨x, hx, rfl⟩
    exact hmap.iterate n (hJI hx)
  let E : Set ℕ := {n | ε ≤ (A n).right - (A n).left}
  have hE : E.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro m
    obtain ⟨n, hn, x, hx, y, hy, hsep⟩ := arbitrarily_late_separation hB hmap hε
      (finite_fibres hI hB hε) hJI J.infinite (m + 1)
    refine ⟨n, ?_, by omega⟩
    have hxA := (hA n).subset (mem_image_of_mem (f^[n]) hx)
    have hyA := (hA n).subset (mem_image_of_mem (f^[n]) hy)
    have hdist : dist (f^[n] x) (f^[n] y) ≤ (A n).right - (A n).left := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hxA.1, hxA.2, hyA.1, hyA.2]
    exact hsep.trans hdist
  obtain ⟨C, _, hC, hcover⟩ := hI.finite_cover_balls (show 0 < ε / 8 by positivity)
  have hchoose : ∀ n, ∃ c ∈ C, (A n).left ∈ Metric.ball c (ε / 8) := by
    intro n
    obtain ⟨c, hc, ht⟩ := mem_iUnion₂.mp (hcover (hAI n ⟨le_rfl, (A n).proper.le⟩))
    exact ⟨c, hc, ht⟩
  choose c hc hclose using hchoose
  obtain ⟨i, hi, j, hj, hne, hcij⟩ :=
    hE.exists_ne_map_eq_of_mapsTo (fun n _ => hc n) hC
  have hnear : dist (A i).left (A j).left < ε / 4 := by
    have h₁ : dist (A i).left (c i) < ε / 8 := hclose i
    have h₂ : dist (c i) (A j).left < ε / 8 := by
      simpa only [Metric.mem_ball, hcij, dist_comm] using hclose j
    linarith [dist_triangle (A i).left (c i) (A j).left]
  have habs := abs_lt.mp (show |(A i).left - (A j).left| < ε / 4 by
    simpa only [Real.dist_eq] using hnear)
  have hiE : ε ≤ (A i).right - (A i).left := hi
  have hjE : ε ≤ (A j).right - (A j).left := hj
  have hcross₁ : (A i).left < (A j).right := by linarith [habs.1, habs.2]
  have hcross₂ : (A j).left < (A i).right := by linarith [habs.1, habs.2]
  have hspan : max (A i).left (A j).left < min (A i).right (A j).right :=
    max_lt (lt_min (A i).proper hcross₁) (lt_min hcross₂ (A j).proper)
  obtain ⟨a, ha, har⟩ := exists_between hspan
  obtain ⟨b, hab, hb⟩ := exists_between har
  let H : Segment := ⟨a, b, hab⟩
  have hHi : (H : Set ℝ) ⊆ (A i : Set ℝ) := Icc_subset_Icc
    ((le_max_left _ _).trans ha.le) (hb.le.trans (min_le_left _ _))
  have hHj : (H : Set ℝ) ⊆ (A j : Set ℝ) := Icc_subset_Icc
    ((le_max_right _ _).trans ha.le) (hb.le.trans (min_le_right _ _))
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i, j, hij, H, hHi, hHj⟩
  · exact ⟨j, i, hji, H, hHj, hHi⟩

/-- Injectivity of all iterates on J gives injectivity of any return iterate
on each actual image of J. No inverse image is assumed to be an interval. -/
theorem injective_on_iterate_image {J : Set ℝ}
    (hinj : ∀ n : ℕ, InjOn (f^[n]) J) (m p : ℕ) :
    InjOn (f^[p]) (f^[m] '' J) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
  have he' : f^[p + m] x = f^[p + m] y := by
    simpa only [Function.iterate_add_apply] using he
  exact congrArg (f^[m]) (hinj (p + m) hx hy he')

end MacroscopicOverlap

section ReturnChain

variable {F : ℝ → ℝ}

/-- Finite prefixes of an overlapping chain are order-connected and the same
strict orientation glues over each prefix, hence over the entire actual union. -/
theorem strictMonoOn_interval_chain (A : ℕ → Segment)
    (hmeet : ∀ k, ((A k : Set ℝ) ∩ (A (k + 1) : Set ℝ)).Nonempty)
    (hm : ∀ k, StrictMonoOn F (A k : Set ℝ)) :
    StrictMonoOn F (⋃ k, (A k : Set ℝ)) := by
  let V : ℕ → Set ℝ := fun n => ⋃ k ≤ n, (A k : Set ℝ)
  have hAV : ∀ k n, k ≤ n → (A k : Set ℝ) ⊆ V n := by
    intro k n hkn x hx
    exact mem_iUnion₂.mpr ⟨k, hkn, hx⟩
  have hstep : ∀ n, V (n + 1) = V n ∪ (A (n + 1) : Set ℝ) := by
    intro n
    ext x
    constructor
    · intro hx
      obtain ⟨k, hkn, hx⟩ := mem_iUnion₂.mp hx
      by_cases h : k ≤ n
      · exact Or.inl (hAV k n h hx)
      · have he : k = n + 1 := by omega
        subst k
        exact Or.inr hx
    · rintro (hx | hx)
      · obtain ⟨k, hkn, hk⟩ := mem_iUnion₂.mp hx
        exact hAV k (n + 1) (by omega) hk
      · exact hAV (n + 1) (n + 1) le_rfl hx
  have hV : ∀ n, OrdConnected (V n) ∧ StrictMonoOn F (V n) := by
    intro n
    induction n with
    | zero => simpa [V] using (And.intro (ordConnected_Icc : OrdConnected (A 0 : Set ℝ)) (hm 0))
    | succ n ih =>
      have hVN : (V n ∩ (A (n + 1) : Set ℝ)).Nonempty := by
        obtain ⟨x, hx, hy⟩ := hmeet n
        exact ⟨x, hAV n n le_rfl hx, hy⟩
      rw [hstep]
      exact ⟨(IsPreconnected.union' hVN ih.1.isPreconnected isPreconnected_Icc).ordConnected,
        strictMonoOn_union_overlap ih.1 ordConnected_Icc hVN ih.2 (hm (n + 1))⟩
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  exact (hV (max i j)).2 (hAV i _ (le_max_left _ _) hi)
    (hAV j _ (le_max_right _ _) hj) hxy

/-- Continuous injectivity on each actual image and nondegenerate neighboring
overlaps force one strict orientation on the entire countable union. -/
theorem strictly_monotone_interval_chain (A H : ℕ → Segment)
    (hHA : ∀ k, (H k : Set ℝ) ⊆ (A k : Set ℝ))
    (hHB : ∀ k, (H k : Set ℝ) ⊆ (A (k + 1) : Set ℝ))
    (hF : ∀ k, ContinuousOn F (A k : Set ℝ)) (hi : ∀ k, InjOn F (A k : Set ℝ)) :
    IsConnected (⋃ k, (A k : Set ℝ)) ∧
      (StrictMonoOn F (⋃ k, (A k : Set ℝ)) ∨ StrictAntiOn F (⋃ k, (A k : Set ℝ))) := by
  have hmeet : ∀ k, ((A k : Set ℝ) ∩ (A (k + 1) : Set ℝ)).Nonempty := by
    intro k
    obtain ⟨x, hx⟩ := (H k).nonempty
    exact ⟨x, hHA k hx, hHB k hx⟩
  have hp : ∀ k, StrictMonoOn F ((A k : Set ℝ) ∪ (A (k + 1) : Set ℝ)) ∨
      StrictAntiOn F ((A k : Set ℝ) ∪ (A (k + 1) : Set ℝ)) := by
    intro k
    exact strictly_monotone_union_of_injective (A k) (A (k + 1)) (H k)
      (hHA k) (hHB k) (hF k) (hF (k + 1)) (hi k) (hi (k + 1))
  have propagate : ∀ {G : ℝ → ℝ},
      (∀ k, StrictMonoOn G ((A k : Set ℝ) ∪ (A (k + 1) : Set ℝ)) ∨
        StrictAntiOn G ((A k : Set ℝ) ∪ (A (k + 1) : Set ℝ))) →
      StrictMonoOn G (A 0 : Set ℝ) → StrictMonoOn G (⋃ k, (A k : Set ℝ)) := by
    intro G hpair hzero
    have hall : ∀ k, StrictMonoOn G (A k : Set ℝ) := by
      intro k
      induction k with
      | zero => exact hzero
      | succ k ih =>
        rcases hpair k with hm | ha
        · exact hm.mono subset_union_right
        · have hl : (A k).left ∈ (A k : Set ℝ) := ⟨le_rfl, (A k).proper.le⟩
          have hr : (A k).right ∈ (A k : Set ℝ) := ⟨(A k).proper.le, le_rfl⟩
          exact (not_lt_of_gt (ih hl hr (A k).proper)
            (ha (Or.inl hl) (Or.inl hr) (A k).proper)).elim
    exact strictMonoOn_interval_chain A hmeet hall
  refine ⟨IsConnected.iUnion_of_chain
    (fun k => ⟨(A k).nonempty, isPreconnected_Icc⟩) hmeet, ?_⟩
  rcases (hF 0).strictMonoOn_of_injOn_Icc' (A 0).proper.le (hi 0) with hm | ha
  · exact Or.inl (propagate hp hm)
  · have hpn : ∀ k, StrictMonoOn (fun x => -F x) ((A k : Set ℝ) ∪ (A (k + 1) : Set ℝ)) ∨
        StrictAntiOn (fun x => -F x) ((A k : Set ℝ) ∪ (A (k + 1) : Set ℝ)) := by
      intro k
      rcases hp k with hm | ha
      · exact Or.inr (fun x hx y hy hxy => neg_lt_neg (hm hx hy hxy))
      · exact Or.inl (fun x hx y hy hxy => neg_lt_neg (ha hx hy hxy))
    have hzero : StrictMonoOn (fun x => -F x) (A 0 : Set ℝ) :=
      fun x hx y hy hxy => neg_lt_neg (ha hx hy hxy)
    have hn := propagate hpn hzero
    exact Or.inr (fun x hx y hy hxy => neg_lt_neg_iff.mp (hn hx hy hxy))

/-- A compact connected infinite real set is represented by a genuine segment. -/
theorem compact_connected_segment {S : Set ℝ} (hc : IsCompact S)
    (hn : IsConnected S) (hi : S.Infinite) : ∃ K : Segment, S = (K : Set ℝ) := by
  have he := eq_Icc_of_connected_compact hn hc
  have hp : sInf S < sSup S := by
    by_contra! h
    apply hi
    apply (Set.finite_singleton (sInf S)).subset
    intro x hx
    have hx' := he.subset hx
    exact le_antisymm (hx'.2.trans h) hx'.1
  exact ⟨⟨sInf S, sSup S, hp⟩, he⟩

end ReturnChain

section GlobalReturn

variable {f : ℝ → ℝ} {I : Set ℝ} {ε : ℝ} {N : ℕ}

/-- The elementary overlap-return argument: no nondegenerate interval can
have all forward iterates injective under a finite strict all-time Bowen bound. -/
theorem exists_noninjective_iterate (hI : IsCompact I) (hf : ContinuousOn f I)
    (hmap : MapsTo f I I) (hε : 0 < ε) (hB : ForwardBowenBound f I ε N)
    (J : Segment) (hJI : (J : Set ℝ) ⊆ I) :
    ∃ r : ℕ, 0 < r ∧ ¬InjOn (f^[r]) (J : Set ℝ) := by
  classical
  by_contra! hall
  have hinj : ∀ n : ℕ, InjOn (f^[n]) (J : Set ℝ) := by
    intro n
    cases n with
    | zero => intro x _ y _ he; simpa only [Function.iterate_zero_apply] using he
    | succ n => exact hall (n + 1) (by omega)
  have himages : ∀ n, ∃ A : Segment, f^[n] '' (J : Set ℝ) = (A : Set ℝ) :=
    fun n => iterate_image_segment hI hf hmap hε hB J hJI n
  choose A hA using himages
  have hAI : ∀ n, (A n : Set ℝ) ⊆ I := by
    intro n
    rw [← hA n]
    rintro _ ⟨x, hx, rfl⟩
    exact hmap.iterate n (hJI hx)
  obtain ⟨i, j, hij, H₀, hH₀i, hH₀j⟩ := iterate_images_overlap hI hf hmap hε hB J hJI A hA
  let p := j - i
  have hp : 0 < p := Nat.sub_pos_of_lt hij
  have hj : j = i + p := by dsimp [p]; omega
  let B : ℕ → Segment := fun k => A (i + k * p)
  have hshift : ∀ n m, f^[n] '' (A m : Set ℝ) = (A (n + m) : Set ℝ) := by
    intro n m
    calc
      _ = f^[n] '' (f^[m] '' (J : Set ℝ)) := by rw [hA m]
      _ = f^[n + m] '' (J : Set ℝ) := by rw [Set.image_image, Function.iterate_add]; rfl
      _ = (A (n + m) : Set ℝ) := hA (n + m)
  have hFB : ∀ k, f^[p] '' (B k : Set ℝ) = (B (k + 1) : Set ℝ) := by
    intro k
    have he : p + (i + k * p) = i + (k + 1) * p := by ring
    simpa only [B, he] using hshift p (i + k * p)
  have hH₀I : (H₀ : Set ℝ) ⊆ I := hH₀i.trans (hAI i)
  have hHimages : ∀ k, ∃ H : Segment, f^[k * p] '' (H₀ : Set ℝ) = (H : Set ℝ) :=
    fun k => iterate_image_segment hI hf hmap hε hB H₀ hH₀I (k * p)
  choose H hH using hHimages
  have hHB : ∀ k, (H k : Set ℝ) ⊆ (B k : Set ℝ) := by
    intro k
    rw [← hH k]
    have he : k * p + i = i + k * p := Nat.add_comm _ _
    exact (Set.image_mono hH₀i).trans (by simpa only [B, he] using (hshift (k * p) i).subset)
  have hHB' : ∀ k, (H k : Set ℝ) ⊆ (B (k + 1) : Set ℝ) := by
    intro k
    rw [← hH k]
    have he : k * p + j = i + (k + 1) * p := by rw [hj]; ring
    exact (Set.image_mono hH₀j).trans (by simpa only [B, he] using (hshift (k * p) j).subset)
  have hcontB : ∀ k, ContinuousOn (f^[p]) (B k : Set ℝ) :=
    fun k => (hf.iterate hmap p).mono (hAI (i + k * p))
  have hinjB : ∀ k, InjOn (f^[p]) (B k : Set ℝ) := by
    intro k
    change InjOn (f^[p]) (A (i + k * p) : Set ℝ)
    rw [← hA (i + k * p)]
    exact injective_on_iterate_image hinj (i + k * p) p
  obtain ⟨hconn, hmono⟩ := strictly_monotone_interval_chain B H hHB hHB' hcontB hinjB
  let U : Set ℝ := ⋃ k, (B k : Set ℝ)
  have hUI : U ⊆ I := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact hAI (i + k * p) hk
  have hclI : closure U ⊆ I := closure_minimal hUI hI.isClosed
  have hFcl : ContinuousOn (f^[p]) (closure U) := (hf.iterate hmap p).mono hclI
  have hFU : MapsTo (f^[p]) U U := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨k + 1, (hFB k).subset (mem_image_of_mem _ hk)⟩
  have htrap := hFU.closure_of_continuousOn hFcl
  have hcomp : IsCompact (closure U) := hI.of_isClosed_subset isClosed_closure hclI
  have hinf : (closure U).Infinite := (B 0).infinite.mono (by
    intro x hx
    exact subset_closure (mem_iUnion.mpr ⟨0, hx⟩))
  obtain ⟨K, hK⟩ := compact_connected_segment hcomp hconn.closure hinf
  have hfibcl : ∀ z, (closure U ∩ (f^[p]) ⁻¹' {z}).Finite := by
    intro z
    exact (finite_iterate_fibres hmap (finite_fibres hI hB hε) p z).subset
      (inter_subset_inter_left _ hclI)
  have hstrict := strictly_monotone_closure hconn.closure.isPreconnected.ordConnected
    hFcl hfibcl hmono
  rw [hK] at htrap hstrict
  have hKI : (K : Set ℝ) ⊆ I := by simpa only [hK] using hclI
  exact no_strictly_monotone_trapping hI hf hmap hε hB hp K hKI htrap hstrict

end GlobalReturn

section Amplification

variable {f : ℝ → ℝ} {ε η : ℝ} {N : ℕ}

/-- Actual binary history amplification for every depth, with no homterval or
noninjectivity supplier among the hypotheses. -/
theorem arbitrarily_many_histories (I : Segment) (hf : ContinuousOn f (I : Set ℝ))
    (hmap : MapsTo f (I : Set ℝ) (I : Set ℝ)) (hε : 0 < ε)
    (hB : ForwardBowenBound f (I : Set ℝ) ε N) (hη : 0 < η) (k : ℕ) :
    ∃ (ι : Type) (hι : Fintype ι) (_ : Nonempty ι),
      ∃ H : HistoryFamily f (I : Set ℝ) η ι, @Fintype.card ι hι = 2 ^ k := by
  classical
  induction k with
  | zero =>
    let r := min I.right (I.left + η / 2)
    have hlr : I.left < r := lt_min I.proper (by linarith)
    let J : Segment := ⟨I.left, r, hlr⟩
    have hJI : (J : Set ℝ) ⊆ (I : Set ℝ) := Icc_subset_Icc le_rfl (min_le_left _ _)
    have hJsmall : ∀ x ∈ (J : Set ℝ), ∀ y ∈ (J : Set ℝ), dist x y < η := by
      intro x hx y hy
      have hr : r ≤ I.left + η / 2 := min_le_right _ _
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    let H : HistoryFamily f (I : Set ℝ) η PUnit :=
      { domain := fun _ => J
        inside := fun _ => hJI
        disjoint := fun i j h => (h (Subsingleton.elim i j)).elim
        time := 0
        terminal := J
        onto := by intro i; simp
        small := by
          intro s hs i j x hx y hy
          have he : s = 0 := by omega
          subst s
          simpa only [Function.iterate_zero_apply] using hJsmall x hx y hy }
    exact ⟨PUnit, inferInstance, inferInstance, H, by simp⟩
  | succ k ih =>
    obtain ⟨ι, hι, hne, H, hcard⟩ := ih
    letI := hι
    letI := hne
    have hAI : (H.terminal : Set ℝ) ⊆ (I : Set ℝ) := by
      let i : ι := Classical.choice hne
      rw [← H.onto i]
      rintro _ ⟨x, hx, rfl⟩
      exact hmap.iterate H.time (H.inside i hx)
    obtain ⟨r, hr, hni⟩ := exists_noninjective_iterate I.compact hf hmap hε hB H.terminal hAI
    obtain ⟨H', _⟩ := H.exists_extension I.compact hf hmap hε hη hB hni
    refine ⟨ι × Bool, inferInstance, inferInstance, H', ?_⟩
    simpa only [Fintype.card_prod, Fintype.card_bool, pow_succ, hcard]

/-- Full real-interval obstruction with the original strict all-forward-time
bound. There is no surjectivity or additional dynamical premise. -/
theorem not_forwardBowenBound (I : Segment) (hf : ContinuousOn f (I : Set ℝ))
    (hmap : MapsTo f (I : Set ℝ) (I : Set ℝ)) (hε : 0 < ε) :
    ¬ForwardBowenBound f (I : Set ℝ) ε N := by
  intro hB
  obtain ⟨ι, hι, hne, H, hcard⟩ := arbitrarily_many_histories I hf hmap hε hB hε N
  letI := hι
  letI := hne
  have hle := H.card_le hε le_rfl hB
  rw [hcard] at hle
  exact (not_le_of_gt N.lt_two_pow_self) hle

/-- Cardinal failure supplies genuine distinct witnesses, still quantified
over every natural-number time. -/
theorem witnesses_of_not_bound {X : Type*} [MetricSpace X] {f : X → X}
    {K : Set X} {ε : ℝ} {N : ℕ} (hB : ¬ForwardBowenBound f K ε N) :
    ∃ x ∈ K, ∃ y : Fin (N + 1) → X, Injective y ∧
      ∀ i, y i ∈ K ∧ ∀ t : ℕ, dist (f^[t] x) (f^[t] (y i)) < ε := by
  classical
  have hex : ∃ x ∈ K, (N : ℕ∞) < (K ∩ ForwardBowen f ε x).encard := by
    by_contra! h
    exact hB h
  obtain ⟨x, hx, hlarge⟩ := hex
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ (K ∩ ForwardBowen f ε x).encard := by
    by_cases ht : (K ∩ ForwardBowen f ε x).encard = ⊤
    · rw [ht]
      exact le_top
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ht
      rw [← hm] at hlarge ⊢
      exact_mod_cast Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp hlarge)
  obtain ⟨y, hy, hi⟩ := (Set.le_encard_iff_exists_fin_injective _ (N + 1)).mp hle
  exact ⟨x, hx, y, hi, fun i => ⟨(hy i).1, (hy i).2⟩⟩

end Amplification

section OriginalInterval

variable {a b : ℝ}

/-- The all-time bound on the subtype transfers to its real-interval extension
using an exact identification of the Bowen sets under subtype inclusion. -/
theorem interval_extension_bound (hab : a ≤ b) (f : Icc a b → Icc a b)
    {ε : ℝ} {N : ℕ} (hB : ForwardBowenBound f univ ε N) :
    ForwardBowenBound (Set.IccExtend hab (fun x => (f x : ℝ))) (Icc a b) ε N := by
  let F : ℝ → ℝ := Set.IccExtend hab (fun x => (f x : ℝ))
  have hsem : Semiconj (fun x : Icc a b => (x : ℝ)) f F := by
    intro x
    exact (Set.IccExtend_of_mem hab (fun x => (f x : ℝ)) x.property).symm
  intro x hx
  let x' : Icc a b := ⟨x, hx⟩
  have he : Icc a b ∩ ForwardBowen F ε x =
      Subtype.val '' (univ ∩ ForwardBowen f ε x') := by
    ext y
    constructor
    · rintro ⟨hy, hclose⟩
      let y' : Icc a b := ⟨y, hy⟩
      refine ⟨y', ⟨mem_univ _, ?_⟩, rfl⟩
      intro t
      change dist (↑(f^[t] x') : ℝ) (↑(f^[t] y') : ℝ) < ε
      have hxsem : (f^[t] x' : ℝ) = F^[t] x := hsem.iterate_right t x'
      have hysem : (f^[t] y' : ℝ) = F^[t] y := hsem.iterate_right t y'
      rw [hxsem, hysem]
      exact hclose t
    · rintro ⟨y', ⟨_, hclose⟩, rfl⟩
      refine ⟨y'.property, fun t => ?_⟩
      have ht := hclose t
      change dist (↑(f^[t] x') : ℝ) (↑(f^[t] y') : ℝ) < ε at ht
      have hxsem : (f^[t] x' : ℝ) = F^[t] x := hsem.iterate_right t x'
      have hysem : (f^[t] y' : ℝ) = F^[t] (y' : ℝ) := hsem.iterate_right t y'
      rw [hxsem, hysem] at ht
      exact ht
  change (Icc a b ∩ ForwardBowen F ε x).encard ≤ (N : ℕ∞)
  rw [he]
  exact (Set.encard_image_le _ _).trans (hB x' (mem_univ _))

/-- Original nondegenerate compact real-interval theorem. The map acts on
the actual subtype; witnesses are distinct and close at every forward time. -/
theorem interval_bowen_witnesses (hab : a < b) (f : Icc a b → Icc a b)
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ x : Icc a b, ∃ y : Fin (N + 1) → Icc a b, Injective y ∧
      ∀ i, ∀ t : ℕ, dist (f^[t] x) (f^[t] (y i)) < ε := by
  have hnot : ¬ForwardBowenBound f univ ε N := by
    intro hB
    let F : ℝ → ℝ := Set.IccExtend hab.le (fun x => (f x : ℝ))
    have hF : Continuous F := continuous_IccExtend_iff.mpr (continuous_subtype_val.comp hf)
    have hmap : MapsTo F (Icc a b) (Icc a b) := by
      intro x hx
      exact (f (Set.projIcc a b hab.le x)).property
    exact not_forwardBowenBound (⟨a, b, hab⟩ : Segment) hF.continuousOn hmap hε
      (interval_extension_bound hab.le f hB)
  obtain ⟨x, _, y, hi, hy⟩ := witnesses_of_not_bound hnot
  exact ⟨x, y, hi, fun i => (hy i).2⟩

/-- The original finite-positive-expansivity obstruction, leaving the existing
N=1 `PositivelyExpansive` definition unchanged. -/
theorem interval_not_finitelyPositiveExpansive (hab : a < b)
    (f : Icc a b → Icc a b) (hf : Continuous f) : ¬FinitelyPositiveExpansive f := by
  rintro ⟨ε, hε, N, _, hB⟩
  obtain ⟨x, y, hi, hy⟩ := interval_bowen_witnesses hab f hf hε N
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ (univ ∩ ForwardBowen f ε x).encard := by
    apply (Set.le_encard_iff_exists_fin_injective _ (N + 1)).mpr
    exact ⟨y, fun i => ⟨mem_univ _, hy i⟩, hi⟩
  have hbad := hle.trans (hB x (mem_univ _))
  have hbad' : N + 1 ≤ N := by exact_mod_cast hbad
  omega

end OriginalInterval

end IntervalObstruction
end D5.S1.Dynamics.Shadowing
