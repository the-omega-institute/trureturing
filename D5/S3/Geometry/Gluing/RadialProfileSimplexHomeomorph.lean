/- GID: D5/S3/Geometry/Gluing/RadialProfileSimplexHomeomorph
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/RadialProfileSimplexHomeomorph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Order.OrderClosed]
   utility: none
   digest: Explicit radial interpolation with a moving inverse interface. -/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Tactic

open Set Topology
noncomputable section
namespace D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph

/-- The source profile range, including both endpoints. -/
abbrev ProfileRange := Icc (1 / 4 : ℝ) (23 / 48)

/-- Radial interpolation, extended to the real line by the same outer formulas. -/
def forward (a r : ℝ) : ℝ :=
  if r ≤ 1 / 4 then 4 * a * r
  else if r ≤ 1 / 2 then a + 4 * (1 / 2 - a) * (r - 1 / 4) else r

/-- Explicit inverse; its first interface varies with the profile value. -/
def backward (a s : ℝ) : ℝ :=
  if s ≤ a then s / (4 * a)
  else if s ≤ 1 / 2 then 1 / 4 + (s - a) / (4 * (1 / 2 - a)) else s

private theorem a_pos (a : ProfileRange) : 0 < (a : ℝ) := by
  have := a.property.1
  linarith

private theorem a_lt_half (a : ProfileRange) : (a : ℝ) < 1 / 2 := by
  have := a.property.2
  linarith

private theorem forward_first (a : ProfileRange) {r : ℝ} (hr : r ≤ 1 / 4) :
    forward a r = 4 * (a : ℝ) * r := if_pos hr

private theorem forward_middle (a : ProfileRange) {r : ℝ}
    (hl : 1 / 4 ≤ r) (hr : r ≤ 1 / 2) :
    forward a r = (a : ℝ) + 4 * (1 / 2 - (a : ℝ)) * (r - 1 / 4) := by
  by_cases h : r ≤ 1 / 4
  · have he : r = 1 / 4 := le_antisymm h hl
    simp [forward, he]
    ring
  · simp only [forward, if_neg h, if_pos hr]

private theorem forward_last (a : ProfileRange) {r : ℝ} (hr : 1 / 2 ≤ r) :
    forward a r = r := by
  by_cases h : r ≤ 1 / 2
  · have he : r = 1 / 2 := le_antisymm h hr
    norm_num [forward, he]
    ring
  · have hq : ¬r ≤ 1 / 4 := by linarith
    simp only [forward, if_neg hq, if_neg h]

private theorem inverse_left (a : ProfileRange) (r : ℝ) :
    backward a (forward a r) = r := by
  have ha := a_pos a
  have hb := a_lt_half a
  by_cases hq : r ≤ 1 / 4
  · rw [forward_first a hq, backward, if_pos (by nlinarith)]
    field_simp
  · have hq' : 1 / 4 < r := lt_of_not_ge hq
    by_cases hR : r ≤ 1 / 2
    · rw [forward_middle a hq'.le hR, backward]
      have hlow : ¬ (a : ℝ) + 4 * (1 / 2 - (a : ℝ)) * (r - 1 / 4) ≤ a := by
        nlinarith
      have hupp : (a : ℝ) + 4 * (1 / 2 - (a : ℝ)) * (r - 1 / 4) ≤ 1 / 2 := by
        nlinarith
      rw [if_neg hlow, if_pos hupp]
      field_simp [ha.ne', show (1 - (a : ℝ) * 2) ≠ 0 by linarith]
      ring
    · rw [forward_last a (le_of_lt (lt_of_not_ge hR)), backward,
        if_neg (by linarith), if_neg hR]

private theorem inverse_right (a : ProfileRange) (s : ℝ) :
    forward a (backward a s) = s := by
  have ha := a_pos a
  have hb := a_lt_half a
  have hd : 0 < 4 * (1 / 2 - (a : ℝ)) := by linarith
  by_cases hs : s ≤ a
  · rw [backward, if_pos hs, forward_first a ((div_le_iff₀ (by positivity)).mpr (by nlinarith))]
    field_simp
  · by_cases hR : s ≤ 1 / 2
    · rw [backward, if_neg hs, if_pos hR]
      have hq : 1 / 4 ≤ 1 / 4 + (s - (a : ℝ)) / (4 * (1 / 2 - (a : ℝ))) := by
        have := div_nonneg (by linarith : 0 ≤ s - (a : ℝ)) hd.le
        linarith
      have hh : 1 / 4 + (s - (a : ℝ)) / (4 * (1 / 2 - (a : ℝ))) ≤ 1 / 2 := by
        have : (s - (a : ℝ)) / (4 * (1 / 2 - (a : ℝ))) ≤ 1 / 4 :=
          (div_le_iff₀ hd).mpr (by linarith)
        linarith
      rw [forward_middle a hq hh]
      field_simp [ha.ne', show (1 - (a : ℝ) * 2) ≠ 0 by linarith]
      ring
    · rw [backward, if_neg hs, if_neg hR, forward_last a (by linarith)]

private theorem forward_joint : Continuous (fun p : ProfileRange × ℝ => forward p.1 p.2) := by
  have ha : Continuous (fun p : ProfileRange × ℝ => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hm : Continuous (fun p : ProfileRange × ℝ =>
      (p.1 : ℝ) + 4 * (1 / 2 - (p.1 : ℝ)) * (p.2 - 1 / 4)) := by fun_prop
  have hi : Continuous (fun p : ProfileRange × ℝ =>
      if p.2 ≤ 1 / 2 then (p.1 : ℝ) + 4 * (1 / 2 - (p.1 : ℝ)) * (p.2 - 1 / 4)
      else p.2) :=
    hm.if_le continuous_snd continuous_snd continuous_const (by intro p hp; rw [hp]; ring)
  exact (show Continuous (fun p : ProfileRange × ℝ => 4 * (p.1 : ℝ) * p.2) by fun_prop).if_le
    hi continuous_snd continuous_const (by
      intro p hp
      rw [hp, if_pos (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)]
      ring)

private theorem backward_joint : Continuous (fun p : ProfileRange × ℝ => backward p.1 p.2) := by
  have ha : Continuous (fun p : ProfileRange × ℝ => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hn : ∀ p : ProfileRange × ℝ, 4 * (p.1 : ℝ) ≠ 0 :=
    fun p => ne_of_gt (mul_pos (by norm_num) (a_pos p.1))
  have hd : ∀ p : ProfileRange × ℝ, 4 * (1 / 2 - (p.1 : ℝ)) ≠ 0 :=
    fun p => ne_of_gt (mul_pos (by norm_num) (sub_pos.mpr (a_lt_half p.1)))
  have hf : Continuous (fun p : ProfileRange × ℝ => p.2 / (4 * (p.1 : ℝ))) :=
    continuous_snd.div (continuous_const.mul ha) hn
  have hm : Continuous (fun p : ProfileRange × ℝ =>
      1 / 4 + (p.2 - (p.1 : ℝ)) / (4 * (1 / 2 - (p.1 : ℝ)))) :=
    continuous_const.add ((continuous_snd.sub ha).div
      (continuous_const.mul (continuous_const.sub ha)) hd)
  have hi : Continuous (fun p : ProfileRange × ℝ =>
      if p.2 ≤ 1 / 2 then 1 / 4 + (p.2 - (p.1 : ℝ)) / (4 * (1 / 2 - (p.1 : ℝ)))
      else p.2) := hm.if_le continuous_snd continuous_snd continuous_const (by
        intro p hp
        rw [hp]
        rw [show (1 / 2 - (p.1 : ℝ)) / (4 * (1 / 2 - (p.1 : ℝ))) = 1 / 4 from
          (div_eq_iff (hd p)).mpr (by ring)]
        norm_num)
  exact hf.if_le hi continuous_snd ha (by
    intro p hp
    rw [hp, if_pos (a_lt_half p.1).le]
    have h := hn p
    field_simp [(a_pos p.1).ne']
    <;> ring)

private theorem forward_zero (a : ProfileRange) : forward a 0 = 0 := by
  norm_num [forward]

private theorem forward_quarter (a : ProfileRange) : forward a (1 / 4) = a := by
  norm_num [forward]
  ring

private theorem forward_half (a : ProfileRange) : forward a (1 / 2) = 1 / 2 :=
  forward_last a le_rfl

private theorem forward_one (a : ProfileRange) : forward a 1 = 1 :=
  forward_last a (by norm_num)

private theorem forward_strict (a : ProfileRange) : StrictMono (forward a) := by
  have hc : Continuous (forward a) := forward_joint.comp (continuous_const.prodMk continuous_id)
  rcases hc.strictMono_of_inj (Function.LeftInverse.injective (inverse_left a)) with h | h
  · exact h
  · have hh := h (by norm_num : (0 : ℝ) < 1)
    rw [forward_zero, forward_one] at hh
    norm_num at hh

private theorem forward_mem (a : ProfileRange) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 2)) :
    forward a r ∈ Icc (0 : ℝ) (1 / 2) := by
  constructor
  · simpa only [forward_zero] using (forward_strict a).monotone hr.1
  · simpa only [forward_half] using (forward_strict a).monotone hr.2

private theorem backward_zero (a : ProfileRange) : backward a 0 = 0 := by
  simpa only [forward_zero] using inverse_left a 0

private theorem backward_half (a : ProfileRange) : backward a (1 / 2) = 1 / 2 := by
  simpa only [forward_half] using inverse_left a (1 / 2)

private theorem backward_mem (a : ProfileRange) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (1 / 2)) :
    backward a r ∈ Icc (0 : ℝ) (1 / 2) := by
  constructor
  · apply (forward_strict a).le_iff_le.mp
    simpa only [inverse_right, forward_zero] using hr.1
  · apply (forward_strict a).le_iff_le.mp
    simpa only [inverse_right, forward_half] using hr.2

abbrev Simplex := stdSimplex ℝ (Fin 4)
abbrev Opposite (i : Fin 4) := {u : Simplex // u.val i = 0}
abbrev Radius := Icc (0 : ℝ) (1 / 2)
abbrev Central := {x : Simplex // ∀ i, x.val i ≤ 1 / 2}

/-- The actual old vertex of the standard simplex. -/
def vertex (i : Fin 4) : Simplex := ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩

/-- Actual affine radial coordinates on the closed half-corner. -/
def ray (i : Fin 4) (u : Opposite i) (r : Radius) : Simplex :=
  ⟨(1 - (r : ℝ)) • (vertex i).val + (r : ℝ) • u.val.val,
    (convex_stdSimplex ℝ (Fin 4)) (vertex i).property u.val.property
      (by have := r.property.2; linarith) r.property.1 (by ring)⟩

theorem ray_at (i : Fin 4) (u : Opposite i) (r : Radius) :
    (ray i u r).val i = 1 - (r : ℝ) := by
  simp [ray, vertex, u.property]

theorem ray_other (i : Fin 4) (u : Opposite i) (r : Radius) (j : Fin 4)
    (h : j ≠ i) : (ray i u r).val j = (r : ℝ) * u.val.val j := by
  simp [ray, vertex, h]

theorem simplex_pair (x : Simplex) {i j : Fin 4} (h : i ≠ j) :
    x.val i + x.val j ≤ 1 := by
  have hs : ∑ k ∈ ({i, j} : Finset (Fin 4)), x.val k ≤ ∑ k, x.val k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro k _ _; exact x.property.1 k)
  simpa [Finset.sum_pair h, x.property.2] using hs

private theorem ray_injective (i : Fin 4) (u v : Opposite i) (r s : Radius)
    (hr : (r : ℝ) ≠ 0) (h : ray i u r = ray i v s) : u = v ∧ r = s := by
  have he := congrArg (fun x : Simplex => x.val i) h
  rw [ray_at, ray_at] at he
  have hrs : r = s := Subtype.ext (by linarith)
  subst s
  refine ⟨?_, rfl⟩
  apply Subtype.ext
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j; exact u.property.trans v.property.symm
  · have hh := congrArg (fun x : Simplex => x.val j) h
    rw [ray_other i u r j hj, ray_other i v r j hj] at hh
    exact mul_left_cancel₀ hr hh

private theorem ray_zero (i : Fin 4) (u : Opposite i) (r : Radius) (hr : (r : ℝ) = 0) :
    ray i u r = vertex i := by
  apply Subtype.ext
  simp [ray, hr]

private theorem opposite_nonempty (i : Fin 4) : Nonempty (Opposite i) := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨⟨vertex j, by simp [vertex, Ne.symm hj]⟩⟩

theorem ray_cover (x : Simplex) (i : Fin 4) (hi : 1 / 2 ≤ x.val i) :
    ∃ (u : Opposite i) (r : Radius), ray i u r = x := by
  have hx := mem_Icc_of_mem_stdSimplex x.property i
  let r : Radius := ⟨1 - x.val i, ⟨sub_nonneg.mpr hx.2, by linarith⟩⟩
  by_cases hz : (r : ℝ) = 0
  · obtain ⟨u⟩ := opposite_nonempty i
    refine ⟨u, r, (ray_zero i u r hz).trans ?_⟩
    apply Subtype.ext
    funext j
    have hxi : x.val i = 1 := by change 1 - x.val i = 0 at hz; linarith
    by_cases hj : j = i
    · subst j; simp [vertex, hxi]
    · have hp := simplex_pair x (Ne.symm hj)
      have hn := x.property.1 j
      have hxj : x.val j = 0 := by linarith
      simp [vertex, hj, hxj]
  · have hr : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1 (Ne.symm hz)
    let v : Fin 4 → ℝ := fun j => if j = i then 0 else x.val j / (r : ℝ)
    have hv : v ∈ stdSimplex ℝ (Fin 4) := by
      constructor
      · intro j; dsimp [v]; split_ifs
        · exact le_rfl
        · exact div_nonneg (x.property.1 j) hr.le
      · have hsum : ∑ j, (if j = i then 0 else x.val j) = 1 - x.val i := by
          have h : (∑ j, if j = i then 0 else x.val j) +
              (∑ j, if j = i then x.val j else 0) = ∑ j, x.val j := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, x.property.2] at h
          linarith
        change ∑ j, (if j = i then 0 else x.val j / (r : ℝ)) = 1
        have hid (j : Fin 4) : (if j = i then (0 : ℝ) else x.val j / (r : ℝ)) =
            (if j = i then 0 else x.val j) / (r : ℝ) := by split_ifs <;> simp
        simp_rw [hid]
        rw [← Finset.sum_div, hsum]
        exact div_self hz
    let u : Opposite i := ⟨⟨v, hv⟩, by simp [v]⟩
    refine ⟨u, r, ?_⟩
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j; rw [ray_at]; dsimp [r]; ring
    · rw [ray_other i u r j hj]
      change (r : ℝ) * (if j = i then 0 else x.val j / (r : ℝ)) = x.val j
      rw [if_neg hj, mul_div_cancel₀ _ hz]


abbrev Charts := (Σ i : Fin 4, Opposite i × Radius) ⊕ Central

def project : Charts → Simplex
  | .inl ⟨i, u, r⟩ => ray i u r
  | .inr x => x.val

theorem project_surjective : Function.Surjective project := by
  intro x
  by_cases hc : ∀ i, x.val i ≤ 1 / 2
  · exact ⟨.inr ⟨x, hc⟩, rfl⟩
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    obtain ⟨u, r, h⟩ := ray_cover x i hi.le
    exact ⟨.inl ⟨i, u, r⟩, h⟩

def zeroRadius : Radius := ⟨0, by norm_num⟩
def halfRadius : Radius := ⟨1 / 2, by norm_num⟩

def onChart (α : ∀ i, Opposite i → ProfileRange)
    (k : ProfileRange → Radius → Radius) : Charts → Simplex
  | .inl ⟨i, u, r⟩ => ray i u (k (α i u) r)
  | .inr x => x.val

private theorem onChart_fiber (α : ∀ i, Opposite i → ProfileRange)
    (k : ProfileRange → Radius → Radius)
    (hzero : ∀ a, k a zeroRadius = zeroRadius)
    (hhalf : ∀ a, k a halfRadius = halfRadius)
    (p q : Charts) (hpq : project p = project q) : onChart α k p = onChart α k q := by
  have hcc (i : Fin 4) (u : Opposite i) (r : Radius) (x : Central)
      (h : ray i u r = x.val) : ray i u (k (α i u) r) = x.val := by
    have hi := x.property i
    rw [← h, ray_at] at hi
    have hr : r = halfRadius := Subtype.ext (by
      change (r : ℝ) = 1 / 2
      have := r.property.2
      linarith)
    subst r
    rw [hhalf]
    exact h
  cases p with
  | inl p =>
    rcases p with ⟨i, u, r⟩
    cases q with
    | inr x => exact hcc i u r x hpq
    | inl q =>
      rcases q with ⟨j, v, s⟩
      change ray i u r = ray j v s at hpq
      change ray i u (k (α i u) r) = ray j v (k (α j v) s)
      by_cases hij : i = j
      · subst j
        have hh := congrArg (fun x : Simplex => x.val i) hpq
        rw [ray_at, ray_at] at hh
        have hrs : r = s := Subtype.ext (by linarith)
        subst s
        by_cases hr : (r : ℝ) = 0
        · have he : r = zeroRadius := Subtype.ext hr
          subst r
          rw [hzero, hzero, ray_zero i u zeroRadius rfl, ray_zero i v zeroRadius rfl]
        · obtain ⟨huv, _⟩ := ray_injective i u v r r hr hpq
          subst v; rfl
      · have hh := simplex_pair (ray i u r) hij
        rw [ray_at, hpq, ray_at] at hh
        have hr := r.property.2
        have hs := s.property.2
        have her : r = halfRadius := Subtype.ext (by change (r : ℝ) = 1 / 2; linarith)
        have hes : s = halfRadius := Subtype.ext (by change (s : ℝ) = 1 / 2; linarith)
        subst r; subst s
        rw [hhalf, hhalf]
        exact hpq
  | inr x =>
    cases q with
    | inr y => exact hpq
    | inl q =>
      rcases q with ⟨i, u, r⟩
      exact (hcc i u r x hpq.symm).symm

/-- Evaluation from radial charts. The fiber lemma removes all chart-choice ambiguity. -/
def move (α : ∀ i, Opposite i → ProfileRange)
    (k : ProfileRange → Radius → Radius) (x : Simplex) : Simplex :=
  if ∃ i, x = vertex i then x else onChart α k (Function.surjInv project_surjective x)

theorem move_project (α : ∀ i, Opposite i → ProfileRange)
    (k : ProfileRange → Radius → Radius)
    (hzero : ∀ a, k a zeroRadius = zeroRadius)
    (hhalf : ∀ a, k a halfRadius = halfRadius) (p : Charts) :
    move α k (project p) = onChart α k p := by
  unfold move
  split_ifs with hv
  · obtain ⟨i, hi⟩ := hv
    obtain ⟨u⟩ := opposite_nonempty i
    have he : project (.inl ⟨i, u, zeroRadius⟩) = project p := by
      exact (ray_zero i u zeroRadius rfl).trans hi.symm
    rw [← onChart_fiber α k hzero hhalf _ _ he]
    change project p = ray i u (k (α i u) zeroRadius)
    rw [hzero, ray_zero i u zeroRadius rfl]
    exact hi
  · exact onChart_fiber α k hzero hhalf _ _ (Function.surjInv_eq project_surjective _)

private instance : CompactSpace Simplex :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin 4))

private instance (i : Fin 4) : CompactSpace (Opposite i) :=
  isCompact_iff_compactSpace.mp
    (isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const).isCompact

private instance : CompactSpace Central := by
  apply isCompact_iff_compactSpace.mp
  have h : IsClosed {x : Simplex | ∀ i, x.val i ≤ 1 / 2} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le
      ((continuous_apply i).comp continuous_subtype_val) continuous_const
  exact h.isCompact

private theorem continuous_ray (i : Fin 4) :
    Continuous (fun p : Opposite i × Radius => ray i p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Opposite i × Radius =>
    (1 - (p.2 : ℝ)) • (vertex i).val + (p.2 : ℝ) • p.1.val.val)
  fun_prop

private theorem continuous_project : Continuous project := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_sigma fun i => continuous_ray i
  · exact continuous_subtype_val

theorem continuous_move (α : ∀ i, Opposite i → ProfileRange)
    (hα : ∀ i, Continuous (α i)) (k : ProfileRange → Radius → Radius)
    (hk : Continuous (fun p : ProfileRange × Radius => k p.1 p.2))
    (hzero : ∀ a, k a zeroRadius = zeroRadius)
    (hhalf : ∀ a, k a halfRadius = halfRadius) : Continuous (move α k) := by
  have hq := continuous_project.isClosedMap.isQuotientMap continuous_project project_surjective
  apply hq.continuous_iff.mpr
  have he : move α k ∘ project = onChart α k := funext (move_project α k hzero hhalf)
  rw [he]
  apply continuous_sum_dom.mpr
  constructor
  · apply continuous_sigma
    intro i
    exact (continuous_ray i).comp (continuous_fst.prodMk
      (hk.comp (((hα i).comp continuous_fst).prodMk continuous_snd)))
  · exact continuous_subtype_val

private def forwardRadius (a : ProfileRange) (r : Radius) : Radius :=
  ⟨forward a r, forward_mem a r.property⟩
private def backwardRadius (a : ProfileRange) (r : Radius) : Radius :=
  ⟨backward a r, backward_mem a r.property⟩

private theorem forwardRadius_zero (a : ProfileRange) :
    forwardRadius a zeroRadius = zeroRadius := Subtype.ext (forward_zero a)
private theorem forwardRadius_half (a : ProfileRange) :
    forwardRadius a halfRadius = halfRadius := Subtype.ext (forward_half a)
private theorem backwardRadius_zero (a : ProfileRange) :
    backwardRadius a zeroRadius = zeroRadius := Subtype.ext (backward_zero a)
private theorem backwardRadius_half (a : ProfileRange) :
    backwardRadius a halfRadius = halfRadius := Subtype.ext (backward_half a)

/-- The actual radial map on the standard closed tetrahedron. -/
def phi (α : ∀ i, Opposite i → ProfileRange) : Simplex → Simplex := move α forwardRadius
/-- Its explicit inverse uses the inverse interpolation on the same radial charts. -/
def psi (α : ∀ i, Opposite i → ProfileRange) : Simplex → Simplex := move α backwardRadius

private theorem phi_ray (α : ∀ i, Opposite i → ProfileRange)
    (i : Fin 4) (u : Opposite i) (r : Radius) :
    phi α (ray i u r) = ray i u (forwardRadius (α i u) r) :=
  move_project α forwardRadius forwardRadius_zero forwardRadius_half (.inl ⟨i, u, r⟩)
private theorem psi_ray (α : ∀ i, Opposite i → ProfileRange)
    (i : Fin 4) (u : Opposite i) (r : Radius) :
    psi α (ray i u r) = ray i u (backwardRadius (α i u) r) :=
  move_project α backwardRadius backwardRadius_zero backwardRadius_half (.inl ⟨i, u, r⟩)
private theorem phi_central (α : ∀ i, Opposite i → ProfileRange) (x : Central) :
    phi α x.val = x.val :=
  move_project α forwardRadius forwardRadius_zero forwardRadius_half (.inr x)
private theorem psi_central (α : ∀ i, Opposite i → ProfileRange) (x : Central) :
    psi α x.val = x.val :=
  move_project α backwardRadius backwardRadius_zero backwardRadius_half (.inr x)

private theorem psi_phi (α : ∀ i, Opposite i → ProfileRange) (x : Simplex) :
    psi α (phi α x) = x := by
  obtain ⟨p, rfl⟩ := project_surjective x
  cases p with
  | inl p =>
    rcases p with ⟨i, u, r⟩
    change psi α (phi α (ray i u r)) = ray i u r
    rw [phi_ray, psi_ray]
    congr 1
    exact Subtype.ext (inverse_left (α i u) r)
  | inr x => change psi α (phi α x.val) = x.val; rw [phi_central, psi_central]
private theorem phi_psi (α : ∀ i, Opposite i → ProfileRange) (x : Simplex) :
    phi α (psi α x) = x := by
  obtain ⟨p, rfl⟩ := project_surjective x
  cases p with
  | inl p =>
    rcases p with ⟨i, u, r⟩
    change phi α (psi α (ray i u r)) = ray i u r
    rw [psi_ray, phi_ray]
    congr 1
    exact Subtype.ext (inverse_right (α i u) r)
  | inr x => change phi α (psi α x.val) = x.val; rw [psi_central, phi_central]

/-- The closed-tetrahedron homeomorphism for arbitrary continuous admissible profiles. -/
def radialHomeomorph (α : ∀ i, Opposite i → ProfileRange) (hα : ∀ i, Continuous (α i)) :
    Simplex ≃ₜ Simplex where
  toFun := phi α
  invFun := psi α
  left_inv := psi_phi α
  right_inv := phi_psi α
  continuous_toFun := continuous_move α hα forwardRadius
    ((forward_joint.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _)
    forwardRadius_zero forwardRadius_half
  continuous_invFun := continuous_move α hα backwardRadius
    ((backward_joint.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _)
    backwardRadius_zero backwardRadius_half


private theorem phi_zero_iff (α : ∀ i, Opposite i → ProfileRange)
    (x : Simplex) (j : Fin 4) : (phi α x).val j = 0 ↔ x.val j = 0 := by
  obtain ⟨p, rfl⟩ := project_surjective x
  cases p with
  | inr x => change (phi α x.val).val j = 0 ↔ x.val.val j = 0; rw [phi_central]
  | inl p =>
    rcases p with ⟨i, u, r⟩
    change (phi α (ray i u r)).val j = 0 ↔ (ray i u r).val j = 0
    rw [phi_ray]
    by_cases hj : j = i
    · subst j
      rw [ray_at, ray_at]
      have hr := r.property.2
      have ht := (forwardRadius (α i u) r).property.2
      constructor <;> intro h <;> linarith
    · rw [ray_other i u _ j hj, ray_other i u _ j hj]
      have hz : forward (α i u) r = 0 ↔ (r : ℝ) = 0 := by
        have h : forward (α i u) r = forward (α i u) 0 ↔ (r : ℝ) = 0 :=
          (forward_strict (α i u)).injective.eq_iff
        simpa only [forward_zero] using h
      change forward (α i u) r * u.val.val j = 0 ↔ (r : ℝ) * u.val.val j = 0
      simp only [mul_eq_zero, hz]

/-- Coordinate action with exactly the original inverse-permutation convention. -/
def permute (ρ : Equiv.Perm (Fin 4)) (x : Simplex) : Simplex :=
  ⟨fun j => x.val (ρ.symm j), ⟨fun j => x.property.1 (ρ.symm j),
    (Equiv.sum_comp ρ.symm x.val).trans x.property.2⟩⟩

def permuteOpposite (ρ : Equiv.Perm (Fin 4)) (i : Fin 4) (u : Opposite i) :
    Opposite (ρ i) :=
  ⟨permute ρ u.val, by simpa only [permute, Equiv.symm_apply_apply] using u.property⟩

theorem permute_ray (ρ : Equiv.Perm (Fin 4)) (i : Fin 4)
    (u : Opposite i) (r : Radius) :
    permute ρ (ray i u r) = ray (ρ i) (permuteOpposite ρ i u) r := by
  apply Subtype.ext
  funext j
  by_cases hj : j = ρ i
  · subst j
    change (ray i u r).val (ρ.symm (ρ i)) = (ray (ρ i) (permuteOpposite ρ i u) r).val (ρ i)
    rw [Equiv.symm_apply_apply, ray_at, ray_at]
  · have hk : ρ.symm j ≠ i := by intro h; apply hj; simpa only [← h, Equiv.apply_symm_apply]
    change (ray i u r).val (ρ.symm j) = (ray (ρ i) (permuteOpposite ρ i u) r).val j
    rw [ray_other _ _ _ _ hk, ray_other _ _ _ _ hj]
    rfl

private theorem phi_natural (α β : ∀ i, Opposite i → ProfileRange)
    (ρ : Equiv.Perm (Fin 4))
    (h : ∀ i u, β (ρ i) (permuteOpposite ρ i u) = α i u) (x : Simplex) :
    phi β (permute ρ x) = permute ρ (phi α x) := by
  obtain ⟨p, rfl⟩ := project_surjective x
  cases p with
  | inl p =>
    rcases p with ⟨i, u, r⟩
    change phi β (permute ρ (ray i u r)) = permute ρ (phi α (ray i u r))
    rw [permute_ray, phi_ray, phi_ray, permute_ray, h]
  | inr x =>
    have hc : ∀ i, (permute ρ x.val).val i ≤ 1 / 2 := fun i => x.property _
    change phi β (permute ρ x.val) = permute ρ (phi α x.val)
    rw [phi_central α x]
    exact phi_central β ⟨_, hc⟩

private theorem phi_vertex (α : ∀ i, Opposite i → ProfileRange) (i : Fin 4) :
    phi α (vertex i) = vertex i := by
  obtain ⟨u⟩ := opposite_nonempty i
  rw [← ray_zero i u zeroRadius rfl, phi_ray, forwardRadius_zero]

private theorem phi_cap (α : ∀ i, Opposite i → ProfileRange) (i : Fin 4) (u : Opposite i) :
    phi α (ray i u ⟨1 / 4, by norm_num⟩) =
      ray i u ⟨α i u, ⟨(a_pos (α i u)).le, (a_lt_half (α i u)).le⟩⟩ := by
  rw [phi_ray]
  congr 1
  exact Subtype.ext (forward_quarter (α i u))


/-- Extrema over the three actual non-omitted coordinates. -/
def directionMax (i : Fin 4) (u : Opposite i) : ℝ :=
  max (u.val.val (i.succAbove 0))
    (max (u.val.val (i.succAbove 1)) (u.val.val (i.succAbove 2)))
def directionMin (i : Fin 4) (u : Opposite i) : ℝ :=
  min (u.val.val (i.succAbove 0))
    (min (u.val.val (i.succAbove 1)) (u.val.val (i.succAbove 2)))

def sourceValue (i : Fin 4) (u : Opposite i) : ℝ :=
  let M := directionMax i u
  let m := directionMin i u
  let w := 1 - M - m
  1 / (1 + M + max (2 * (M - w)) (max (3 * (w - m)) (4 * m)))

private theorem triple_statistics (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 1) :
    0 ≤ min a (min b c) ∧ min a (min b c) ≤ 1 - max a (max b c) - min a (min b c) ∧
    1 - max a (max b c) - min a (min b c) ≤ max a (max b c) ∧ max a (max b c) ≤ 1 := by
  simp only [max_def, min_def]
  split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

private theorem statistics (i : Fin 4) (u : Opposite i) :
    0 ≤ directionMin i u ∧ directionMin i u ≤ 1 - directionMax i u - directionMin i u ∧
    1 - directionMax i u - directionMin i u ≤ directionMax i u ∧ directionMax i u ≤ 1 := by
  apply triple_statistics _ _ _ (u.val.property.1 _) (u.val.property.1 _) (u.val.property.1 _)
  have hs := u.val.property.2
  have hi := u.property
  fin_cases i
  · change u.val.val 1 + u.val.val 2 + u.val.val 3 = 1
    change u.val.val 0 = 0 at hi
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change u.val.val 0 + (u.val.val 1 + (u.val.val 2 + u.val.val 3)) = 1 at hs
    rw [hi] at hs
    linarith
  · change u.val.val 0 + u.val.val 2 + u.val.val 3 = 1
    change u.val.val 1 = 0 at hi
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change u.val.val 0 + (u.val.val 1 + (u.val.val 2 + u.val.val 3)) = 1 at hs
    rw [hi] at hs
    linarith
  · change u.val.val 0 + u.val.val 1 + u.val.val 3 = 1
    change u.val.val 2 = 0 at hi
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change u.val.val 0 + (u.val.val 1 + (u.val.val 2 + u.val.val 3)) = 1 at hs
    rw [hi] at hs
    linarith
  · change u.val.val 0 + u.val.val 1 + u.val.val 2 = 1
    change u.val.val 3 = 0 at hi
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change u.val.val 0 + (u.val.val 1 + (u.val.val 2 + u.val.val 3)) = 1 at hs
    rw [hi] at hs
    linarith

private theorem source_bounds (i : Fin 4) (u : Opposite i) :
    sourceValue i u ∈ ProfileRange := by
  obtain ⟨hm, hmw, hwM, hM⟩ := statistics i u
  let M := directionMax i u
  let m := directionMin i u
  let w := 1 - M - m
  let t := max (2 * (M - w)) (max (3 * (w - m)) (4 * m))
  have h1 : 2 * (M - w) ≤ t := le_max_left _ _
  have h2 : 3 * (w - m) ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : 4 * m ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  have he : M + w + m = 1 := by dsimp [w]; ring
  change 0 ≤ m at hm
  change m ≤ w at hmw
  change w ≤ M at hwM
  change M ≤ 1 at hM
  have ht : t ≤ 3 - M := by
    apply max_le
    · linarith
    · apply max_le <;> linarith
  have hl : 48 / 23 ≤ 1 + M + t := by linarith
  have hd : 0 < 1 + M + t := by linarith
  change 1 / 4 ≤ 1 / (1 + M + t) ∧ 1 / (1 + M + t) ≤ 23 / 48
  exact ⟨(le_div_iff₀ hd).mpr (by linarith), (div_le_iff₀ hd).mpr (by linarith)⟩

/-- The source's concrete profile, with its bounds proved from its formula. -/
def sourceProfile (i : Fin 4) (u : Opposite i) : ProfileRange :=
  ⟨sourceValue i u, source_bounds i u⟩

private theorem source_continuous (i : Fin 4) : Continuous (sourceProfile i) := by
  have hc (j : Fin 4) : Continuous (fun u : Opposite i => u.val.val j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hM : Continuous (directionMax i) :=
    (hc _).max ((hc _).max (hc _))
  have hm : Continuous (directionMin i) :=
    (hc _).min ((hc _).min (hc _))
  apply Continuous.subtype_mk
  unfold sourceValue
  apply Continuous.div continuous_const
  · fun_prop
  · intro u
    have ⟨hm0, hmw, hwM, _⟩ := statistics i u
    have hmax : 4 * directionMin i u ≤
        max (2 * (directionMax i u - (1 - directionMax i u - directionMin i u)))
          (max (3 * ((1 - directionMax i u - directionMin i u) - directionMin i u))
            (4 * directionMin i u)) :=
      (le_max_right _ _).trans (le_max_right _ _)
    linarith

private theorem directionMax_le (i : Fin 4) (u : Opposite i) (b : ℝ) :
    directionMax i u ≤ b ↔ ∀ j, j ≠ i → u.val.val j ≤ b := by
  fin_cases i <;> simp [directionMax, max_le_iff, Fin.forall_fin_succ, Fin.succAbove]

private theorem le_directionMin (i : Fin 4) (u : Opposite i) (b : ℝ) :
    b ≤ directionMin i u ↔ ∀ j, j ≠ i → b ≤ u.val.val j := by
  fin_cases i <;> simp [directionMin, le_min_iff, Fin.forall_fin_succ, Fin.succAbove]

private theorem source_covariant (ρ : Equiv.Perm (Fin 4)) (i : Fin 4) (u : Opposite i) :
    sourceProfile (ρ i) (permuteOpposite ρ i u) = sourceProfile i u := by
  have hM : directionMax (ρ i) (permuteOpposite ρ i u) = directionMax i u := by
    apply le_antisymm
    · apply (directionMax_le _ _ _).mpr
      intro j hj
      apply (directionMax_le i u _).mp le_rfl (ρ.symm j)
      intro h; apply hj; simpa only [← h, Equiv.apply_symm_apply]
    · apply (directionMax_le _ _ _).mpr
      intro j hj
      have h := (directionMax_le (ρ i) (permuteOpposite ρ i u) _).mp le_rfl
        (ρ j) (fun he => hj (ρ.injective he))
      simpa only [permuteOpposite, permute, Equiv.symm_apply_apply] using h
  have hm : directionMin (ρ i) (permuteOpposite ρ i u) = directionMin i u := by
    apply le_antisymm
    · apply (le_directionMin _ _ _).mpr
      intro j hj
      have h := (le_directionMin (ρ i) (permuteOpposite ρ i u) _).mp le_rfl
        (ρ j) (fun he => hj (ρ.injective he))
      simpa only [permuteOpposite, permute, Equiv.symm_apply_apply] using h
    · apply (le_directionMin _ _ _).mpr
      intro j hj
      apply (le_directionMin i u _).mp le_rfl (ρ.symm j)
      intro h; apply hj; simpa only [← h, Equiv.apply_symm_apply]
  apply Subtype.ext
  change sourceValue (ρ i) (permuteOpposite ρ i u) = sourceValue i u
  unfold sourceValue
  rw [hM, hm]

/-- Instantiation of the constructed simplex homeomorphism with the source formula. -/
def sourceHomeomorph : Simplex ≃ₜ Simplex := radialHomeomorph sourceProfile source_continuous

/-- The original tagged zero-coordinate generator; every occurrence keeps its own face witness. -/
def seam {T : Type*} (next : T × Fin 4 → T) (σ : T × Fin 4 → Equiv.Perm (Fin 4))
    (a b : T × Simplex) : Prop :=
  ∃ f : Fin 4, a.2.val f = 0 ∧ b = (next (a.1, f), permute (σ (a.1, f)) a.2)

/-- The same constructed map, acting separately on the tagged copies. -/
def taggedHomeomorph {T : Type*} [TopologicalSpace T] : (T × Simplex) ≃ₜ (T × Simplex) :=
  (Homeomorph.refl T).prodCongr sourceHomeomorph

private theorem seam_iff {T : Type*} [TopologicalSpace T]
    (next : T × Fin 4 → T) (σ : T × Fin 4 → Equiv.Perm (Fin 4)) (a b : T × Simplex) :
    seam next σ (taggedHomeomorph a) (taggedHomeomorph b) ↔ seam next σ a b := by
  constructor
  · rintro ⟨f, hf, hb⟩
    refine ⟨f, (phi_zero_iff sourceProfile a.2 f).mp hf, ?_⟩
    apply (taggedHomeomorph (T := T)).injective
    change (b.1, phi sourceProfile b.2) =
      (next (a.1, f), phi sourceProfile (permute (σ (a.1, f)) a.2))
    rw [phi_natural sourceProfile sourceProfile _ (source_covariant _)]
    exact hb
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f, (phi_zero_iff sourceProfile a.2 f).mpr hf, ?_⟩
    change (next (a.1, f), phi sourceProfile (permute (σ (a.1, f)) a.2)) =
      (next (a.1, f), permute (σ (a.1, f)) (phi sourceProfile a.2))
    rw [phi_natural sourceProfile sourceProfile _ (source_covariant _)]

private theorem original_eqv_iff {T : Type*} [TopologicalSpace T]
    (next : T × Fin 4 → T) (σ : T × Fin 4 → Equiv.Perm (Fin 4)) (a b : T × Simplex) :
    Relation.EqvGen (seam next σ) (taggedHomeomorph a) (taggedHomeomorph b) ↔
      Relation.EqvGen (seam next σ) a b := by
  let H : (T × Simplex) ≃ₜ (T × Simplex) := taggedHomeomorph
  have hf (a b : T × Simplex) (h : Relation.EqvGen (seam next σ) a b) :
      Relation.EqvGen (seam next σ) (H a) (H b) := by
    induction h with
    | rel a b h => exact .rel _ _ ((seam_iff next σ a b).mpr h)
    | refl a => exact .refl _
    | symm a b h ih => exact .symm _ _ ih
    | trans a b c h k ih ik => exact .trans _ _ _ ih ik
  have hb (a b : T × Simplex) (h : Relation.EqvGen (seam next σ) a b) :
      Relation.EqvGen (seam next σ) (H.symm a) (H.symm b) := by
    induction h with
    | rel a b h =>
      apply Relation.EqvGen.rel
      apply (seam_iff next σ (H.symm a) (H.symm b)).mp
      change seam next σ (H (H.symm a)) (H (H.symm b))
      simpa only [H.apply_symm_apply] using h
    | refl a => exact .refl _
    | symm a b h ih => exact .symm _ _ ih
    | trans a b c h k ih ik => exact .trans _ _ _ ih ik
  exact ⟨fun h => by simpa only [H.symm_apply_apply] using hb (H a) (H b) h, hf a b⟩

private theorem psi_natural (α β : ∀ i, Opposite i → ProfileRange)
    (ρ : Equiv.Perm (Fin 4))
    (h : ∀ i u, β (ρ i) (permuteOpposite ρ i u) = α i u) (x : Simplex) :
    psi β (permute ρ x) = permute ρ (psi α x) := by
  apply Function.LeftInverse.injective (psi_phi β)
  rw [phi_psi, phi_natural α β ρ h, phi_psi]

private theorem ray_apex_bound (i : Fin 4) (u : Opposite i) (r : Radius) (j : Fin 4) :
    |(ray i u r).val j - (vertex i).val j| ≤ (r : ℝ) := by
  by_cases hj : j = i
  · subst j
    rw [ray_at]
    simp only [vertex, Pi.single_eq_same]
    rw [abs_of_nonpos (by have := r.property.1; linarith)]
    linarith
  · rw [ray_other i u r j hj]
    have hjv : (vertex i).val j = 0 := by simp [vertex, hj]
    rw [hjv, sub_zero, abs_of_nonneg (mul_nonneg r.property.1 (u.val.property.1 j))]
    exact mul_le_of_le_one_right r.property.1 (mem_Icc_of_mem_stdSimplex u.val.property j).2

private theorem forward_apex_bound (α : ∀ i, Opposite i → ProfileRange)
    (i : Fin 4) (u : Opposite i) (r : Radius) (hr : (r : ℝ) ≤ 1 / 4) (j : Fin 4) :
    |(phi α (ray i u r)).val j - (vertex i).val j| ≤ 23 / 12 * (r : ℝ) := by
  rw [phi_ray]
  apply (ray_apex_bound i u _ j).trans
  change forward (α i u) r ≤ 23 / 12 * (r : ℝ)
  rw [forward_first (α i u) hr]
  nlinarith [mul_nonneg r.property.1 (sub_nonneg.mpr (α i u).property.2)]

private theorem backward_apex_bound (α : ∀ i, Opposite i → ProfileRange)
    (i : Fin 4) (u : Opposite i) (r : Radius) (hr : (r : ℝ) ≤ 1 / 4) (j : Fin 4) :
    |(psi α (ray i u r)).val j - (vertex i).val j| ≤ (r : ℝ) := by
  rw [psi_ray]
  apply (ray_apex_bound i u _ j).trans
  change backward (α i u) r ≤ (r : ℝ)
  rw [backward, if_pos (hr.trans (α i u).property.1)]
  apply (div_le_iff₀ (mul_pos (by norm_num) (a_pos (α i u)))).mpr
  nlinarith [mul_nonneg r.property.1 (sub_nonneg.mpr (α i u).property.1)]


/-- Explicit formulas, all zero faces and transported-profile naturality for the constructed map. -/
theorem radial_homeomorph_spec (α : ∀ i, Opposite i → ProfileRange)
    (hα : ∀ i, Continuous (α i)) :
    (∀ i, radialHomeomorph α hα (vertex i) = vertex i) ∧
    (∀ i u r, radialHomeomorph α hα (ray i u r) = ray i u (forwardRadius (α i u) r)) ∧
    (∀ i u r, (radialHomeomorph α hα).symm (ray i u r) = ray i u (backwardRadius (α i u) r)) ∧
    (∀ x : Central, radialHomeomorph α hα x.val = x.val ∧
      (radialHomeomorph α hα).symm x.val = x.val) ∧
    (∀ x j, (phi α x).val j = 0 ↔ x.val j = 0) ∧
    (∀ x j, ((radialHomeomorph α hα).symm x).val j = 0 ↔ x.val j = 0) ∧
    (∀ (J : Set (Fin 4)) x, (∀ j ∈ J, (radialHomeomorph α hα x).val j = 0) ↔
      ∀ j ∈ J, x.val j = 0) ∧
    (∀ (β : ∀ i, Opposite i → ProfileRange) (ρ : Equiv.Perm (Fin 4)),
      (∀ i u, β (ρ i) (permuteOpposite ρ i u) = α i u) →
      ∀ x, phi β (permute ρ x) = permute ρ (phi α x)) ∧
    (∀ (β : ∀ i, Opposite i → ProfileRange) (ρ : Equiv.Perm (Fin 4)),
      (∀ i u, β (ρ i) (permuteOpposite ρ i u) = α i u) →
      ∀ x, psi β (permute ρ x) = permute ρ (psi α x)) ∧
    (∀ i u (r : Radius), (r : ℝ) ≤ 1 / 4 → ∀ j,
      |(phi α (ray i u r)).val j - (vertex i).val j| ≤ 23 / 12 * (r : ℝ) ∧
      |(psi α (ray i u r)).val j - (vertex i).val j| ≤ (r : ℝ)) ∧
    (∀ i u, radialHomeomorph α hα (ray i u ⟨1 / 4, by norm_num⟩) =
      ray i u ⟨α i u, ⟨(a_pos (α i u)).le, (a_lt_half (α i u)).le⟩⟩) := by
  refine ⟨phi_vertex α, phi_ray α, psi_ray α, fun x => ⟨phi_central α x, psi_central α x⟩,
    phi_zero_iff α, ?_, ?_, phi_natural α, psi_natural α,
    (fun i u r hr j => ⟨forward_apex_bound α i u r hr j,
      backward_apex_bound α i u r hr j⟩), phi_cap α⟩
  · intro x j
    have h := phi_zero_iff α (psi α x) j
    rw [phi_psi] at h
    exact h.symm
  · intro J x
    simp only [show ∀ j, (radialHomeomorph α hα x).val j = 0 ↔ x.val j = 0 from phi_zero_iff α x]

/-- Source covariance and both directions of the original generator and full equivalence closure. -/
theorem source_original_relation {T : Type*} [TopologicalSpace T]
    (next : T × Fin 4 → T) (σ : T × Fin 4 → Equiv.Perm (Fin 4)) :
    (∀ ρ i u, sourceProfile (ρ i) (permuteOpposite ρ i u) = sourceProfile i u) ∧
    (∀ a b, seam next σ (taggedHomeomorph a) (taggedHomeomorph b) ↔ seam next σ a b) ∧
    (∀ a b, Relation.EqvGen (seam next σ) (taggedHomeomorph a) (taggedHomeomorph b) ↔
      Relation.EqvGen (seam next σ) a b) :=
  ⟨source_covariant, seam_iff next σ, original_eqv_iff next σ⟩

/-- Direct use of the upstream quotient congruence on the exact original generated relation. -/
def originalQuotientHomeomorph {T : Type*} [TopologicalSpace T]
    (next : T × Fin 4 → T) (σ : T × Fin 4 → Equiv.Perm (Fin 4)) :
    Quotient (Relation.EqvGen.setoid (seam next σ)) ≃ₜ
      Quotient (Relation.EqvGen.setoid (seam next σ)) :=
  Homeomorph.Quotient.congr taggedHomeomorph (fun a b => ((source_original_relation next σ).2.2 a b).symm)

#print axioms radial_homeomorph_spec
#print axioms source_original_relation
#print axioms radialHomeomorph
#print axioms sourceHomeomorph
#print axioms originalQuotientHomeomorph

end D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph
