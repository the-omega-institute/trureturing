/- GID: D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complete difference-span and endpoint balances for anchored square partitions. -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.CastCard
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance

open scoped BigOperators
open Finset

/-- The actual original coordinate pairs in a square of side q. -/
abbrev Cell (q : ℕ) := Fin q × Fin q

/-- The signed difference of the two original coordinates. -/
def difference {q : ℕ} (x : Cell q) : ℤ := (x.1.val : ℤ) - x.2.val

/-- A complete disjoint square partition, with its attained diagonal labels
and no repeated difference within a class. -/
structure Cover (q : ℕ) where
  label : Cell q → Fin q
  anchor : ∀ t, label (t, t) = t
  separates : ∀ x y, label x = label y → difference x = difference y → x = y

namespace Cover

noncomputable section

variable {q : ℕ} (C : Cover q)

/-- The entire class of one label. -/
def cells (t : Fin q) : Finset (Cell q) := univ.filter (C.label · = t)

/-- The occupied differences of the entire class. -/
def occupied (t : Fin q) : Finset ℤ := (C.cells t).image difference

private lemma zero_mem (t : Fin q) : 0 ∈ C.occupied t := by
  classical
  exact mem_image.mpr ⟨(t, t), by simp [cells, C.anchor], by simp [difference]⟩

private lemma occupied_nonempty (t : Fin q) : (C.occupied t).Nonempty :=
  ⟨0, C.zero_mem t⟩

/-- Actual lower and upper occupied endpoints. -/
def lower (t : Fin q) : ℤ := (C.occupied t).min' (C.occupied_nonempty t)

def upper (t : Fin q) : ℤ := (C.occupied t).max' (C.occupied_nonempty t)

/-- Class size, inherited defect, class gap count and total gap count. -/
def size (t : Fin q) : ℤ := (C.cells t).card

def defect (t : Fin q) : ℤ := 19 - C.size t

def gap (t : Fin q) : ℤ := C.upper t - C.lower t + 1 - C.size t

def totalGap : ℤ := ∑ t, C.gap t

/-- Classes whose occupied difference set contains j. -/
def supplied (j : ℤ) : Finset (Fin q) := univ.filter (j ∈ C.occupied ·)

/-- Classes whose actual span contains j. -/
def spanning (j : ℤ) : Finset (Fin q) :=
  univ.filter (fun t => C.lower t ≤ j ∧ j ≤ C.upper t)

/-- A missing membership retains its class index. -/
def missing (j : ℤ) : Finset (Fin q) :=
  (C.spanning j).filter (j ∉ C.occupied ·)

def spanCount (j : ℤ) : ℤ := (C.spanning j).card

def holeCount (j : ℤ) : ℤ := (C.missing j).card

def starts (j : ℤ) : ℤ := (univ.filter (C.lower · = j)).card

def ends (j : ℤ) : ℤ := (univ.filter (C.upper · = j)).card

private lemma occupied_bounds (t : Fin q) (j : ℤ) (hj : j ∈ C.occupied t) :
    1 - (q : ℤ) ≤ j ∧ j ≤ (q : ℤ) - 1 := by
  classical
  obtain ⟨x, _, rfl⟩ := mem_image.mp hj
  have ha := x.1.isLt
  have hb := x.2.isLt
  dsimp [difference]
  omega

private lemma endpoints (t : Fin q) :
    1 - (q : ℤ) ≤ C.lower t ∧ C.lower t ≤ 0 ∧
      0 ≤ C.upper t ∧ C.upper t ≤ (q : ℤ) - 1 := by
  classical
  refine ⟨(C.occupied_bounds t _ (min'_mem _ _)).1,
    min'_le _ 0 (C.zero_mem t), le_max' _ 0 (C.zero_mem t),
    (C.occupied_bounds t _ (max'_mem _ _)).2⟩

private lemma occupied_in_span (t : Fin q) (j : ℤ) (hj : j ∈ C.occupied t) :
    C.lower t ≤ j ∧ j ≤ C.upper t :=
  ⟨min'_le _ j hj, le_max' _ j hj⟩

private lemma occupied_card (t : Fin q) : (C.occupied t).card = (C.cells t).card := by
  classical
  apply card_image_iff.mpr
  intro x hx y hy hd
  exact C.separates x y
    ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) hd

private lemma total_size : (∑ t, C.size t) = (q : ℤ) ^ 2 := by
  classical
  have h : ∑ t : Fin q, (C.cells t).card = (univ : Finset (Cell q)).card := by
    simpa [cells] using
      (card_eq_sum_card_fiberwise (s := (univ : Finset (Cell q)))
        (t := (univ : Finset (Fin q))) (f := C.label) (by simp)).symm
  unfold size
  have he : ∑ t : Fin q, (C.cells t).card = q ^ 2 := by
    simpa [Fintype.card_prod, pow_two] using h
  exact_mod_cast he

private def band (q : ℕ) (j : ℤ) : Finset (Cell q) :=
  univ.filter (difference · = j)

private lemma positive_band_card (q k : ℕ) (hk : k < q) :
    (band q (k : ℤ)).card = q - k := by
  classical
  have h := card_bij
    (s := (univ : Finset (Fin (q - k)))) (t := band q (k : ℤ))
    (fun i _ => ((⟨i.val + k, by omega⟩, ⟨i.val, by omega⟩) : Cell q))
    (by
      intro i hi
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      dsimp [difference]
      omega)
    (by
      intro i hi r hr he
      apply Fin.ext
      exact congrArg (fun x : Cell q => x.2.val) he)
    (by
      intro x hx
      have hd := (mem_filter.mp hx).2
      have ha := x.1.isLt
      have hb := x.2.isLt
      dsimp [difference] at hd
      refine ⟨⟨x.2.val, by omega⟩, mem_univ _, ?_⟩
      apply Prod.ext
      · apply Fin.ext
        dsimp
        omega
      · rfl)
  simpa using h.symm

private lemma reflect_band_card (q : ℕ) (j : ℤ) :
    (band q (-j)).card = (band q j).card := by
  classical
  apply card_bij (fun x _ => (x.2, x.1))
  · intro x hx
    simp only [band, mem_filter, mem_univ, true_and] at hx ⊢
    dsimp [difference] at hx ⊢
    omega
  · intro x hx y hy h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro x hx
    refine ⟨(x.2, x.1), ?_, rfl⟩
    simp only [band, mem_filter, mem_univ, true_and] at hx ⊢
    dsimp [difference] at hx ⊢
    omega

private lemma band_card (j : ℤ) (hj : |j| < (q : ℤ)) :
    ((band q j).card : ℤ) = (q : ℤ) - |j| := by
  by_cases h : 0 ≤ j
  · have hk : j.toNat < q := by rw [abs_of_nonneg h] at hj; omega
    have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg h
    have hc := positive_band_card q j.toNat hk
    rw [he] at hc
    rw [hc, Nat.cast_sub hk.le, abs_of_nonneg h, he]
  · have hn : 0 ≤ -j := by omega
    have hk : (-j).toNat < q := by rw [abs_of_neg (by omega)] at hj; omega
    have he : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg hn
    have hc := positive_band_card q (-j).toNat hk
    rw [he, reflect_band_card] at hc
    rw [hc, Nat.cast_sub hk.le, abs_of_neg (by omega), he]

private lemma supplied_card (j : ℤ) : (C.supplied j).card = (band q j).card := by
  classical
  have he : C.supplied j = (band q j).image C.label := by
    ext t
    simp only [supplied, occupied, cells, band, mem_filter, mem_univ, true_and,
      mem_image]
    constructor
    · rintro ⟨x, hx, hd⟩
      exact ⟨x, hd, hx⟩
    · rintro ⟨x, hd, hx⟩
      exact ⟨x, hx, hd⟩
  rw [he]
  apply card_image_iff.mpr
  intro x hx y hy he
  exact C.separates x y he ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)

private lemma incidence_split (j : ℤ) :
    C.spanCount j = ((C.supplied j).card : ℤ) + C.holeCount j := by
  classical
  have he : (C.spanning j).filter (j ∈ C.occupied ·) = C.supplied j := by
    ext t
    simp only [spanning, supplied, mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨C.occupied_in_span t j h, h⟩⟩
  have h := card_filter_add_card_filter_not (s := C.spanning j) (fun t => j ∈ C.occupied t)
  rw [he] at h
  dsimp [spanCount, holeCount, missing]
  exact_mod_cast h.symm

private lemma span_balance (j : ℤ) (hj : |j| < (q : ℤ)) :
    C.spanCount j = (q : ℤ) - |j| + C.holeCount j := by
  rw [C.incidence_split, C.supplied_card, band_card j hj]

private def gaps (t : Fin q) : Finset ℤ :=
  Icc (C.lower t) (C.upper t) \ C.occupied t

private lemma gap_card (t : Fin q) : C.gap t = ((C.gaps t).card : ℤ) := by
  classical
  have hs : C.occupied t ⊆ Icc (C.lower t) (C.upper t) := by
    intro j hj
    exact mem_Icc.mpr (C.occupied_in_span t j hj)
  have hb := C.endpoints t
  rw [gaps, cast_card_sdiff hs,
    Int.card_Icc_of_le (a := C.lower t) (b := C.upper t) (by omega), C.occupied_card]
  dsimp [gap, size]
  ring

private lemma holes_support (j : ℤ) (hj : j < 1 - (q : ℤ) ∨ (q : ℤ) - 1 < j) :
    C.holeCount j = 0 := by
  classical
  have he : C.missing j = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hs := (mem_filter.mp (mem_filter.mp ht).1).2
    have hb := C.endpoints t
    omega
  simp [holeCount, he]

private lemma boundary_holes (j : ℤ)
    (hj : j = 0 ∨ j = 1 - (q : ℤ) ∨ j = (q : ℤ) - 1) : C.holeCount j = 0 := by
  classical
  have he : C.missing j = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hspan := (mem_filter.mp (mem_filter.mp ht).1).2
    have hnot := (mem_filter.mp ht).2
    have hb := C.endpoints t
    rcases hj with rfl | rfl | rfl
    · exact hnot (C.zero_mem t)
    · have hl : C.lower t = 1 - (q : ℤ) := by omega
      exact hnot (hl ▸ min'_mem _ _)
    · have hu : C.upper t = (q : ℤ) - 1 := by omega
      exact hnot (hu ▸ max'_mem _ _)
  simp [holeCount, he]

private lemma holes_bound (j : ℤ) (hj : |j| < (q : ℤ)) :
    0 ≤ C.holeCount j ∧ C.holeCount j ≤ |j| := by
  have hc : C.spanCount j ≤ (q : ℤ) := by
    have h := card_le_card (filter_subset (fun t => C.lower t ≤ j ∧ j ≤ C.upper t)
      (univ : Finset (Fin q)))
    simpa [spanCount, spanning] using (Int.ofNat_le.mpr h)
  have hb := C.span_balance j hj
  exact ⟨Int.natCast_nonneg _, by omega⟩

private lemma gap_double_count :
    C.totalGap = ∑ j ∈ Icc (1 - (q : ℤ)) ((q : ℤ) - 1), C.holeCount j := by
  classical
  let J := Icc (1 - (q : ℤ)) ((q : ℤ) - 1)
  have ht (t : Fin q) : C.gap t = ∑ j ∈ J, if j ∈ C.gaps t then (1 : ℤ) else 0 := by
    rw [C.gap_card]
    have hs : C.gaps t ⊆ J := by
      intro j hj
      have hspan := mem_Icc.mp (mem_sdiff.mp hj).1
      have hb := C.endpoints t
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    rw [← sum_filter]
    have he : J.filter (· ∈ C.gaps t) = C.gaps t := filter_mem_eq_of_subset hs
    simp [he]
  have hj (j : ℤ) : C.holeCount j = ∑ t : Fin q,
      if j ∈ C.gaps t then (1 : ℤ) else 0 := by
    have he : C.missing j = univ.filter (j ∈ C.gaps ·) := by
      ext t
      simp [missing, spanning, gaps, and_assoc]
    simp [holeCount, he]
  simp_rw [totalGap, ht]
  rw [sum_comm]
  exact sum_congr rfl (fun j _ => (hj j).symm)

private lemma negative_step (j : ℤ) (hj : j ≤ 0) :
    C.spanCount j = C.spanCount (j - 1) + C.starts j := by
  classical
  have he : (C.spanning j).filter (C.lower · ≠ j) = C.spanning (j - 1) := by
    ext t
    have hb := C.endpoints t
    simp only [spanning, mem_filter, mem_univ, true_and]
    omega
  have ha : (C.spanning j).filter (C.lower · = j) = univ.filter (C.lower · = j) := by
    ext t
    have hb := C.endpoints t
    simp only [spanning, mem_filter, mem_univ, true_and]
    omega
  have h := card_filter_add_card_filter_not (s := C.spanning j) (fun t => C.lower t = j)
  rw [he, ha] at h
  dsimp [spanCount, starts]
  exact_mod_cast (by omega : (C.spanning j).card =
    (C.spanning (j - 1)).card + (univ.filter (C.lower · = j)).card)

private lemma positive_step (j : ℤ) (hj : 0 ≤ j) :
    C.spanCount j = C.spanCount (j + 1) + C.ends j := by
  classical
  have he : (C.spanning j).filter (C.upper · ≠ j) = C.spanning (j + 1) := by
    ext t
    have hb := C.endpoints t
    simp only [spanning, mem_filter, mem_univ, true_and]
    omega
  have ha : (C.spanning j).filter (C.upper · = j) = univ.filter (C.upper · = j) := by
    ext t
    have hb := C.endpoints t
    simp only [spanning, mem_filter, mem_univ, true_and]
    omega
  have h := card_filter_add_card_filter_not (s := C.spanning j) (fun t => C.upper t = j)
  rw [he, ha] at h
  dsimp [spanCount, ends]
  exact_mod_cast (by omega : (C.spanning j).card =
    (C.spanning (j + 1)).card + (univ.filter (C.upper · = j)).card)

private lemma outside_span (j : ℤ) (hj : j < 1 - (q : ℤ) ∨ (q : ℤ) - 1 < j) :
    C.spanCount j = 0 := by
  classical
  have he : C.spanning j = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hs := (mem_filter.mp ht).2
    have hb := C.endpoints t
    omega
  simp [spanCount, he]

private lemma negative_balance (j : ℤ)
    (hj : 1 - (q : ℤ) ≤ j ∧ j ≤ 0) :
    C.starts j = 1 + C.holeCount j - C.holeCount (j - 1) := by
  have h := C.negative_step j hj.2
  have hjq : |j| < (q : ℤ) := by rw [abs_of_nonpos hj.2]; omega
  rw [C.span_balance j hjq] at h
  by_cases he : j = 1 - (q : ℤ)
  · have hprev : j - 1 < 1 - (q : ℤ) := by omega
    rw [C.outside_span (j - 1) (Or.inl hprev)] at h
    rw [C.holes_support (j - 1) (Or.inl hprev)]
    rw [abs_of_nonpos hj.2] at h
    omega
  · have hp : |j - 1| < (q : ℤ) := by rw [abs_of_nonpos (by omega)]; omega
    rw [C.span_balance (j - 1) hp, abs_of_nonpos hj.2,
      abs_of_nonpos (by omega : j - 1 ≤ 0)] at h
    omega

private lemma positive_balance (j : ℤ)
    (hj : 0 ≤ j ∧ j ≤ (q : ℤ) - 1) :
    C.ends j = 1 + C.holeCount j - C.holeCount (j + 1) := by
  have h := C.positive_step j hj.1
  have hjq : |j| < (q : ℤ) := by rw [abs_of_nonneg hj.1]; omega
  rw [C.span_balance j hjq] at h
  by_cases he : j = (q : ℤ) - 1
  · have hnext : (q : ℤ) - 1 < j + 1 := by omega
    rw [C.outside_span (j + 1) (Or.inr hnext)] at h
    rw [C.holes_support (j + 1) (Or.inr hnext)]
    rw [abs_of_nonneg hj.1] at h
    omega
  · have hp : |j + 1| < (q : ℤ) := by rw [abs_of_nonneg (by omega)]; omega
    rw [C.span_balance (j + 1) hp, abs_of_nonneg hj.1,
      abs_of_nonneg (by omega : 0 ≤ j + 1)] at h
    omega

private lemma cumulative_ends (k : ℤ) (hk : 0 < k ∧ k < (q : ℤ)) :
    ((univ.filter (fun t : Fin q => C.upper t < k)).card : ℤ) = k - C.holeCount k := by
  classical
  have he : univ.filter (fun t => ¬ C.upper t < k) = C.spanning k := by
    ext t
    have hb := C.endpoints t
    simp only [spanning, mem_filter, mem_univ, true_and]
    omega
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin q)))
    (fun t => C.upper t < k)
  rw [he] at h
  have hb := C.span_balance k (by rw [abs_of_pos hk.1]; exact hk.2)
  simp only [card_univ, Fintype.card_fin] at h
  dsimp [spanCount] at hb
  have hc : ((univ.filter (fun t : Fin q => C.upper t < k)).card : ℤ) +
      ((C.spanning k).card : ℤ) = q := by exact_mod_cast h
  rw [abs_of_pos hk.1] at hb
  omega

private lemma cumulative_starts (k : ℤ) (hk : 0 < k ∧ k < (q : ℤ)) :
    ((univ.filter (fun t : Fin q => -C.lower t < k)).card : ℤ) = k - C.holeCount (-k) := by
  classical
  have he : univ.filter (fun t => ¬ -C.lower t < k) = C.spanning (-k) := by
    ext t
    have hb := C.endpoints t
    simp only [spanning, mem_filter, mem_univ, true_and]
    omega
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin q)))
    (fun t => -C.lower t < k)
  rw [he] at h
  have hb := C.span_balance (-k) (by rw [abs_neg, abs_of_pos hk.1]; exact hk.2)
  simp only [card_univ, Fintype.card_fin] at h
  dsimp [spanCount] at hb
  have hc : ((univ.filter (fun t : Fin q => -C.lower t < k)).card : ℤ) +
      ((C.spanning (-k)).card : ℤ) = q := by exact_mod_cast h
  rw [abs_neg, abs_of_pos hk.1] at hb
  omega

/-- Complete span, missing-membership and endpoint accounting. No monotonicity,
uniform class size or prescribed defect allocation is required. The finite
hole sum is the all-integer sum, since holes vanish outside its interval. -/
theorem complete_span_endpoint_balance :
    (∀ j : ℤ, |j| < (q : ℤ) →
      C.spanCount j = (q : ℤ) - |j| + C.holeCount j) ∧
    C.holeCount 0 = 0 ∧ C.holeCount (1 - (q : ℤ)) = 0 ∧
    C.holeCount ((q : ℤ) - 1) = 0 ∧
    (∀ j : ℤ, |j| < (q : ℤ) → 0 ≤ C.holeCount j ∧ C.holeCount j ≤ |j|) ∧
    (∀ j : ℤ, j < 1 - (q : ℤ) ∨ (q : ℤ) - 1 < j → C.holeCount j = 0) ∧
    C.totalGap = (∑ j ∈ Icc (1 - (q : ℤ)) ((q : ℤ) - 1), C.holeCount j) ∧
    (∀ j : ℤ, 1 - (q : ℤ) ≤ j ∧ j ≤ 0 →
      C.starts j = 1 + C.holeCount j - C.holeCount (j - 1)) ∧
    (∀ j : ℤ, 0 ≤ j ∧ j ≤ (q : ℤ) - 1 →
      C.ends j = 1 + C.holeCount j - C.holeCount (j + 1)) ∧
    (∀ t : Fin q, C.upper t - C.lower t = 18 - C.defect t + C.gap t) ∧
    (∑ t : Fin q, (C.upper t - C.lower t)) = (q : ℤ) * ((q : ℤ) - 1) + C.totalGap ∧
    (∀ k : ℤ, 0 < k ∧ k < (q : ℤ) →
      ((univ.filter (fun t : Fin q => C.upper t < k)).card : ℤ) = k - C.holeCount k ∧
      ((univ.filter (fun t : Fin q => -C.lower t < k)).card : ℤ) = k - C.holeCount (-k)) := by
  classical
  refine ⟨C.span_balance, C.boundary_holes 0 (Or.inl rfl),
    C.boundary_holes _ (Or.inr (Or.inl rfl)),
    C.boundary_holes _ (Or.inr (Or.inr rfl)), C.holes_bound, C.holes_support,
    C.gap_double_count, C.negative_balance, C.positive_balance, ?_, ?_, ?_⟩
  · intro t
    dsimp [defect, gap]
    ring
  · have he (t : Fin q) : C.upper t - C.lower t = C.size t - 1 + C.gap t := by
      dsimp [gap]
      ring
    simp_rw [he]
    rw [sum_add_distrib, sum_sub_distrib, C.total_size]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    dsimp [totalGap]
    ring
  · intro k hk
    exact ⟨C.cumulative_ends k hk, C.cumulative_starts k hk⟩

end

end Cover

end D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance

open D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance in
#print axioms Cover.complete_span_endpoint_balance
