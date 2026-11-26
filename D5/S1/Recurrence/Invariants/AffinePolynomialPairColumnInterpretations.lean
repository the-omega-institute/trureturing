/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Chebyshev]
   utility: none
   digest: Subset, queens, Chebyshev and order-polytope interpretations of h_d. -/

import D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialColumnFamily
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Group.Abs

/-! Combinatorial and Chebyshev interpretations of the binomial column family `h_d`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairColumnInterpretations

open Finset
open D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialColumnFamily

section Chebyshev
open Polynomial Polynomial.Chebyshev

private theorem h_succ_succ (r m : ℕ) : h (r + 1) (m + 1) = h r (m + 1) + h (r + 1) m := by
  rw [result.2.1 r (m + 1), result.2.1 r m, sum_range_succ]; ring

private theorem h_zero (r : ℕ) (hr : 1 ≤ r) : h (r + 1) 0 = 1 := by
  rw [(result.1 (r + 1) 0 (by omega)).1]
  simp [Nat.choose_eq_zero_of_lt (show r - 1 < r by omega)]

private theorem h_two (m : ℕ) : h 2 m = 2 * m + 1 := by
  rw [(result.1 2 m le_rfl).1]; simp; ring

private theorem T_coeff_rec (n k : ℕ) : (T ℤ ((n + 2 : ℕ) : ℤ)).coeff (k + 1) =
    2 * (T ℤ ((n + 1 : ℕ) : ℤ)).coeff k - (T ℤ (n : ℤ)).coeff (k + 1) := by
  rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring, T_add_two,
    show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, coeff_sub, mul_assoc,
    coeff_ofNat_mul, coeff_X_mul]

private theorem T_coeff_zero (m : ℕ) : (T ℤ ((0 + 2 * m : ℕ) : ℤ)).coeff 0 = (-1) ^ m := by
  rw [coeff_zero_eq_eval_zero, show ((0 + 2 * m : ℕ) : ℤ) = 2 * (m : ℤ) by push_cast; ring,
    T_eval_two_mul_zero]
  simp [Int.negOnePow_def]

private theorem cheb (m r : ℕ) (hr : 1 ≤ r) :
    (T ℤ ((r + 2 * m : ℕ) : ℤ)).coeff r = (-1) ^ m * 2 ^ (r - 1) * h (r + 1) m := by
  induction m generalizing r with
  | zero =>
    have := leadingCoeff_T ℤ (r : ℤ)
    rw [leadingCoeff, natDegree_T] at this
    simp only [Int.natAbs_natCast] at this
    simp [this, h_zero r hr]
  | succ m ihm =>
    induction r with
    | zero => omega
    | succ r ihr =>
      rw [show r + 1 + 2 * (m + 1) = (r + 2 * m + 1) + 2 by ring, T_coeff_rec,
        show r + 2 * m + 1 + 1 = r + 2 * (m + 1) by ring,
        show r + 2 * m + 1 = (r + 1) + 2 * m by ring, ihm (r + 1) (by omega)]
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · rw [T_coeff_zero, h_two, h_two]
        push_cast; ring
      · rw [ihr hr0, h_succ_succ (r + 1) m, show r + 1 - 1 = (r - 1) + 1 by omega, pow_succ]
        ring

end Chebyshev

section Subsets
open PowerSeries

private theorem h_diff (d m : ℕ) (hm : 2 ≤ m + d) :
    h d m = ((m + d).choose d : ℤ) - (m + d - 2).choose d := by
  have hg : (1 + X : ℤ⟦X⟧) * (invOneSubPow ℤ d).val =
      (invOneSubPow ℤ (d + 1)).val - X ^ 2 * (invOneSubPow ℤ (d + 1)).val := by
    rw [← one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val (S := ℤ) (d := d) 1]
    ring
  rw [h, hg, map_sub, coeff_X_pow_mul', invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]
  split_ifs with h2
  · rw [coeff_mk, show d + m = m + d by ring, show d + (m - 2) = m + d - 2 by omega]
  · rw [Nat.choose_eq_zero_of_lt (show m + d - 2 < d by omega), show d + m = m + d by ring]
    simp

private theorem subsets {α : Type*} [DecidableEq α] (d m : ℕ) (X Y Z : Finset α)
    (hY : Y ⊆ X) (hZ : Z ⊆ X) (hX : X.card = m + d) (hYc : Y.card = 2) :
    (((X.powersetCard d).filter (fun S => (S ∩ Y).Nonempty ∧ (S ∩ Z).Nonempty)).card : ℤ) =
      h d m ↔ d = 0 ∨ m < Z.card ∨ Y ⊆ Z := by
  have hmd : 2 ≤ m + d := by have := card_le_card hY; omega
  have h2 : (X.powersetCard d).filter (fun S => ¬ (S ∩ Y).Nonempty) = (X \ Y).powersetCard d := by
    ext S
    simp only [mem_filter, mem_powersetCard, not_nonempty_iff_eq_empty, subset_sdiff]
    constructor
    · rintro ⟨⟨hS, hc⟩, he⟩
      exact ⟨⟨hS, disjoint_iff_inter_eq_empty.2 he⟩, hc⟩
    · rintro ⟨⟨hS, hdis⟩, hc⟩
      exact ⟨⟨hS, hc⟩, disjoint_iff_inter_eq_empty.1 hdis⟩
  have h3 := card_filter_add_card_filter_not (s := X.powersetCard d) (fun S => (S ∩ Y).Nonempty)
  rw [h2, card_powersetCard, card_powersetCard, card_sdiff_of_subset hY, hX, hYc] at h3
  have hYcount : (((X.powersetCard d).filter (fun S => (S ∩ Y).Nonempty)).card : ℤ) = h d m := by
    rw [h_diff d m hmd]; omega
  have hsub : (X.powersetCard d).filter (fun S => (S ∩ Y).Nonempty ∧ (S ∩ Z).Nonempty) ⊆
      (X.powersetCard d).filter (fun S => (S ∩ Y).Nonempty) :=
    fun S hS => by
      simp only [mem_filter] at hS ⊢
      exact ⟨hS.1, hS.2.1⟩
  constructor
  · intro heq
    by_contra hne
    push Not at hne
    obtain ⟨hd, hZc, hYZ⟩ := hne
    obtain ⟨y, hyY, hyZ⟩ := not_subset.1 hYZ
    have hyX : y ∈ X \ Z := mem_sdiff.2 ⟨hY hyY, hyZ⟩
    obtain ⟨S, hyS, hSX, hSc⟩ := exists_subsuperset_card_eq (s := {y}) (t := X \ Z) (n := d)
      (singleton_subset_iff.2 hyX) (by simp; omega)
      (by rw [card_sdiff_of_subset hZ]; omega)
    have hSmem : S ∈ (X.powersetCard d).filter (fun S => (S ∩ Y).Nonempty) :=
      mem_filter.2 ⟨mem_powersetCard.2 ⟨hSX.trans sdiff_subset, hSc⟩,
        ⟨y, mem_inter.2 ⟨singleton_subset_iff.1 hyS, hyY⟩⟩⟩
    have hSnot : S ∉ (X.powersetCard d).filter (fun S => (S ∩ Y).Nonempty ∧ (S ∩ Z).Nonempty) := by
      intro hm
      obtain ⟨z, hz⟩ := (mem_filter.1 hm).2.2
      exact (mem_sdiff.1 (hSX (mem_inter.1 hz).1)).2 (mem_inter.1 hz).2
    have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun he => hSnot (he ▸ hSmem)⟩)
    have : (((X.powersetCard d).filter
        (fun S => (S ∩ Y).Nonempty ∧ (S ∩ Z).Nonempty)).card : ℤ) <
        (((X.powersetCard d).filter (fun S => (S ∩ Y).Nonempty)).card : ℤ) := by exact_mod_cast hlt
    omega
  · intro hcase
    rw [← hYcount]
    congr 2
    refine filter_congr fun S hS => ⟨fun h => h.1, fun hYS => ⟨hYS, ?_⟩⟩
    rcases hcase with rfl | hZc | hYZ
    · obtain ⟨y, hy⟩ := hYS
      rw [mem_powersetCard] at hS
      rw [card_eq_zero.1 hS.2] at hy; simp at hy
    · rw [mem_powersetCard] at hS
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have hsub2 : S ⊆ X \ Z := fun x hx => mem_sdiff.2 ⟨hS.1 hx, fun hz => by
        have : x ∈ S ∩ Z := mem_inter.2 ⟨hx, hz⟩
        rw [hne] at this; simp at this⟩
      have := card_le_card hsub2
      have hpos : 0 < S.card := by
        obtain ⟨y, hy⟩ := hYS
        exact card_pos.2 ⟨y, (mem_inter.1 hy).1⟩
      rw [card_sdiff_of_subset hZ, hX] at this
      omega
    · obtain ⟨y, hy⟩ := hYS
      exact ⟨y, mem_inter.2 ⟨(mem_inter.1 hy).1, hYZ (mem_inter.1 hy).2⟩⟩

end Subsets

section ChebyshevIff
open Polynomial Polynomial.Chebyshev

private theorem h_one_zero : h 1 0 = 1 := by
  rw [AffinePolynomialPairBinomialColumnFamily.result.2.1 0 0]
  simp [h, PowerSeries.invOneSubPow_zero]

private theorem h_one_succ (m : ℕ) : h 1 (m + 1) = 2 := by
  rw [h_diff 1 (m + 1) (by omega), show m + 1 + 1 - 2 = m by omega, Nat.choose_one_right,
    Nat.choose_one_right]
  push_cast; ring

private theorem cheb_iff (r m : ℕ) :
    2 * (T ℤ ((r + 2 * m : ℕ) : ℤ)).coeff r = (-1) ^ m * 2 ^ r * h (r + 1) m ↔ 1 ≤ r ∨ 1 ≤ m := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [h_one_zero]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [T_coeff_zero, h_one_succ]
      simp only [pow_zero, mul_one]
      constructor
      · intro _; omega
      · intro _; ring
  · rw [cheb m r hr, show r = (r - 1) + 1 by omega, pow_succ]
    simp only [show r - 1 + 1 - 1 = r - 1 by omega]
    constructor
    · intro _; omega
    · intro _; ring

end ChebyshevIff

section OrderPolytope

/-- Lattice points of the `m`-th dilation of the order polytope of a chain of `k` elements below
two incomparable elements: order-preserving labelings by `{0, …, m}`, written as the labels of the
chain together with the labels of the two upper elements. -/
def orderPolytopePoints (k m : ℕ) : Finset ((Fin k → Fin (m + 1)) × Fin (m + 1) × Fin (m + 1)) :=
  univ.filter (fun x => Monotone x.1 ∧ ∀ i, x.1 i ≤ x.2.1 ∧ x.1 i ≤ x.2.2)

private theorem mono_snoc {X : Type*} [PartialOrder X] {k : ℕ} (g : Fin k → X) (s : X) :
    Monotone (Fin.snoc g s : Fin (k + 1) → X) ↔ Monotone g ∧ ∀ i, g i ≤ s := by
  constructor
  · intro hm
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := hm (Fin.castSucc_le_castSucc_iff.2 hij); simpa using this
    · have := hm (Fin.castSucc_lt_last i).le; simpa using this
  · rintro ⟨hg, hs⟩ i j hij
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => exact le_rfl
      | cast i => simpa using hs i
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_le.2 (Fin.castSucc_lt_last j))
      | cast i => simpa using hg (Fin.castSucc_le_castSucc_iff.1 hij)

private def A (k m t : ℕ) : ℕ :=
  ((univ : Finset (Fin k → Fin (m + 1))).filter (fun g => Monotone g ∧ ∀ i, (g i).val ≤ t)).card

private theorem A_succ (k m t : ℕ) (ht : t ≤ m) : A (k + 1) m t = ∑ s ∈ range (t + 1), A k m s := by
  unfold A
  rw [card_equiv (Fin.snocEquiv (fun _ => Fin (m + 1))).symm
    (t := univ.filter (fun p : Fin (m + 1) × (Fin k → Fin (m + 1)) =>
      (Monotone p.2 ∧ ∀ i, (p.2 i).val ≤ p.1.val) ∧ p.1.val ≤ t))]
  · rw [card_filter, Fintype.sum_prod_type]
    rw [Fin.sum_univ_eq_sum_range (fun s => ∑ g : Fin k → Fin (m + 1),
      if (Monotone g ∧ ∀ i, (g i).val ≤ s) ∧ s ≤ t then 1 else 0) (m + 1)]
    · have : range (t + 1) = (range (m + 1)).filter (· ≤ t) := by
        ext s; simp; omega
      rw [this, sum_filter]
      refine sum_congr rfl fun s _ => ?_
      by_cases hst : s ≤ t
      · simp only [hst, and_true, ite_true]
        rw [card_filter]
      · simp [hst]
  · intro g
    simp only [mem_filter, mem_univ, true_and, Fin.snocEquiv_symm_apply]
    rw [← Fin.snoc_init_self g, mono_snoc]
    simp only [Fin.snoc_init_self, Fin.init]
    constructor
    · rintro ⟨⟨hm, hle⟩, hall⟩
      exact ⟨⟨hm, fun i => hle i⟩, hall (Fin.last k)⟩
    · rintro ⟨⟨hm, hle⟩, hlast⟩
      refine ⟨⟨hm, hle⟩, fun i => ?_⟩
      induction i using Fin.lastCases with
      | last => exact hlast
      | cast i => exact le_trans (hle i) hlast

private theorem A_closed (k m t : ℕ) (ht : t ≤ m) : A k m t = (t + k).choose k := by
  induction k generalizing t with
  | zero =>
    have hm : ∀ g : Fin 0 → Fin (m + 1), Monotone g := fun g i => i.elim0
    unfold A
    simp [hm]
  | succ k ih =>
    rw [A_succ k m t ht, sum_congr rfl fun s hs => ih s (by simp at hs; omega),
      Nat.sum_range_add_choose]
    ring_nf

private theorem card_points (k m : ℕ) : (orderPolytopePoints k m).card =
    ∑ u ∈ range (m + 1), ∑ w ∈ range (m + 1), (min u w + k).choose k := by
  unfold orderPolytopePoints
  rw [card_filter, Fintype.sum_prod_type, sum_comm, Fintype.sum_prod_type]
  dsimp only
  have inner : ∀ u w : Fin (m + 1), (∑ g : Fin k → Fin (m + 1),
      if Monotone g ∧ ∀ i, g i ≤ u ∧ g i ≤ w then 1 else 0) = (min u.val w.val + k).choose k := by
    intro u w
    rw [← A_closed k m (min u.val w.val) (by omega), A, card_filter]
    refine sum_congr rfl fun g _ => ?_
    simp only [Fin.le_def, le_min_iff]
  rw [sum_congr rfl fun u _ => sum_congr rfl fun w _ => inner u w,
    Fin.sum_univ_eq_sum_range (fun u => ∑ w : Fin (m + 1), (min u w.val + k).choose k) (m + 1)]
  exact sum_congr rfl fun u _ =>
    Fin.sum_univ_eq_sum_range (fun w => (min u w + k).choose k) (m + 1)

private theorem double_sum_eq (k m : ℕ) :
    ((∑ u ∈ range (m + 1), ∑ w ∈ range (m + 1), (min u w + k).choose k : ℕ) : ℤ) = h (k + 3) m := by
  induction m with
  | zero => simp [h_zero (k + 2) (by omega)]
  | succ m ih =>
    have hrow : ∀ u ∈ range (m + 1), ∑ w ∈ range (m + 1 + 1), (min u w + k).choose k =
        ∑ w ∈ range (m + 1), (min u w + k).choose k + (u + k).choose k := by
      intro u hu
      rw [sum_range_succ, min_eq_left (by simp at hu; omega)]
    have hlast : ∑ w ∈ range (m + 1 + 1), (min (m + 1) w + k).choose k =
        ∑ w ∈ range (m + 1), (w + k).choose k + (m + 1 + k).choose k := by
      rw [sum_range_succ, min_self]
      congr 1
      exact sum_congr rfl fun w hw => by rw [min_eq_right (by simp at hw; omega)]
    rw [sum_range_succ, sum_congr rfl hrow, sum_add_distrib, hlast, Nat.sum_range_add_choose,
      Nat.cast_add, Nat.cast_add, ih]
    push_cast
    rw [show k + 3 = (k + 2) + 1 by ring, h_succ_succ (k + 2) m,
      (result.1 (k + 2) (m + 1) (by omega)).1,
      show m + 1 + (k + 2) - 1 = (m + k + 1) + 1 by omega, show m + 1 + (k + 2) - 2 = m + k + 1 by omega,
      show k + 2 - 1 = k + 1 by omega, Nat.choose_succ_succ (m + k + 1) k, Nat.succ_eq_add_one,
      show m + 1 + k = m + k + 1 by ring]
    push_cast
    ring

end OrderPolytope

section Queens

/-- Cells `(row, column)` of an `n × n` board. -/
def cells (n : ℕ) : Finset (ℕ × ℕ) := range n ×ˢ range n

private def line (n t : ℕ) : Finset (ℕ × ℕ) := (cells n).filter (fun p => p.2 + n = p.1 + t)

private theorem card_line_le (n t : ℕ) (ht : t ≤ n) : (line n t).card = t := by
  have : line n t = (range t).image (fun c => (c + (n - t), c)) := by
    ext ⟨r, c⟩
    simp only [line, cells, mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hr, hc⟩, he⟩; exact ⟨c, by omega, by omega, rfl⟩
    · rintro ⟨c', hc', rfl, rfl⟩; omega
  rw [this, card_image_of_injective _ (fun a b hab => by simp only [Prod.mk.injEq] at hab; exact hab.2),
    card_range]

private theorem card_line_ge (n t : ℕ) (ht : n ≤ t) : (line n t).card = 2 * n - t := by
  have : line n t = (range (2 * n - t)).image (fun r => (r, r + (t - n))) := by
    ext ⟨r, c⟩
    simp only [line, cells, mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hr, hc⟩, he⟩; exact ⟨r, by omega, rfl, by omega⟩
    · rintro ⟨r', hr', rfl, rfl⟩; omega
  rw [this, card_image_of_injective _ (fun a b hab => by simp only [Prod.mk.injEq] at hab; exact hab.1),
    card_range]

private theorem sum_range_choose' (n k : ℕ) : ∑ t ∈ range n, t.choose k = n.choose (k + 1) := by
  rcases Nat.lt_or_ge k n with hkn | hkn
  · obtain ⟨j, rfl⟩ : ∃ j, n = k + (j + 1) := ⟨n - k - 1, by omega⟩
    rw [sum_range_add, sum_eq_zero fun t ht => Nat.choose_eq_zero_of_lt (by simpa using ht),
      zero_add, sum_congr rfl fun t _ => by rw [add_comm k t], Nat.sum_range_add_choose]
    congr 1; ring
  · rw [sum_eq_zero fun t ht => Nat.choose_eq_zero_of_lt (by simp at ht; omega),
      Nat.choose_eq_zero_of_lt (by omega)]

private theorem sum_lines (n k : ℕ) (hk : 1 ≤ k) :
    ∑ t ∈ range (2 * n), (line n t).card.choose k = n.choose (k + 1) + (n + 1).choose (k + 1) := by
  rw [show 2 * n = n + n by ring, sum_range_add]
  have e1 : ∑ t ∈ range n, (line n t).card.choose k = ∑ t ∈ range n, t.choose k :=
    sum_congr rfl fun t ht => by rw [card_line_le n t (by simp at ht; omega)]
  have e2 : ∑ t ∈ range n, (line n (n + t)).card.choose k = ∑ t ∈ range n, (n - t).choose k :=
    sum_congr rfl fun t ht => by rw [card_line_ge n (n + t) (by omega)]; congr 1; omega
  have e3 : ∑ t ∈ range n, (n - t).choose k = ∑ t ∈ range n, (t + 1).choose k := by
    rw [← sum_range_reflect]
    exact sum_congr rfl fun t ht => by simp at ht; congr 1; omega
  have e4 : ∑ t ∈ range n, (t + 1).choose k = (n + 1).choose (k + 1) := by
    rw [← sum_range_choose' (n + 1) k, sum_range_succ' (fun t => t.choose k),
      Nat.choose_eq_zero_of_lt (show 0 < k by omega), add_zero]
  rw [e1, e2, e3, e4, sum_range_choose']

private def mainSets (n k : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((cells n).powersetCard k).filter (fun S => ∀ p ∈ S, ∀ q ∈ S, p.2 + q.1 = q.2 + p.1)

private def antiSets (n k : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((cells n).powersetCard k).filter (fun S => ∀ p ∈ S, ∀ q ∈ S, p.1 + p.2 = q.1 + q.2)

private theorem mainSets_eq (n k : ℕ) (hk : 1 ≤ k) :
    mainSets n k = (range (2 * n)).biUnion (fun t => (line n t).powersetCard k) := by
  ext S
  simp only [mainSets, mem_filter, mem_powersetCard, mem_biUnion, mem_range]
  constructor
  · rintro ⟨⟨hS, hc⟩, hm⟩
    obtain ⟨p, hp⟩ : S.Nonempty := card_pos.1 (by omega)
    have hpc := hS hp
    simp only [cells, mem_product, mem_range] at hpc
    refine ⟨p.2 + n - p.1, by omega, fun q hq => ?_, hc⟩
    have hqc := hS hq
    have := hm p hp q hq
    simp only [line, mem_filter]
    exact ⟨hqc, by simp only [cells, mem_product, mem_range] at hqc; omega⟩
  · rintro ⟨t, -, hS, hc⟩
    refine ⟨⟨fun x hx => (mem_filter.1 (hS hx)).1, hc⟩, fun p hp q hq => ?_⟩
    have h1 := (mem_filter.1 (hS hp)).2
    have h2 := (mem_filter.1 (hS hq)).2
    omega

private theorem card_mainSets (n k : ℕ) (hk : 1 ≤ k) :
    (mainSets n k).card = n.choose (k + 1) + (n + 1).choose (k + 1) := by
  rw [mainSets_eq n k hk, card_biUnion]
  · simp only [card_powersetCard]
    exact sum_lines n k hk
  · intro t _ t' _ htt'
    rw [Function.onFun, disjoint_left]
    intro S hS hS'
    rw [mem_powersetCard] at hS hS'
    obtain ⟨p, hp⟩ : S.Nonempty := card_pos.1 (by omega)
    have h1 := (mem_filter.1 (hS.1 hp)).2
    have h2 := (mem_filter.1 (hS'.1 hp)).2
    omega

private def flipCol (n : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1, n - 1 - p.2)

private theorem flipCol_flipCol (n : ℕ) (p : ℕ × ℕ) (hp : p ∈ cells n) : flipCol n (flipCol n p) = p := by
  simp only [cells, mem_product, mem_range] at hp
  refine Prod.ext rfl ?_
  simp only [flipCol]
  omega

private theorem flipCol_mem (n : ℕ) (p : ℕ × ℕ) (hp : p ∈ cells n) : flipCol n p ∈ cells n := by
  simp only [cells, mem_product, mem_range] at hp ⊢
  simp only [flipCol]
  omega

private theorem image_flipCol_image_flipCol (n : ℕ) (S : Finset (ℕ × ℕ)) (hS : S ⊆ cells n) :
    (S.image (flipCol n)).image (flipCol n) = S := by
  rw [image_image]
  conv_rhs => rw [← image_id (s := S)]
  exact image_congr fun p hp => flipCol_flipCol n p (hS hp)

private theorem card_antiSets (n k : ℕ) : (antiSets n k).card = (mainSets n k).card := by
  have key : ∀ S ⊆ cells n, ∀ (P : (ℕ × ℕ) → (ℕ × ℕ) → Prop) (Q : (ℕ × ℕ) → (ℕ × ℕ) → Prop),
      (∀ p ∈ cells n, ∀ q ∈ cells n, P p q ↔ Q (flipCol n p) (flipCol n q)) →
      ((∀ p ∈ S, ∀ q ∈ S, P p q) ↔ ∀ p ∈ S.image (flipCol n), ∀ q ∈ S.image (flipCol n), Q p q) := by
    intro S hS P Q hPQ
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact ⟨fun h p hp q hq => (hPQ p (hS hp) q (hS hq)).1 (h p hp q hq),
      fun h p hp q hq => (hPQ p (hS hp) q (hS hq)).2 (h p hp q hq)⟩
  have hinj : ∀ S ⊆ cells n, (S.image (flipCol n)).card = S.card := fun S hS =>
    card_image_of_injOn fun p hp q hq hpq => by
      rw [← flipCol_flipCol n p (hS hp), ← flipCol_flipCol n q (hS hq), hpq]
  have himg : ∀ S ⊆ cells n, S.image (flipCol n) ⊆ cells n := fun S hS x hx => by
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
    exact flipCol_mem n p (hS hp)
  refine card_nbij' (fun S => S.image (flipCol n)) (fun S => S.image (flipCol n)) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [antiSets, mainSets, mem_coe, mem_filter, mem_powersetCard] at hS ⊢
    refine ⟨⟨himg S hS.1.1, by rw [hinj S hS.1.1, hS.1.2]⟩, ?_⟩
    refine (key S hS.1.1 _ _ fun p hp q hq => ?_).1 hS.2
    simp only [cells, mem_product, mem_range] at hp hq
    simp only [flipCol]
    omega
  · intro S hS
    simp only [antiSets, mainSets, mem_coe, mem_filter, mem_powersetCard] at hS ⊢
    refine ⟨⟨himg S hS.1.1, by rw [hinj S hS.1.1, hS.1.2]⟩, ?_⟩
    refine (key S hS.1.1 _ _ fun p hp q hq => ?_).1 hS.2
    simp only [cells, mem_product, mem_range] at hp hq
    simp only [flipCol]
    omega
  · intro S hS
    simp only [antiSets, mem_coe, mem_filter, mem_powersetCard] at hS
    exact image_flipCol_image_flipCol n S hS.1.1
  · intro S hS
    simp only [mainSets, mem_coe, mem_filter, mem_powersetCard] at hS
    exact image_flipCol_image_flipCol n S hS.1.1

/-- Placements of `k` queens on an `n × n` board in distinct rows and columns, every pair attacking
diagonally. -/
def queenPlacements (n k : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((cells n).powersetCard k).filter (fun S => ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ |(p.1 : ℤ) - q.1| = |(p.2 : ℤ) - q.2|)

private theorem attack_iff (p q : ℕ × ℕ) : |(p.1 : ℤ) - q.1| = |(p.2 : ℤ) - q.2| ↔
    p.2 + q.1 = q.2 + p.1 ∨ p.1 + p.2 = q.1 + q.2 := by
  rw [abs_eq_abs]; omega

private theorem queens_eq (n k : ℕ) (hk : 2 ≤ k) : queenPlacements n k = mainSets n k ∪ antiSets n k := by
  ext S
  simp only [queenPlacements, mainSets, antiSets, mem_union, mem_filter]
  constructor
  · rintro ⟨hSc, hatt⟩
    have key : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        x.1 ≠ y.1 ∧ (x.2 + y.1 = y.2 + x.1 ∨ x.1 + x.2 = y.1 + y.2) := fun x hx y hy hxy =>
      ⟨(hatt x hx y hy hxy).1, (attack_iff x y).1 (hatt x hx y hy hxy).2.2⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.1 (by rw [(mem_powersetCard.1 hSc).2]; omega)
    have k0 := key p hp q hq hpq
    have via : ∀ x ∈ S,
        (p.2 + x.1 = x.2 + p.1 ∨ x.1 = p.1 ∧ x.2 = p.2) ∧
          (q.2 + x.1 = x.2 + q.1 ∨ x.1 = q.1 ∧ x.2 = q.2) ∨
        (p.1 + p.2 = x.1 + x.2 ∨ x.1 = p.1 ∧ x.2 = p.2) ∧
          (q.1 + q.2 = x.1 + x.2 ∨ x.1 = q.1 ∧ x.2 = q.2) := by
      intro x hx
      by_cases h1 : x = p
      · subst h1; rcases k0.2 with h | h <;> omega
      by_cases h2 : x = q
      · subst h2; rcases k0.2 with h | h <;> omega
      have k1 := key p hp x hx (Ne.symm h1)
      have k2 := key q hq x hx (Ne.symm h2)
      omega
    rcases k0.2 with hm | ha
    · refine Or.inl ⟨hSc, fun x hx y hy => ?_⟩
      have v1 := via x hx
      have v2 := via y hy
      omega
    · refine Or.inr ⟨hSc, fun x hx y hy => ?_⟩
      have v1 := via x hx
      have v2 := via y hy
      omega
  · have hne : ∀ p q : ℕ × ℕ, p ≠ q → p.1 ≠ q.1 ∨ p.2 ≠ q.2 := fun p q hpq => by
      by_contra h
      push Not at h
      exact hpq (Prod.ext h.1 h.2)
    rintro (⟨hSc, hm⟩ | ⟨hSc, ha⟩)
    · refine ⟨hSc, fun p hp q hq hpq => ?_⟩
      have := hm p hp q hq
      have h2 := hne p q hpq
      exact ⟨by omega, by omega, (attack_iff p q).2 (Or.inl this)⟩
    · refine ⟨hSc, fun p hp q hq hpq => ?_⟩
      have := ha p hp q hq
      have h2 := hne p q hpq
      exact ⟨by omega, by omega, (attack_iff p q).2 (Or.inr this)⟩

private theorem queens_disjoint (n k : ℕ) (hk : 2 ≤ k) : Disjoint (mainSets n k) (antiSets n k) := by
  rw [disjoint_left]
  intro S hM hA
  simp only [mainSets, antiSets, mem_filter, mem_powersetCard] at hM hA
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.1 (by rw [hM.1.2]; omega)
  have h1 := hM.2 p hp q hq
  have h2 := hA.2 p hp q hq
  exact hpq (Prod.ext (by omega) (by omega))

private theorem card_queens (n k : ℕ) (hk : 2 ≤ k) :
    (queenPlacements n k).card = 2 * (n.choose (k + 1) + (n + 1).choose (k + 1)) := by
  rw [queens_eq n k hk, card_union_of_disjoint (queens_disjoint n k hk), card_antiSets,
    card_mainSets n k (by omega)]
  ring

private theorem h_three (m : ℕ) : h 3 m = (m + 1) ^ 2 := by
  induction m with
  | zero => rw [h_zero 2 (by omega)]; ring
  | succ m ih => rw [h_succ_succ 2 m, h_two, ih]; push_cast; ring

private theorem queens_iff (d m : ℕ) :
    ((queenPlacements (m + d - 2) (d - 2)).card : ℤ) = 2 * h d m ↔ 4 ≤ d := by
  constructor
  · intro heq
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_or_ge d 3 with h2 | h3
    · have hzero : queenPlacements (m + d - 2) (d - 2) = {∅} := by
        rw [show d - 2 = 0 by omega, queenPlacements, powersetCard_zero]
        simp
      rw [hzero, card_singleton] at heq
      omega
    · have hd : d = 3 := by omega
      subst hd
      have hall : queenPlacements (m + 3 - 2) (3 - 2) = (cells (m + 1)).powersetCard 1 := by
        rw [show m + 3 - 2 = m + 1 by omega, show 3 - 2 = 1 by omega, queenPlacements]
        refine filter_true_of_mem fun S hS p hp q hq hpq => absurd ?_ hpq
        obtain ⟨a, rfl⟩ := card_eq_one.1 (mem_powersetCard.1 hS).2
        rw [mem_singleton] at hp hq
        rw [hp, hq]
      rw [hall, card_powersetCard, Nat.choose_one_right, cells, card_product, card_range,
        h_three] at heq
      push_cast at heq
      nlinarith
  · intro hd
    rw [card_queens _ _ (by omega),
      (AffinePolynomialPairBinomialColumnFamily.result.1 d m (by omega)).1,
      show m + d - 2 + 1 = m + d - 1 by omega, show d - 2 + 1 = d - 1 by omega]
    push_cast
    ring

end Queens

open Polynomial.Chebyshev in
/-- Corollary 8 of the Ma–Zhang note on A208509, for `h_d(m) = [z^m](1 + z)/(1 - z)^d`:
in a set `X` of size `m + d` with `Y ⊆ X` of size 2 and `Z ⊆ X`, the number of `d`-subsets of `X`
meeting both `Y` and `Z` equals `h_d(m)` exactly when `d = 0`, `m < |Z|` or `Y ⊆ Z`; there are
`2 h_d(m)` placements of `d - 2` pairwise diagonally attacking queens in distinct rows and columns of
an `(m + d - 2) × (m + d - 2)` board exactly when `d ≥ 4`; `2 [t^r] T_(r+2m)(t) = (-1)^m 2^r h_(r+1)(m)`
exactly when `(r, m) ≠ (0, 0)`; and the `m`-th dilation of the order polytope of a chain of `k` elements below two
incomparable elements has `h_(k+3)(m)` lattice points. -/
theorem result :
    (∀ {α : Type u} [DecidableEq α] (d m : ℕ) (X Y Z : Finset α), Y ⊆ X → Z ⊆ X →
      X.card = m + d → Y.card = 2 →
      ((((X.powersetCard d).filter (fun S => (S ∩ Y).Nonempty ∧ (S ∩ Z).Nonempty)).card : ℤ) =
        h d m ↔ d = 0 ∨ m < Z.card ∨ Y ⊆ Z)) ∧
    (∀ d m : ℕ, ((queenPlacements (m + d - 2) (d - 2)).card : ℤ) = 2 * h d m ↔ 4 ≤ d) ∧
    (∀ r m : ℕ,
      2 * (T ℤ ((r + 2 * m : ℕ) : ℤ)).coeff r = (-1) ^ m * 2 ^ r * h (r + 1) m ↔ 1 ≤ r ∨ 1 ≤ m) ∧
    (∀ k m : ℕ, ((orderPolytopePoints k m).card : ℤ) = h (k + 3) m) := by
  exact ⟨fun d m X Y Z hY hZ hX hYc => subsets d m X Y Z hY hZ hX hYc, queens_iff,
    cheb_iff, fun k m => by rw [card_points, double_sum_eq]⟩

end D5.S1.Recurrence.Invariants.AffinePolynomialPairColumnInterpretations
