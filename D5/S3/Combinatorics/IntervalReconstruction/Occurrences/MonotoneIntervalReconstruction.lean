/- GID: D5/S3/Combinatorics/IntervalReconstruction/Occurrences/MonotoneIntervalReconstruction
   generality: G
   mirror-B: none(waiver:covered-by-monotone-interval-reconstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unlabelled interval observations retain one occurrence for each pair of distinct endpoints. -/

module

public import OmegaBuild.Commands
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Linarith

/-!
Omega original.

Unlabelled interval observations retain one occurrence for each pair of distinct
endpoints. The reconstruction argument extends the extremal and residual method
of Hegyvári, Pach and Tang, Proposition 4.1, to nonnegative weakly increasing real
lists. No computational complexity statement is made.
-/

compile_only_with_mathlib

@[expose] public section

namespace Omega.MonotoneIntervalReconstruction

open Finset

/-- All inclusive index intervals with at least two entries. -/
def intervals (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range n).product (range n)).filter fun p => p.1 < p.2

/-- The inclusive sum on the actual index interval. -/
noncomputable def intervalSum (a : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  ∑ k ∈ Icc p.1 p.2, a k

/-- Mapping the endpoint set retains every interval occurrence, including ties. -/
noncomputable def observations (a : ℕ → ℝ) (n : ℕ) : Multiset ℝ :=
  (intervals n).val.map (intervalSum a)

private theorem mem_intervals {n i j : ℕ} :
    (i, j) ∈ intervals n ↔ i < j ∧ j < n := by
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    exact ⟨hp'.2, Finset.mem_range.mp (Finset.mem_product.mp hp'.1).2⟩
  · rintro ⟨hij,hjn⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (lt_trans hij hjn), Finset.mem_range.mpr hjn⟩, hij⟩

private theorem intervals_mono {n m : ℕ} (h : n ≤ m) : intervals n ⊆ intervals m := by
  rintro ⟨i,j⟩ hp
  rw [mem_intervals] at hp ⊢
  omega

private theorem intervals_card_lt {n m : ℕ} (hn : 1 ≤ n) (h : n < m) :
    (intervals n).card < (intervals m).card := by
  apply card_lt_card
  refine (ssubset_iff_subset_ne).mpr ⟨intervals_mono h.le, ?_⟩
  intro he
  have hp : (0,n) ∈ intervals m := mem_intervals.mpr (by omega)
  rw [← he, mem_intervals] at hp
  omega

/-- The number of observations determines every positive length. -/
theorem length_eq_of_observations_eq {a b : ℕ → ℝ} {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (h : observations a n = observations b m) : n = m := by
  have hc : (intervals n).card = (intervals m).card := by
    simpa [observations] using congrArg Multiset.card h
  rcases lt_trichotomy n m with hnm | he | hmn
  · exact False.elim ((ne_of_lt (intervals_card_lt hn hnm)) hc)
  · exact he
  · exact False.elim ((ne_of_lt (intervals_card_lt hm hmn)) hc.symm)

private theorem sum_le_full {a : ℕ → ℝ} {n i j : ℕ}
    (ha : ∀ k < n, 0 ≤ a k) (hj : j < n) :
    intervalSum a (i,j) ≤ intervalSum a (0,n-1) := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [mem_Icc] at hk ⊢
    omega
  · intro k hk _
    exact ha k (by have := (Finset.mem_Icc.mp hk).2; omega)

private theorem sum_add_missing_le {a : ℕ → ℝ} {n i j t : ℕ}
    (ha : ∀ k < n, 0 ≤ a k) (hj : j < n) (ht : t < n)
    (hout : t ∉ Icc i j) :
    intervalSum a (i,j) + a t ≤ intervalSum a (0,n-1) := by
  have hs : insert t (Icc i j) ⊆ Icc 0 (n-1) := by
    intro k hk
    simp only [mem_insert, mem_Icc] at hk ⊢
    omega
  have h := sum_le_sum_of_subset_of_nonneg hs
    (fun k hk _ => ha k (by have := (mem_Icc.mp hk).2; omega))
  simpa [intervalSum, sum_insert hout, add_comm] using h

private theorem adjacent_sum (a : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    intervalSum a (k-1,k) = a (k-1) + a k := by
  have hs : Icc (k-1) k = {k-1,k} := by
    ext j
    simp only [mem_Icc, mem_insert, mem_singleton]
    omega
  simp [intervalSum, hs, show k-1 ≠ k by omega]

private theorem boundary_le {a : ℕ → ℝ} {n i j k : ℕ}
    (ha : ∀ t < n, 0 ≤ a t)
    (hs : ∀ u v, u ≤ v → v < n → a u ≤ a v)
    (hi : i < j) (hj : j < n) (hk : 1 ≤ k) (hkj : k ≤ j) :
    a (k-1) + a k ≤ intervalSum a (i,j) := by
  have hp : {j-1,j} ⊆ Icc i j := by
    intro t ht
    simp only [mem_insert, mem_singleton, mem_Icc] at ht ⊢
    omega
  have h := sum_le_sum_of_subset_of_nonneg hp
    (fun t ht _ => ha t (by have := (mem_Icc.mp ht).2; omega))
  have hv : a (j-1) + a j ≤ intervalSum a (i,j) := by
    simpa [intervalSum, show j-1 ≠ j by omega] using h
  exact le_trans (add_le_add (hs _ _ (by omega) (by omega))
    (hs _ _ hkj hj)) hv

private theorem extrema_eq {s t : Multiset ℝ} {x y : ℝ}
    (he : s = t) (hx : x ∈ s) (hy : y ∈ t)
    (hs : ∀ z ∈ s, z ≤ x) (ht : ∀ z ∈ t, z ≤ y) : x = y :=
  le_antisymm (ht x (he ▸ hx)) (hs y (he.symm ▸ hy))

private theorem total_mem (a : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    intervalSum a (0,n-1) ∈ observations a n := by
  apply Multiset.mem_map.mpr
  exact ⟨(0,n-1), mem_intervals.mpr (by omega), rfl⟩

private theorem total_eq {a b : ℕ → ℝ} {n : ℕ}
    (hn : 2 ≤ n) (ha : ∀ k < n, 0 ≤ a k) (hb : ∀ k < n, 0 ≤ b k)
    (he : observations a n = observations b n) :
    intervalSum a (0,n-1) = intervalSum b (0,n-1) := by
  apply extrema_eq he (total_mem a hn) (total_mem b hn)
  · intro z hz
    obtain ⟨⟨i,j⟩, hp, rfl⟩ := Multiset.mem_map.mp hz
    exact sum_le_full ha (mem_intervals.mp hp).2
  · intro z hz
    obtain ⟨⟨i,j⟩, hp, rfl⟩ := Multiset.mem_map.mp hz
    exact sum_le_full hb (mem_intervals.mp hp).2

private noncomputable def properObservations (a : ℕ → ℝ) (n : ℕ) : Multiset ℝ :=
  ((intervals n).erase (0,n-1)).val.map (intervalSum a)

private theorem observations_cons_proper (a : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    observations a n = intervalSum a (0,n-1) ::ₘ properObservations a n := by
  have hp : (0,n-1) ∈ (intervals n).val := mem_intervals.mpr (by omega)
  simp only [observations, properObservations, Finset.erase_val]
  rw [← Multiset.map_cons, Multiset.cons_erase hp]

private theorem tail_total (a : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    a 0 + intervalSum a (1,n-1) = intervalSum a (0,n-1) := by
  have hs : insert 0 (Icc 1 (n-1)) = Icc 0 (n-1) := by
    ext k
    simp only [mem_insert, mem_Icc]
    omega
  have he := congrArg (fun s : Finset ℕ => ∑ k ∈ s, a k) hs
  simpa [intervalSum] using he

private theorem proper_max {a : ℕ → ℝ} {n : ℕ} (hn : 3 ≤ n)
    (ha : ∀ k < n, 0 ≤ a k)
    (hs : ∀ u v, u ≤ v → v < n → a u ≤ a v) :
    intervalSum a (1,n-1) ∈ properObservations a n ∧
      ∀ z ∈ properObservations a n, z ≤ intervalSum a (1,n-1) := by
  constructor
  · apply Multiset.mem_map.mpr
    refine ⟨(1,n-1), ?_, rfl⟩
    exact mem_erase.mpr ⟨by simp, mem_intervals.mpr (by omega)⟩
  · intro z hz
    obtain ⟨⟨i,j⟩, hp, rfl⟩ := Multiset.mem_map.mp hz
    have hpm := mem_erase.mp hp
    have hij := mem_intervals.mp hpm.2
    have ht := tail_total a (by omega : 1 ≤ n)
    by_cases hi : i = 0
    · have hj : j < n-1 := by
        have hjne : j ≠ n-1 := fun hh => hpm.1 (Prod.ext hi hh)
        omega
      have h := sum_add_missing_le ha hij.2 (by omega : n-1 < n)
        (by simp only [mem_Icc]; omega : n-1 ∉ Icc i j)
      have hm := hs 0 (n-1) (by omega) (by omega)
      linarith
    · have h := sum_add_missing_le ha hij.2 (by omega : 0 < n)
        (by simp only [mem_Icc]; omega : 0 ∉ Icc i j)
      linarith

private theorem first_eq {a b : ℕ → ℝ} {n : ℕ} (hn : 3 ≤ n)
    (ha : ∀ k < n, 0 ≤ a k) (hb : ∀ k < n, 0 ≤ b k)
    (hsa : ∀ u v, u ≤ v → v < n → a u ≤ a v)
    (hsb : ∀ u v, u ≤ v → v < n → b u ≤ b v)
    (he : observations a n = observations b n) : a 0 = b 0 := by
  have ht := total_eq (by omega : 2 ≤ n) ha hb he
  have hp : properObservations a n = properObservations b n := by
    rw [observations_cons_proper a (by omega), observations_cons_proper b (by omega), ht] at he
    simpa only [Multiset.cons_inj_right] using he
  have hpa := proper_max hn ha hsa
  have hpb := proper_max hn hb hsb
  have htt := extrema_eq hp hpa.1 hpb.1 hpa.2 hpb.2
  have hta := tail_total a (by omega : 1 ≤ n)
  have htb := tail_total b (by omega : 1 ≤ n)
  linarith

/-- The actual intervals not wholly contained in the first `k` entries. -/
noncomputable def residual (a : ℕ → ℝ) (n k : ℕ) : Multiset ℝ :=
  ((intervals n).filter fun p => k ≤ p.2).val.map (intervalSum a)

private theorem observations_split (a : ℕ → ℝ) {n k : ℕ} (hk : k ≤ n) :
    observations a n = observations a k + residual a n k := by
  have hf : intervals k = (intervals n).filter (fun p => p.2 < k) := by
    ext ⟨i,j⟩
    simp only [Finset.mem_filter, mem_intervals]
    omega
  have hh := congrArg (Multiset.map (intervalSum a))
    (Multiset.filter_add_not (fun p : ℕ × ℕ => p.2 < k) (intervals n).val)
  simpa only [observations, residual, hf, Finset.filter_val,
    Multiset.map_add, not_lt] using hh.symm

private theorem prefix_observations_eq {a b : ℕ → ℝ} {k : ℕ}
    (he : ∀ i < k, a i = b i) : observations a k = observations b k := by
  apply Multiset.map_congr rfl
  rintro ⟨i,j⟩ hp
  apply Finset.sum_congr rfl
  intro t ht
  exact he t (by have := (mem_intervals.mp hp).2; have := (mem_Icc.mp ht).2; omega)

/-- The least remaining value is the boundary adjacent sum; occurrences need not be unique. -/
theorem residual_boundary {a : ℕ → ℝ} {n k : ℕ}
    (ha : ∀ t < n, 0 ≤ a t)
    (hs : ∀ u v, u ≤ v → v < n → a u ≤ a v)
    (hk : 1 ≤ k) (hkn : k < n) :
    a (k-1) + a k ∈ residual a n k ∧
      ∀ z ∈ residual a n k, a (k-1) + a k ≤ z := by
  constructor
  · apply Multiset.mem_map.mpr
    refine ⟨(k-1,k), ?_, adjacent_sum a k hk⟩
    exact mem_filter.mpr ⟨mem_intervals.mpr (by omega), le_rfl⟩
  · intro z hz
    obtain ⟨⟨i,j⟩,hp,rfl⟩ := Multiset.mem_map.mp hz
    have hp' := mem_filter.mp hp
    exact boundary_le ha hs (mem_intervals.mp hp'.1).1
      (mem_intervals.mp hp'.1).2 hk hp'.2

/-- Equal full observations synchronize one more entry of two actual realizations. -/
theorem prefix_extension {a b : ℕ → ℝ} {n k : ℕ}
    (ha : ∀ t < n, 0 ≤ a t) (hb : ∀ t < n, 0 ≤ b t)
    (hsa : ∀ u v, u ≤ v → v < n → a u ≤ a v)
    (hsb : ∀ u v, u ≤ v → v < n → b u ≤ b v)
    (hk : 1 ≤ k) (hkn : k < n)
    (he : observations a n = observations b n)
    (hp : ∀ i < k, a i = b i) : a k = b k := by
  have hr : residual a n k = residual b n k := by
    rw [observations_split a hkn.le, observations_split b hkn.le,
      prefix_observations_eq hp] at he
    exact add_left_cancel he
  have hma := residual_boundary ha hsa hk hkn
  have hmb := residual_boundary hb hsb hk hkn
  have hle := hmb.2 _ (hr ▸ hma.1)
  have hge := hma.2 _ (hr.symm ▸ hmb.1)
  have hprev := hp (k-1) (by omega)
  linarith

/-- Reconstruction on arbitrary finite nonnegative weakly increasing real sequences. -/
theorem reconstruct {a b : ℕ → ℝ} {n m : ℕ}
    (hn : 3 ≤ n)
    (ha : ∀ k < n, 0 ≤ a k) (hb : ∀ k < m, 0 ≤ b k)
    (hsa : ∀ u v, u ≤ v → v < n → a u ≤ a v)
    (hsb : ∀ u v, u ≤ v → v < m → b u ≤ b v)
    (he : observations a n = observations b m) :
    n = m ∧ ∀ k < n, a k = b k := by
  have hm : 1 ≤ m := by
    have hz := total_mem a (by omega : 2 ≤ n)
    rw [he] at hz
    obtain ⟨⟨i,j⟩, hp, _⟩ := Multiset.mem_map.mp hz
    have hij := mem_intervals.mp hp
    omega
  have hnm := length_eq_of_observations_eq (by omega : 1 ≤ n) hm he
  subst m
  refine ⟨rfl, ?_⟩
  have hinit := first_eq hn ha hb hsa hsb he
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hz : k = 0
    · subst k; exact hinit
    · exact prefix_extension ha hb hsa hsb (by omega) hk he
        (fun i hi => ih i hi (by omega))

/-- The observation map for a list, defined independently of reconstruction. -/
noncomputable def listObservations (L : List ℝ) : Multiset ℝ :=
  observations (fun k => L.getD k 0) L.length

/-- Unordered inclusive interval sums of length at least two determine the full list. -/
theorem list_reconstruct (A B : List ℝ)
    (hA : 3 ≤ A.length)
    (ha : ∀ x ∈ A, 0 ≤ x) (hb : ∀ x ∈ B, 0 ≤ x)
    (hsA : A.Pairwise (· ≤ ·)) (hsB : B.Pairwise (· ≤ ·))
    (he : listObservations A = listObservations B) : A = B := by
  have nonnegA : ∀ k < A.length, 0 ≤ A.getD k 0 := by
    intro k hk
    rw [List.getD_eq_getElem A 0 hk]
    exact ha _ (List.getElem_mem hk)
  have nonnegB : ∀ k < B.length, 0 ≤ B.getD k 0 := by
    intro k hk
    rw [List.getD_eq_getElem B 0 hk]
    exact hb _ (List.getElem_mem hk)
  have sortedA : ∀ u v, u ≤ v → v < A.length → A.getD u 0 ≤ A.getD v 0 := by
    intro u v huv hv
    rw [List.getD_eq_getElem A 0 (by omega), List.getD_eq_getElem A 0 hv]
    exact hsA.rel_get_of_le (a := ⟨u, by omega⟩) (b := ⟨v,hv⟩) huv
  have sortedB : ∀ u v, u ≤ v → v < B.length → B.getD u 0 ≤ B.getD v 0 := by
    intro u v huv hv
    rw [List.getD_eq_getElem B 0 (by omega), List.getD_eq_getElem B 0 hv]
    exact hsB.rel_get_of_le (a := ⟨u, by omega⟩) (b := ⟨v,hv⟩) huv
  have hr := reconstruct hA nonnegA nonnegB sortedA sortedB he
  apply List.ext_getElem hr.1
  intro k hkA hkB
  simpa only [List.getD_eq_getElem A 0 hkA, List.getD_eq_getElem B 0 hkB]
    using hr.2 k hkA

end Omega.MonotoneIntervalReconstruction
