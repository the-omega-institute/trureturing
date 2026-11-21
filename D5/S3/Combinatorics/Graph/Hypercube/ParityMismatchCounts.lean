/- GID: D5/S3/Combinatorics/Graph/Hypercube/ParityMismatchCounts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/ParityMismatchCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even-word cuts characterize the mismatch counts of integer parity couplings. -/

import D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
import D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts

section ParityColumns

open Finset
open D5.S3.QuantumBounds.MerminMeasurementDependence (bit_cases)

variable {R I : Type*} [Fintype R] [Fintype I]

private abbrev Table (R I : Type*) := R → I → ZMod 2

private def rowParity (x : I → ZMod 2) : ZMod 2 := ∑ i, x i
private def columnCounts (A : Table R I) (j : I) : ℕ := ∑ r, (A r j).val
private def disagreement (x y : I → ZMod 2) : ℕ := ∑ j, (x j - y j).val

private theorem bit_flip {a b : ZMod 2} (ne : a ≠ b) : b = a + 1 := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp_all [show (1 : ZMod 2) + 1 = 0 by decide]

private theorem rowParity_sub (x y : I → ZMod 2) :
    ((disagreement x y : ℕ) : ZMod 2) = rowParity x - rowParity y := by
  unfold disagreement rowParity
  rw [Nat.cast_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => ZMod.natCast_zmod_val _

private theorem disagreement_at_least_one {x y : I → ZMod 2}
    (hx : rowParity x = 1) (hy : rowParity y = 0) : 1 ≤ disagreement x y := by
  have h := rowParity_sub x y
  rw [hx, hy, sub_zero] at h
  by_contra! small
  have zero : disagreement x y = 0 := by omega
  simp [zero] at h

private theorem sum_parities_of_even_columns (A : Table R I)
    (columns : ∀ j, Even (columnCounts A j)) : (∑ r, rowParity (A r)) = 0 := by
  simp_rw [rowParity]
  rw [sum_comm]
  apply sum_eq_zero
  intro j _
  have h := (columns j).natCast_zmod_two
  simpa [columnCounts, Nat.cast_sum, ZMod.natCast_zmod_val] using h

variable [DecidableEq R] [DecidableEq I]

private def swapColumn (A : Table R I) (r s : R) (i : I) : Table R I :=
  fun t j => if j = i then A (Equiv.swap r s t) j else A t j

private theorem swap_column_counts (A : Table R I) (r s : R) (i : I) :
    columnCounts (swapColumn A r s i) = columnCounts A := by
  funext j
  by_cases hj : j = i
  · subst j
    unfold columnCounts
    simpa [swapColumn] using Equiv.sum_comp (Equiv.swap r s) (fun t => (A t i).val)
  · simp [columnCounts, swapColumn, hj]

private theorem swap_off_rows (A : Table R I) {r s t : R} {i : I} (hr : t ≠ r) (hs : t ≠ s) :
    swapColumn A r s i t = A t := by
  funext j
  by_cases hj : j = i <;> simp [swapColumn, hj, Equiv.swap_apply_of_ne_of_ne hr hs]

private theorem swap_flips_first_parity (A : Table R I) {r s : R} {i : I}
    (ne : A r i ≠ A s i) :
    rowParity (swapColumn A r s i r) = rowParity (A r) + 1 := by
  unfold rowParity
  have row :
      (∑ j ∈ (univ : Finset I).erase i, swapColumn A r s i r j) =
        ∑ j ∈ (univ : Finset I).erase i, A r j := by
    apply sum_congr rfl
    intro j hj
    exact ite_eq_right (mem_erase.mp hj).1
  have original := sum_erase_add (univ : Finset I) (A r) (mem_univ i)
  rw [← sum_erase_add (univ : Finset I) (swapColumn A r s i r) (mem_univ i), row, ← original]
  simp only [swapColumn, ite_true, Equiv.swap_apply_left]
  rw [bit_flip ne, add_assoc]

private theorem swap_flips_second_parity (A : Table R I) {r s : R} {i : I}
    (ne : A r i ≠ A s i) :
    rowParity (swapColumn A r s i s) = rowParity (A s) + 1 := by
  have commute : swapColumn A r s i = swapColumn A s r i := by
    unfold swapColumn
    rw [Equiv.swap_comm r s]
  rw [commute]
  exact swap_flips_first_parity A ne.symm

private def zeroRows (A : Table R I) : Finset R := univ.filter fun r => rowParity (A r) = 0

private theorem zero_rows_even (A : Table R I) (size : Even (Fintype.card R))
    (columns : ∀ j, Even (columnCounts A j)) : Even (zeroRows A).card := by
  have h : ((zeroRows A).card : ZMod 2) + (∑ r, rowParity (A r)) = (Fintype.card R : ZMod 2) := by
    unfold zeroRows
    rw [← sum_boole, ← sum_add_distrib]
    calc
      _ = ∑ _ : R, (1 : ZMod 2) := by
        apply sum_congr rfl
        intro r _
        rcases bit_cases (rowParity (A r)) with h | h <;> simp [h]
      _ = _ := by simp
  rw [sum_parities_of_even_columns A columns, size.natCast_zmod_two, add_zero] at h
  exact ZMod.natCast_eq_zero_iff_even.mp h

private theorem zeroRows_swap_pair (A : Table R I) {r s : R} {i : I}
    (ne : A r i ≠ A s i) :
    r ≠ s ∧ ∀ t ∉ ({r,s} : Finset R),
      t ∈ zeroRows (swapColumn A r s i) ↔ t ∈ zeroRows A := by
  refine ⟨fun h => ne (congrArg (fun u => A u i) h), ?_⟩
  intro t ht
  have outside : t ≠ r ∧ t ≠ s := by
    simpa [not_or] using ht
  simp [zeroRows, swap_off_rows A outside.1 outside.2]

private theorem zeroRows_count_swap_even_pair (A : Table R I) {r s : R} {i : I}
    (hr : rowParity (A r) = 0) (hs : rowParity (A s) = 0) (ne : A r i ≠ A s i) :
    (zeroRows (swapColumn A r s i)).card < (zeroRows A).card := by
  obtain ⟨rs, outside⟩ := zeroRows_swap_pair A ne
  have dropsR : r ∉ zeroRows (swapColumn A r s i) := by
    simp [zeroRows, swap_flips_first_parity A ne, hr]
  have dropsS : s ∉ zeroRows (swapColumn A r s i) := by
    simp [zeroRows, swap_flips_second_parity A ne, hs]
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro t ht
    have h : t ∉ ({r,s} : Finset R) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun e => dropsR (e ▸ ht), fun e => dropsS (e ▸ ht)⟩
    exact (outside t h).mp ht
  · intro eq
    exact dropsR (eq ▸ (by simp [zeroRows, hr] : r ∈ zeroRows A))

private theorem zeroRows_count_swap_even_odd (A : Table R I) {r s : R} {i : I}
    (hr : rowParity (A r) = 0) (hs : rowParity (A s) = 1) (ne : A r i ≠ A s i) :
    (zeroRows (swapColumn A r s i)).card = (zeroRows A).card := by
  obtain ⟨rs, outside⟩ := zeroRows_swap_pair A ne
  have onePlusOne : (1 : ZMod 2) + 1 = 0 := by decide
  have eq : zeroRows (swapColumn A r s i) = (zeroRows A).map (Equiv.swap r s).toEmbedding := by
    ext t
    by_cases tr : t = r
    · subst t
      simp [zeroRows, swap_flips_first_parity A ne, Equiv.swap_apply_left, hr, hs]
    · by_cases ts : t = s
      · subst t
        simp [zeroRows, swap_flips_second_parity A ne, Equiv.swap_apply_right, hr, hs, onePlusOne]
      · have ht : t ∉ ({r,s} : Finset R) := by simp [tr, ts]
        rw [outside t ht]
        simp [Equiv.swap_apply_of_ne_of_ne tr ts]
  rw [eq, card_map]

private theorem equal_zero_rows_at_minimum (A : Table R I)
    (minimum : ∀ B : Table R I, columnCounts B = columnCounts A →
      (zeroRows A).card ≤ (zeroRows B).card)
    {r s : R} (hr : rowParity (A r) = 0) (hs : rowParity (A s) = 0) :
    A r = A s := by
  funext i
  by_contra ne
  have bound := minimum _ (swap_column_counts A r s i)
  exact (not_lt_of_ge bound) (zeroRows_count_swap_even_pair A hr hs ne)

private theorem odd_row_near_even_rows (A : Table R I)
    (minimum : ∀ B : Table R I, columnCounts B = columnCounts A →
      (zeroRows A).card ≤ (zeroRows B).card)
    {r s t : R} (rs : r ≠ s)
    (hr : rowParity (A r) = 0) (hs : rowParity (A s) = 0) (ht : rowParity (A t) = 1) :
    disagreement (A t) (A r) = 1 := by
  have differ : A t ≠ A r := fun h => by rw [h, hr] at ht; exact zero_ne_one ht
  obtain ⟨i, hi⟩ := Function.ne_iff.mp differ
  have unique (j : I) (ji : j ≠ i) : A t j = A r j := by
    let B := swapColumn A r t i
    have Bmin (C : Table R I) (hc : columnCounts C = columnCounts B) :
        (zeroRows B).card ≤ (zeroRows C).card := by
      rw [zeroRows_count_swap_even_odd A hr ht hi.symm]
      exact minimum C (hc.trans (swap_column_counts A r t i))
    have st : s ≠ t := by
      intro h
      rw [h, ht] at hs
      exact one_ne_zero hs
    have bs : B s = A s := swap_off_rows A rs.symm st
    have bt : rowParity (B t) = 0 := by
      unfold B
      rw [swap_flips_second_parity A hi.symm, ht]
      decide
    have rowEq : B t = B s := equal_zero_rows_at_minimum B Bmin bt (bs.symm ▸ hs)
    have origEq : A s = A r := equal_zero_rows_at_minimum A minimum hs hr
    calc
      A t j = B t j := by simp [B, swapColumn, ji]
      _ = B s j := congrArg (· j) rowEq
      _ = A r j := congrArg (· j) (bs.trans origEq)
  unfold disagreement
  rw [sum_eq_single i]
  · rw [bit_flip hi.symm]
    simp [ZMod.val_one]
  · intro j _ ji
    rw [unique j ji, sub_self, ZMod.val_zero]
  · simp

private theorem minimum_realizer_all_odd (A : Table R I)
    (minimum : ∀ B : Table R I, columnCounts B = columnCounts A →
      (zeroRows A).card ≤ (zeroRows B).card)
    (size : Even (Fintype.card R)) (columns : ∀ j, Even (columnCounts A j))
    (cut : ∀ e : I → ZMod 2, rowParity e = 0 →
      Fintype.card R ≤ ∑ r, disagreement (A r) e) :
    ∀ r, rowParity (A r) = 1 := by
  intro r
  rcases bit_cases (rowParity (A r)) with hr | hr
  · exfalso
    have rZero : r ∈ zeroRows A := by simp [zeroRows, hr]
    have two : 1 < (zeroRows A).card := by
      obtain ⟨k, hk⟩ := zero_rows_even A size columns
      have pos := Finset.card_pos.mpr ⟨r, rZero⟩
      omega
    have existsSecond : ∃ s ∈ zeroRows A, r ≠ s := by
      by_contra! only
      refine (not_le_of_gt two) (Finset.card_le_one.mpr fun x hx y hy => ?_)
      exact (only x hx).symm.trans (only y hy)
    obtain ⟨s, sZero, rs⟩ := existsSecond
    have hs : rowParity (A s) = 0 := by simpa [zeroRows] using sZero
    have distances (t : R) :
        disagreement (A t) (A r) = if rowParity (A t) = 0 then 0 else 1 := by
      rcases bit_cases (rowParity (A t)) with ht | ht
      · rw [equal_zero_rows_at_minimum A minimum ht hr]
        simp [disagreement, hr]
      · simpa [ht] using odd_row_near_even_rows A minimum rs hr hs ht
    have sumSmall : (∑ t, disagreement (A t) (A r)) < Fintype.card R := by
      rw [show Fintype.card R = ∑ _ : R, (1 : ℕ) by simp]
      apply sum_lt_sum
      · intro t _
        rw [distances]
        split <;> omega
      · exact ⟨r, mem_univ r, by simp only [distances, hr, ite_true, Nat.zero_lt_one]⟩
    exact (not_lt_of_ge (cut (A r) hr)) sumSmall
  · exact hr

private theorem total_disagreement_eq_columns (A : Table R I) (e : I → ZMod 2) :
    (∑ r, disagreement (A r) e) =
      ∑ j, if e j = 0 then columnCounts A j else Fintype.card R - columnCounts A j := by
  simp_rw [disagreement]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rcases bit_cases (e j) with hj | hj
  · simp [hj, columnCounts]
  · have h : (∑ r, (A r j - 1).val) + columnCounts A j = Fintype.card R := by
      unfold columnCounts
      rw [← sum_add_distrib]
      calc
        _ = ∑ _ : R, (1 : ℕ) := by
          apply sum_congr rfl
          intro r _
          rcases bit_cases (A r j) with hr | hr <;> rw [hr] <;> decide
        _ = _ := by simp
    rw [hj, ite_eq_right one_ne_zero]
    omega

private theorem odd_table_of_even_columns (A : Table R I)
    (size : Even (Fintype.card R)) (columns : ∀ j, Even (columnCounts A j))
    (cut : ∀ e : I → ZMod 2, rowParity e = 0 →
      Fintype.card R ≤
        ∑ j, if e j = 0 then columnCounts A j else Fintype.card R - columnCounts A j) :
    ∃ B : Table R I, columnCounts B = columnCounts A ∧ ∀ r, rowParity (B r) = 1 := by
  classical
  let P (m : ℕ) := ∃ B : Table R I,
    columnCounts B = columnCounts A ∧ (zeroRows B).card = m
  have existsCount : ∃ m, P m := ⟨(zeroRows A).card, A, rfl, rfl⟩
  obtain ⟨B, counts, minimum⟩ := Nat.find_spec existsCount
  refine ⟨B, counts, minimum_realizer_all_odd B ?_ size ?_ ?_⟩
  · intro C hC
    rw [minimum]
    exact Nat.find_min' existsCount (show P (zeroRows C).card from
      ⟨C, hC.trans counts, rfl⟩)
  · intro j
    rw [counts]
    exact columns j
  · intro e he
    rw [total_disagreement_eq_columns, counts]
    exact cut e he

private def prefixTable {I : Type*} (m : ℕ) (counts : I → ℕ) : Table (Fin m) I :=
  fun r j => if r.val < counts j then 1 else 0

private theorem prefix_table_counts {I : Type*} [Fintype I] (m : ℕ) (c : I → ℕ)
    (cap : ∀ j, c j ≤ m) : columnCounts (prefixTable m c) = c := by
  funext j
  unfold columnCounts
  have values (r : Fin m) : (prefixTable m c r j).val = if r.val < c j then 1 else 0 := by
    unfold prefixTable
    split <;> simp [ZMod.val_one]
  simp only [values, Finset.sum_boole, Nat.cast_id, Fin.card_filter_val_lt, min_eq_right (cap j)]

private theorem exact_odd_words {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (c : I → ℕ)
    (size : Even m) (cap : ∀ j, c j ≤ m) (columns : ∀ j, Even (c j))
    (cut : ∀ e : I → ZMod 2, rowParity e = 0 → m ≤ ∑ j,
      if e j = 0 then c j else m - c j) :
    ∃ B : Table (Fin m) I, columnCounts B = c ∧ ∀ r, rowParity (B r) = 1 := by
  let A := prefixTable m c
  have counts := prefix_table_counts m c cap
  obtain ⟨B, Bcounts, odd⟩ := odd_table_of_even_columns A
    (by simpa using size)
    (by rw [show columnCounts A = c from counts]; exact columns)
    (by rw [show columnCounts A = c from counts]; simpa using cut)
  exact ⟨B, Bcounts.trans counts, odd⟩

end ParityColumns
section ParityNumbering

open Finset
open D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
open D5.S3.FiniteGroups.Hall.PrescribedDifferences

private abbrev CopyGroup (n k : ℕ) := Profile (n + 1) × ZMod k

private theorem parity_add {d : ℕ} (x y : Profile d) :
    parity (x + y) = parity x + parity y := by
  simp only [parity, Pi.add_apply, sum_add_distrib]

private theorem parity_numbering_with_copies (n k : ℕ) [NeZero k]
    (δ : Fin (Nat.card (CopyGroup n k)) → Profile (n + 2))
    (odd : ∀ j, parity (δ j) = 1) (balance : (∑ j, δ j) = 0) :
    ∃ (left : Fin (Nat.card (CopyGroup n k)) ≃ ParityClass (n + 2) 0 × ZMod k)
      (right : Fin (Nat.card (CopyGroup n k)) ≃ ParityClass (n + 2) 1 × ZMod k),
      ∀ j, (right j).1.val = (left j).1.val + δ j ∧ (right j).2 = (left j).2 := by
  let R (j : Fin (Nat.card (CopyGroup n k))) : CopyGroup n k := (Fin.tail (δ j), 0)
  have requestZero : (∑ j, R j) = 0 := by
    ext i
    · simp only [R, Prod.fst_sum, Finset.sum_apply, Fin.tail, Prod.fst_zero, Pi.zero_apply]
      have coord := congrFun balance i.succ
      simpa only [Finset.sum_apply, Pi.zero_apply] using coord
    · simp [R, Prod.snd_sum]
  obtain ⟨x, bij⟩ := (numbering_iff_sum_eq_zero (CopyGroup n k) R).2 requestZero
  let toParity (p : ZMod 2) : CopyGroup n k ≃ ParityClass (n + 2) p × ZMod k :=
    (tailEquiv (n + 1) p).symm.prodCongr (Equiv.refl _)
  let left := x.trans (toParity 0)
  let right := (Equiv.ofBijective _ bij).trans (toParity 1)
  refine ⟨left, right, fun j => ⟨?_, ?_⟩⟩
  · let p : ParityClass (n + 2) 1 := ⟨(left j).1.val + δ j,
      by rw [parity_add, (left j).1.property, odd, zero_add]⟩
    change (right j).1.val = p.val
    have leftTail : (tailEquiv (n + 1) 0) (left j).1 = (x j).1 :=
      (tailEquiv (n + 1) 0).apply_symm_apply _
    have rightTail : (tailEquiv (n + 1) 1) (right j).1 =
        (x j).1 + Fin.tail (δ j) := (tailEquiv (n + 1) 1).apply_symm_apply _
    have pTail : (tailEquiv (n + 1) 1) p = (x j).1 + Fin.tail (δ j) := by
      change Fin.tail ((left j).1.val + δ j) = _
      change Fin.tail (left j).1.val = _ at leftTail
      rw [show Fin.tail ((left j).1.val + δ j) =
        Fin.tail (left j).1.val + Fin.tail (δ j) by rfl, leftTail]
    exact congrArg Subtype.val ((tailEquiv (n + 1) 1).injective (rightTail.trans pTail.symm))
  · change (x j).2 + 0 = (x j).2
    exact add_zero _

end ParityNumbering

open Finset
open D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching

private theorem copy_count (n k : ℕ) [NeZero k] :
    Nat.card (CopyGroup n k) = 2 ^ (n + 1) * k := by
  change Nat.card (Profile (n + 1) × ZMod k) = _
  rw [Nat.card_prod, profileCard, Nat.card_eq_fintype_card (α := ZMod k), ZMod.card]

private theorem group_column_zero {m d : ℕ} (A : Fin m → Profile d)
    (counts : ∀ i, Even (columnCounts A i)) : (∑ j, A j) = 0 := by
  funext i
  rw [Finset.sum_apply, Pi.zero_apply]
  have h := (counts i).natCast_zmod_two
  simpa [columnCounts, Nat.cast_sum, ZMod.natCast_zmod_val] using h

private theorem bit_disagreement (a b : ZMod 2) :
    (a - b).val = if a ≠ b then 1 else 0 := by
  rcases D5.S3.QuantumBounds.MerminMeasurementDependence.bit_cases a with rfl | rfl <;>
    rcases D5.S3.QuantumBounds.MerminMeasurementDependence.bit_cases b with rfl | rfl <;>
    decide

open Classical in
private theorem integer_parity_coupling_attains_mismatch_counts (n k : ℕ) [NeZero k]
    (a : Fin (n + 2) → ℕ)
    (cap : ∀ i, a i ≤ k * 2 ^ n)
    (cut : ∀ e : Profile (n + 2), parity e = 0 →
      k * 2 ^ n ≤ ∑ i, if e i = 0 then a i else k * 2 ^ n - a i) :
    ∃ W : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, W p q = k) ∧ (∀ q, ∑ p, W p q = k) ∧
      ∀ i, (∑ p, ∑ q, if p.val i ≠ q.val i then W p q else 0) = 2 * a i := by
  let m := Nat.card (CopyGroup n k)
  let M := k * 2 ^ n
  have mEq : m = 2 * M := by
    rw [show m = Nat.card (CopyGroup n k) by rfl, copy_count, pow_succ]
    dsimp [M]
    ac_rfl
  have cap' (i : Fin (n + 2)) : 2 * a i ≤ m := by
    rw [mEq]
    exact Nat.mul_le_mul_left _ (cap i)
  have ev' (i : Fin (n + 2)) : Even (2 * a i) := ⟨a i, two_mul _⟩
  have cut' (e : Profile (n + 2)) (ev : rowParity e = 0) :
      m ≤ ∑ i, if e i = 0 then 2 * a i else m - 2 * a i := by
    rw [mEq, show (∑ i, if e i = 0 then 2 * a i else 2 * M - 2 * a i) =
      2 * ∑ i, if e i = 0 then a i else M - a i from ?_]
    · exact Nat.mul_le_mul_left _ (cut e ev)
    · rw [mul_sum]
      apply sum_congr rfl
      intro i _
      by_cases h : e i = 0 <;> simp [h, Nat.mul_sub_left_distrib]
  obtain ⟨A, cols, rows⟩ := exact_odd_words m (fun i => 2 * a i)
    (by rw [mEq]; exact ⟨M, two_mul M⟩) cap' ev' cut'
  obtain ⟨left, right, diff⟩ := parity_numbering_with_copies n k
    A rows (group_column_zero A (fun i => by rw [cols]; exact ev' i))
  let W (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) : ℕ :=
    ∑ j : Fin m, if (left j).1 = p ∧ (right j).1 = q then 1 else 0
  have margin {p : ZMod 2} (E : Fin m ≃ ParityClass (n + 2) p × ZMod k)
      (x : ParityClass (n + 2) p) : (∑ j, if (E j).1 = x then (1 : ℕ) else 0) = k := by
    rw [Equiv.sum_comp E (fun z => if z.1 = x then (1 : ℕ) else 0)]
    rw [Fintype.sum_prod_type]
    simp [ZMod.card]
  refine ⟨W, ?_, ?_, ?_⟩
  · intro p
    unfold W
    rw [sum_comm]
    refine (sum_congr rfl fun j _ => ?_).trans (margin left p)
    by_cases h : (left j).1 = p <;> simp [h]
  · intro q
    unfold W
    rw [sum_comm]
    refine (sum_congr rfl fun j _ => ?_).trans (margin right q)
    by_cases h : (right j).1 = q <;> simp [h]
  · intro i
    have rearrange (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
        (if p.val i ≠ q.val i then W p q else 0) =
          ∑ j : Fin m, if (left j).1 = p ∧ (right j).1 = q then
            (if p.val i ≠ q.val i then 1 else 0) else 0 := by
      by_cases h : p.val i ≠ q.val i <;> simp [W, h]
    simp_rw [rearrange]
    simp_rw [sum_comm (s := (univ : Finset (ParityClass (n + 2) 1)))
      (t := (univ : Finset (Fin m)))]
    rw [sum_comm (s := (univ : Finset (ParityClass (n + 2) 0)))
      (t := (univ : Finset (Fin m))), ← congrFun cols i]
    unfold columnCounts
    apply sum_congr rfl
    intro j _
    have hbit : (right j).1.val i = (left j).1.val i + A j i :=
      congrFun (diff j).1 i
    have eqbit : (right j).1.val i - (left j).1.val i = A j i := by
      rw [hbit, add_sub_cancel_left]
    rw [sum_eq_single (left j).1]
    · rw [sum_eq_single (right j).1]
      · rw [← eqbit, bit_disagreement]
        simp [ne_comm]
      · intro q _ hq
        simp [Ne.symm hq]
      · simp
    · intro p _ hp
      simp [Ne.symm hp]
    · simp

open Classical in
private theorem mismatch_counts_satisfy_even_cuts (n k : ℕ)
    (a : Fin (n + 2) → ℕ)
    (W : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (rows : ∀ p, ∑ q, W p q = k)
    (counts : ∀ i, (∑ p, ∑ q, if p.val i ≠ q.val i then W p q else 0) = 2 * a i) :
    (∀ i, a i ≤ k * 2 ^ n) ∧
    ∀ e : Profile (n + 2), parity e = 0 →
      k * 2 ^ n ≤ ∑ i, if e i = 0 then a i else k * 2 ^ n - a i := by
  let M := k * 2 ^ n
  let P := ParityClass (n + 2) 0
  let Q := ParityClass (n + 2) 1
  have ct : Fintype.card P = 2 ^ (n + 1) := by
    rw [Fintype.card_congr (tailEquiv (n + 1) 0), ← Nat.card_eq_fintype_card, profileCard]
  have total : ∑ p : P, ∑ q : Q, W p q = 2 * M := by
    calc
      _ = ∑ _ : P, k := sum_congr rfl (fun p _ => rows p)
      _ = 2 * M := by
        simp only [sum_const, card_univ, nsmul_eq_mul, ct, pow_succ, M]
        ac_rfl
  have bounded (i : Fin (n + 2)) : 2 * a i ≤ 2 * M := by
    rw [← counts i, ← total]
    apply sum_le_sum
    intro p _
    apply sum_le_sum
    intro q _
    split <;> omega
  refine ⟨fun i => by have h := bounded i; omega, ?_⟩
  intro e ev
  have odd (p : P) (q : Q) : rowParity (q.val - p.val) = 1 := by
    change (∑ i : Fin (n + 2), (q.val i - p.val i)) = 1
    rw [sum_sub_distrib]
    change parity q.val - parity p.val = 1
    rw [q.property, p.property, sub_zero]
  have polar (i : Fin (n + 2)) :
      (∑ p : P, ∑ q : Q, W p q * (q.val i - p.val i - e i).val) =
        if e i = 0 then 2 * a i else 2 * (M - a i) := by
    rcases D5.S3.QuantumBounds.MerminMeasurementDependence.bit_cases (e i) with h | h
    · simp_rw [h, sub_zero, bit_disagreement, mul_ite, mul_one, mul_zero]
      simpa [ne_comm] using counts i
    · let T := ∑ p : P, ∑ q : Q, W p q * (q.val i - p.val i - e i).val
      have local_eq (p : P) (q : Q) :
          W p q * (q.val i - p.val i - e i).val +
            (if p.val i ≠ q.val i then W p q else 0) = W p q := by
        rcases D5.S3.QuantumBounds.MerminMeasurementDependence.bit_cases (p.val i) with hp | hp <;>
          rcases D5.S3.QuantumBounds.MerminMeasurementDependence.bit_cases (q.val i) with hq | hq <;>
          simp [h, hp, hq, show ((0 : ZMod 2) - 1) = 1 by decide, ZMod.val_one]
      have addBack : T + 2 * a i = 2 * M := by
        rw [← counts i, ← total, ← sum_add_distrib]
        apply sum_congr rfl
        intro p _
        rw [← sum_add_distrib]
        exact sum_congr rfl (fun q _ => local_eq p q)
      have cap := bounded i
      have gap : T = 2 * (M - a i) := by omega
      simpa only [T, h, ite_eq_right one_ne_zero] using gap
  have below : 2 * M ≤
      ∑ p : P, ∑ q : Q, W p q * (∑ i, (q.val i - p.val i - e i).val) := by
    rw [← total]
    apply sum_le_sum
    intro p _
    apply sum_le_sum
    intro q _
    have diff := disagreement_at_least_one (odd p q) ev
    exact (Nat.mul_one (W p q)).symm.le.trans (Nat.mul_le_mul_left _ diff)
  have reorder :
      (∑ p : P, ∑ q : Q, W p q * (∑ i, (q.val i - p.val i - e i).val)) =
      2 * ∑ i, if e i = 0 then a i else M - a i := by
    simp_rw [mul_sum]
    simp_rw [sum_comm (s := (univ : Finset Q)) (t := (univ : Finset (Fin (n + 2))))]
    rw [sum_comm (s := (univ : Finset P)) (t := (univ : Finset (Fin (n + 2))))]
    apply sum_congr rfl
    intro i _
    rw [polar]
    split <;> simp_all
  rw [reorder] at below
  change M ≤ ∑ i, if e i = 0 then a i else M - a i
  exact Nat.le_of_mul_le_mul_left below (by decide)

open Classical in
/-- The even-word cuts describe all total coordinate mismatch counts of a parity coupling. -/
theorem exact_integer_parity_mismatch_counts (n k : ℕ) [NeZero k]
    (a : Fin (n + 2) → ℕ) :
    (∃ W : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, W p q = k) ∧ (∀ q, ∑ p, W p q = k) ∧
      ∀ i, (∑ p, ∑ q, if p.val i ≠ q.val i then W p q else 0) = 2 * a i) ↔
    (∀ i, a i ≤ k * 2 ^ n) ∧
    ∀ e : Profile (n + 2), parity e = 0 →
      k * 2 ^ n ≤ ∑ i, if e i = 0 then a i else k * 2 ^ n - a i := by
  constructor
  · rintro ⟨W, rows, _, counts⟩
    exact mismatch_counts_satisfy_even_cuts n k a W rows counts
  · rintro ⟨cap, cut⟩
    exact integer_parity_coupling_attains_mismatch_counts n k a cap cut

end D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts
