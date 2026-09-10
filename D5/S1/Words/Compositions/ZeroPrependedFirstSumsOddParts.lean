/- GID: D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Zero-prepended first sums of increasing partitions correspond to odd parts. -/

import D5.S1.Words.Compositions.FirstSumsPartitionCharacterization
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Zero-prepended first sums and odd parts

The first-sums convention is the existing adjacent-sums definition. A positive
increasing preimage corresponds to the odd parts obtained by replacing each
column height h of its Ferrers diagram by 2*h-1. No zero rows are admitted.
-/

namespace D5.S1.Words.Compositions.ZeroPrependedFirstSumsOddParts

open FirstSumsPartitionCharacterization

/-- Adjacent sums after prepending zero to an increasing positive list. -/
def IsZeroPrependedFirstSums (y : List ℕ) : Prop :=
  ∃ s : List ℕ, s.Pairwise (· ≤ ·) ∧ (∀ x ∈ s, 0 < x) ∧ firstSums (0 :: s) = y

private theorem firstSums_injective (a : ℕ) :
    Function.Injective (fun s : List ℕ => firstSums (a :: s)) := by
  intro s t
  induction s generalizing a t with
  | nil => cases t <;> simp [firstSums]
  | cons b s ih =>
    cases t with
    | nil => simp [firstSums]
    | cons c t =>
      intro h
      have h' : a + b = a + c ∧ firstSums (b :: s) = firstSums (c :: t) :=
        List.cons.inj h
      have hbc : b = c := by omega
      subst c
      exact congrArg (List.cons b) (ih b h'.2)

private theorem firstSums_pos (a : ℕ) (s : List ℕ) (hs : ∀ x ∈ s, 0 < x) :
    ∀ x ∈ firstSums (a :: s), 0 < x := by
  induction s generalizing a with
  | nil => simp [firstSums]
  | cons b s ih =>
    intro x hx
    change x ∈ (a + b) :: firstSums (b :: s) at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have := hs b (by simp); omega
    · exact ih b (fun z hz => hs z (by simp [hz])) x hx

private theorem firstSums_sorted (a : ℕ) (s : List ℕ)
    (hs : (a :: s).Pairwise (· ≤ ·)) : (firstSums (a :: s)).Pairwise (· ≤ ·) := by
  induction s generalizing a with
  | nil => simp [firstSums]
  | cons b s ih =>
    change ((a + b) :: firstSums (b :: s)).Pairwise (· ≤ ·)
    cases s with
    | nil => simp [firstSums]
    | cons c s =>
      have hac : a ≤ c := (List.pairwise_cons.mp hs).1 c (by simp)
      have ht := ih b hs.of_cons
      change ((a + b) :: (b + c) :: firstSums (c :: s)).Pairwise (· ≤ ·)
      refine List.pairwise_cons.mpr ⟨?_, ht⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have hbx := (List.pairwise_cons.mp ht).1 x hx
        change b + c ≤ x at hbx
        omega

private theorem firstSums_sum (a : ℕ) (s : List ℕ) :
    (firstSums (a :: s)).sum + s.getLastD a = a + 2 * s.sum := by
  induction s generalizing a with
  | nil => simp [firstSums]
  | cons b s ih =>
    have h := ih b
    cases s with
    | nil => simp [firstSums]; omega
    | cons c s =>
      change a + b + (firstSums (b :: c :: s)).sum + (b :: c :: s).getLastD a =
        a + 2 * (b + (c :: s).sum)
      simpa only [List.getLastD_cons] using (by omega :
        a + b + (firstSums (b :: c :: s)).sum + (c :: s).getLastD b =
          a + 2 * (b + (c :: s).sum))

private theorem cellsOfRowLens_card (l : List ℕ) :
    (YoungDiagram.cellsOfRowLens l).card = l.sum := by
  induction l with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a l ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint]
    · simpa using congrArg (a + ·) ih
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hy
      simpa using (Finset.mem_product.mp hx).1

private theorem rowLens_sum (d : YoungDiagram) : d.rowLens.sum = d.cells.card := by
  have h := cellsOfRowLens_card d.rowLens
  change (YoungDiagram.ofRowLens d.rowLens d.rowLens_sorted).cells.card = _ at h
  rw [YoungDiagram.ofRowLens_to_rowLens_eq_self] at h
  exact h.symm

private theorem transpose_sum (d : YoungDiagram) : d.transpose.rowLens.sum = d.rowLens.sum := by
  rw [rowLens_sum, rowLens_sum]
  simp [YoungDiagram.transpose]

private abbrev Rows := {l : List ℕ // l.SortedGE ∧ ∀ x ∈ l, 0 < x}

private abbrev OddRows := {l : Rows // ∀ x ∈ l.val, ¬ Even x}

private def conjugate : Rows ≃ Rows :=
  YoungDiagram.equivListRowLens.symm.trans
    (YoungDiagram.transposeOrderIso.toEquiv.trans YoungDiagram.equivListRowLens)

private theorem conjugate_sum (r : Rows) : (conjugate r).val.sum = r.val.sum := by
  change (YoungDiagram.ofRowLens r.val r.property.1).transpose.rowLens.sum = _
  rw [transpose_sum, YoungDiagram.rowLens_ofRowLens_eq_self r.property.2]

private theorem rowLen_zero (d : YoungDiagram) : d.rowLen 0 = d.rowLens.headD 0 := by
  cases h : d.rowLens with
  | nil =>
    have hz : d.colLen 0 = 0 := by simpa [h] using (d.length_rowLens).symm
    have hn : ¬ (0, 0) ∈ d := by rw [YoungDiagram.mem_iff_lt_colLen, hz]; omega
    rw [YoungDiagram.mem_iff_lt_rowLen] at hn
    simpa using (Nat.eq_zero_of_not_pos hn)
  | cons a l =>
    have hlen : 0 < d.rowLens.length := by simp [h]
    have hg := YoungDiagram.get_rowLens (μ := d) (i := 0) (h := hlen)
    simpa [h] using hg.symm

private theorem conjugate_length (r : Rows) : (conjugate r).val.length = r.val.headD 0 := by
  change (YoungDiagram.ofRowLens r.val r.property.1).transpose.rowLens.length = _
  rw [YoungDiagram.length_rowLens, YoungDiagram.colLen_transpose, rowLen_zero,
    YoungDiagram.rowLens_ofRowLens_eq_self r.property.2]

private def oddify : Rows ≃ OddRows where
  toFun r := ⟨⟨r.val.map (fun x => 2 * x - 1),
    (r.property.1.pairwise.map _ (by intros; omega)).sortedGE, by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      have := r.property.2 a ha
      omega⟩, by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        have := r.property.2 a ha
        rw [Nat.even_iff]
        omega⟩
  invFun r := ⟨r.val.val.map (fun x => (x + 1) / 2),
    (r.val.property.1.pairwise.map _ (by intros; omega)).sortedGE, by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      have := r.val.property.2 a ha
      omega⟩
  left_inv r := by
    apply Subtype.ext
    simp only [List.map_map]
    apply Eq.trans (b := r.val.map id) ?_ (List.map_id _)
    apply List.map_congr_left
    intro x hx
    have := r.property.2 x hx
    dsimp
    omega
  right_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [List.map_map]
    apply Eq.trans (b := r.val.val.map id) ?_ (List.map_id _)
    apply List.map_congr_left
    intro x hx
    have := r.property x hx
    rw [Nat.even_iff] at this
    dsimp
    omega

private theorem oddify_sum (r : Rows) :
    (oddify r).val.val.sum + r.val.length = 2 * r.val.sum := by
  change (r.val.map (fun x => 2 * x - 1)).sum + r.val.length = _
  suffices h : ∀ l : List ℕ, (∀ x ∈ l, 0 < x) →
      (l.map (fun x => 2 * x - 1)).sum + l.length = 2 * l.sum from h r.val r.property.2
  intro l hp
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hp a (by simp)
    have hi := ih (fun x hx => hp x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private noncomputable def rowFirstEquiv : Rows ≃ {y : List ℕ // IsZeroPrependedFirstSums y} :=
  Equiv.ofBijective (fun r => ⟨firstSums (0 :: r.val.reverse), r.val.reverse,
    r.property.1.reverse.pairwise, by simpa using r.property.2, rfl⟩) (by
      constructor
      · intro r t h
        apply Subtype.ext
        have he := firstSums_injective 0 (congrArg Subtype.val h)
        simpa using congrArg List.reverse he
      · rintro ⟨y, s, hs, hp, rfl⟩
        refine ⟨⟨s.reverse, hs.sortedLE.reverse, by simpa using hp⟩, ?_⟩
        apply Subtype.ext
        simp)

private noncomputable def firstOddEquiv :
    {y : List ℕ // IsZeroPrependedFirstSums y} ≃ OddRows :=
  rowFirstEquiv.symm.trans (conjugate.trans oddify)

private theorem row_weight (r : Rows) :
    (oddify (conjugate r)).val.val.sum = (firstSums (0 :: r.val.reverse)).sum := by
  have ho := oddify_sum (conjugate r)
  rw [conjugate_sum, conjugate_length] at ho
  have hf := firstSums_sum 0 r.val.reverse
  have hl : r.val.reverse.getLastD 0 = r.val.headD 0 := by
    cases r.val with
    | nil => rfl
    | cons a l => simp [List.reverse_cons]
  rw [hl, List.sum_reverse] at hf
  omega

private theorem firstOddEquiv_sum (y : {y : List ℕ // IsZeroPrependedFirstSums y}) :
    (firstOddEquiv y).val.val.sum = y.val.sum := by
  obtain ⟨r, rfl⟩ := rowFirstEquiv.surjective y
  simp only [firstOddEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact row_weight r

private theorem qualifying_sorted {y : List ℕ} (hy : IsZeroPrependedFirstSums y) :
    y.Pairwise (· ≤ ·) := by
  obtain ⟨s, hs, _, rfl⟩ := hy
  exact firstSums_sorted 0 s (List.pairwise_cons.mpr ⟨by simp, hs⟩)

private theorem qualifying_pos {y : List ℕ} (hy : IsZeroPrependedFirstSums y) :
    ∀ x ∈ y, 0 < x := by
  obtain ⟨s, _, hp, rfl⟩ := hy
  exact firstSums_pos 0 s hp

private noncomputable def firstListEquiv (n : ℕ) :
    {p : Nat.Partition n // IsZeroPrependedFirstSums (p.parts.sort (· ≤ ·))} ≃
      {y : {y : List ℕ // IsZeroPrependedFirstSums y} // y.val.sum = n} where
  toFun p := ⟨⟨p.val.parts.sort (· ≤ ·), p.property⟩, by
    have h := p.val.parts_sum
    rw [← Multiset.sort_eq p.val.parts (· ≤ ·), Multiset.sum_coe] at h
    exact h⟩
  invFun y := ⟨⟨y.val.val, fun hx => qualifying_pos y.val.property _ hx,
    by simpa using y.property⟩, by
    simpa only [Multiset.coe_sort, List.mergeSort_eq_self _
      (qualifying_sorted y.val.property)] using y.val.property⟩
  left_inv p := by
    apply Subtype.ext
    exact Nat.Partition.ext (Multiset.sort_eq _ _)
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Multiset.coe_sort _ _).trans
      (List.mergeSort_eq_self _ (qualifying_sorted y.val.property))

private noncomputable def oddListEquiv (n : ℕ) :
    {p : Nat.Partition n // ∀ x ∈ p.parts, ¬ Even x} ≃
      {r : OddRows // r.val.val.sum = n} where
  toFun p := ⟨⟨⟨p.val.parts.sort (· ≥ ·),
    (Multiset.pairwise_sort _ _).sortedGE, by
      intro x hx
      exact p.val.parts_pos ((Multiset.mem_sort _).mp hx)⟩, by
        intro x hx
        exact p.property x ((Multiset.mem_sort _).mp hx)⟩, by
          have h := p.val.parts_sum
          rw [← Multiset.sort_eq p.val.parts (· ≥ ·), Multiset.sum_coe] at h
          exact h⟩
  invFun r := ⟨⟨r.val.val.val, fun hx => r.val.val.property.2 _ hx,
    by simpa using r.property⟩,
    r.val.property⟩
  left_inv p := by
    apply Subtype.ext
    exact Nat.Partition.ext (Multiset.sort_eq _ _)
  right_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact (Multiset.coe_sort _ _).trans
      (List.mergeSort_eq_self _ r.val.val.property.1.pairwise)

open scoped Classical in
/-- Qualifying reversed partitions are equinumerous with odd-part partitions. -/
theorem card_zeroPrependedFirstSums_eq_odds (n : ℕ) :
    ((Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => IsZeroPrependedFirstSums (p.parts.sort (· ≤ ·)))).card =
      (Nat.Partition.odds n).card := by
  classical
  let e := (firstListEquiv n).trans
    ((firstOddEquiv.subtypeEquiv (fun y => by rw [firstOddEquiv_sum])).trans
      (oddListEquiv n).symm)
  simpa only [Fintype.card_subtype, Nat.Partition.odds, Nat.Partition.restricted]
    using Fintype.card_congr e

open scoped Classical in
/-- The A392694 reversed-partition count is A000009, with no shift. -/
theorem card_zeroPrependedFirstSums_eq_distincts (n : ℕ) :
    ((Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => IsZeroPrependedFirstSums (p.parts.sort (· ≤ ·)))).card =
      (Nat.Partition.distincts n).card :=
  (card_zeroPrependedFirstSums_eq_odds n).trans
    (Nat.Partition.card_odds_eq_card_distincts n)

end D5.S1.Words.Compositions.ZeroPrependedFirstSumsOddParts
