/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoTail
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoTail
   mirror-E: none(waiver:row-four-two-first-reduction)
   anchors: []
   utility: none
   digest: Deletes the first two values from a primitive two-first word. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoPrefix
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoTail

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveBlocks
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoPrefix

theorem primitive_two_tail (w : List ℕ) (n : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hn : 3 ≤ n) (hhead : w.head? = some 2)
    (hprimitive : primitive w n) :
    let z := (w.filter (fun x => decide (2 < x))).map (fun x => x - 2)
    z ∈ NonnestingDefs.avoiders (n - 2)
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] ∧
    (∀ a b, 1 ≤ a → a < b → b ≤ n - 2 → (z).idxOf a < (z).idxOf b) ∧
    primitive z (n - 2) ∧
    w = [2, 1, 3, 2, 1] ++ (shift 2 z).tail := by
  have count_two_positions (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) :
      (w).idxOf a < secondPos a w ∧
        w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hfirst, hsecond]
      omega
    constructor
    · rw [hfirst]
      simp
    · rw [hsecond]
      have hle : ¬ u.length + 1 + v.length < u.length := by omega
      simp [List.getElem?_append, hle]
      have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
      rw [heq]
      simp
  let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
  let z := (w.filter (fun x => decide (2 < x))).map (fun x => x - 2)
  have hdelEq (l : List ℕ) :
      (((l.filter (fun x => decide (1 < x))).map (fun x => x - 1)).filter
          (fun x => decide (1 < x))).map (fun x => x - 1) =
        (l.filter (fun x => decide (2 < x))).map (fun x => x - 2) := by
    induction l with
    | nil => simp
    | cons x xs ih =>
      by_cases hx2 : 2 < x
      · have hx1 : 1 < x := by omega
        have hxsub : 1 < x - 1 := by omega
        have heq : (x - 1) - 1 = x - 2 := by omega
        simp [hx2, hx1, hxsub, heq, ih]
      · by_cases hx1 : 1 < x
        · have hxsub : ¬ 1 < x - 1 := by omega
          simp [hx2, hx1, hxsub, ih]
        · simp [hx2, hx1, ih]
  have hdel1 : (w.filter (fun x => decide (1 < x))).map (fun x => x - 1) ∈
      NonnestingDefs.avoiders (n - 1) Λ := by
    have hnn : n - 1 + 1 = n := by omega
    exact delete_lowest_avoider w (n - 1) Λ (by simpa [hnn] using hw)
  have hdel2 : z ∈ NonnestingDefs.avoiders (n - 2) Λ := by
    have hnn : n - 2 + 1 = n - 1 := by omega
    have h := delete_lowest_avoider
      ((w.filter (fun x => decide (1 < x))).map (fun x => x - 1))
      (n - 2) Λ (by simpa [hnn] using hdel1)
    simpa [z, hdelEq] using h
  have hbound (x : ℕ) (hx : x ∈ w) : 1 ≤ x ∧ x ≤ n := by
    have hxbase := hw.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have heq : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hidx (l : List ℕ) (a : ℕ) (hall : ∀ x ∈ l, 3 ≤ x) :
      (l.map (fun x => x - 2)).idxOf a = l.idxOf (a + 2) := by
    induction l with
    | nil => simp
    | cons x xs ih =>
      have hxge : 3 ≤ x := hall x (by simp)
      have hall' : ∀ y ∈ xs, 3 ≤ y := by
        intro y hy
        exact hall y (by simp [hy])
      by_cases hxa : x = a + 2
      · subst x
        simp [show a + 2 - 2 = a by omega]
      · have hne : x - 2 ≠ a := by omega
        simpa [List.idxOf_cons_ne _ hne,
          List.idxOf_cons_ne _ hxa] using congrArg Nat.succ (ih hall')
  have hfirstZ : ∀ a b, 1 ≤ a → a < b → b ≤ n - 2 →
      (z).idxOf a < (z).idxOf b := by
    intro a b ha hab hb
    let filt := w.filter (fun x => decide (2 < x))
    have hall : ∀ x ∈ filt, 3 ≤ x := by
      intro x hx
      have hx' := (List.mem_filter.mp hx).2
      simp at hx'
      omega
    have hmem (x : ℕ) (hx : 3 ≤ x ∧ x ≤ n) : x ∈ w := by
      have hcount : w.count x = 2 := by
        apply doubled_count n x w hw.1
        rw [List.mem_range'_1]
        omega
      exact List.mem_of_getElem? (count_two_positions x w hcount).2.1
    have hfa := first_order_after_filter w 2 (a + 2) (b + 2)
      (by omega) (by omega)
      (hmem (a + 2) ⟨by omega, by omega⟩)
      (hmem (b + 2) ⟨by omega, by omega⟩)
      ((primitive_later_order w n 2 hw hprimitive (Or.inr rfl) hhead)
        (a + 2) (b + 2) (by omega) (by omega) (by omega))
    have hia := hidx filt a hall
    have hib := hidx filt b hall
    change (filt.map (fun x => x - 2)).idxOf a <
      (filt.map (fun x => x - 2)).idxOf b
    rw [hia, hib]
    exact hfa
  refine ⟨hdel2, hfirstZ, ?_⟩
  have hpos := primitive_two_positions w n hw hn hhead hprimitive
  have hlen : w.length = 2 * n := by
    simpa [Nat.mul_comm] using hw.1.length_eq
  have hcount1 : w.count 1 = 2 := by
    apply doubled_count n 1 w hw.1
    rw [List.mem_range'_1]
    omega
  have hcount2 : w.count 2 = 2 := by
    apply doubled_count n 2 w hw.1
    rw [List.mem_range'_1]
    omega
  have h0 : w[0]? = some 2 := by
    simpa [List.head?_eq_getElem?] using hhead
  have h1 : w[1]? = some 1 := by
    have hp := (count_two_positions 1 w hcount1).2.1
    rw [hpos.1] at hp
    exact hp
  have h2 : w[2]? = some 3 := by
    have hcount3 : w.count 3 = 2 := by
      apply doubled_count n 3 w hw.1
      rw [List.mem_range'_1]
      omega
    have hp := (count_two_positions 3 w hcount3).2.1
    rw [hpos.2.1] at hp
    exact hp
  have h3 : w[3]? = some 2 := by
    have hp := (count_two_positions 2 w hcount2).2.2
    rw [hpos.2.2.1] at hp
    exact hp
  have h4 : w[4]? = some 1 := by
    have hp := (count_two_positions 1 w hcount1).2.2
    rw [hpos.2.2.2] at hp
    exact hp
  have htake : w.take 5 = [2, 1, 3, 2, 1] := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 5
    · have hicase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hicase with h | h | h | h | h <;>
        subst i <;> simp [h0, h1, h2, h3, h4]
    · have hge : 5 ≤ i := by omega
      simp [hge]
  let r := w.drop 5
  have hprefix : w = [2, 1, 3, 2, 1] ++ r := by
    calc
      w = w.take 5 ++ w.drop 5 := (List.take_append_drop 5 w).symm
      _ = [2, 1, 3, 2, 1] ++ r := by rw [htake]
  have hrCount1 : r.count 1 = 0 := by
    rw [hprefix, List.count_append] at hcount1
    simp at hcount1
    omega
  have hrCount2 : r.count 2 = 0 := by
    rw [hprefix, List.count_append] at hcount2
    simp at hcount2
    omega
  have hrHigh : ∀ x ∈ r, 3 ≤ x := by
    intro x hx
    have hxw : x ∈ w := by rw [hprefix]; simp [hx]
    have hxb := hbound x hxw
    have hne1 : x ≠ 1 := by
      intro heq
      subst x
      exact (List.count_eq_zero.mp hrCount1) hx
    have hne2 : x ≠ 2 := by
      intro heq
      subst x
      exact (List.count_eq_zero.mp hrCount2) hx
    omega
  have hrFilter : r.filter (fun x => decide (2 < x)) = r := by
    apply List.filter_eq_self.mpr
    intro x hx
    have hx2 : 2 < x := by have := hrHigh x hx; omega
    simp [hx2]
  have hfilter : w.filter (fun x => decide (2 < x)) = 3 :: r := by
    rw [hprefix]
    simp [hrFilter]
  have hz : z = 1 :: r.map (fun x => x - 2) := by
    simp [z, hfilter]
  have hrestore : shift 2 (r.map (fun x => x - 2)) = r := by
    simp only [shift, List.map_map]
    calc
      r.map ((fun x => x + 2) ∘ (fun x => x - 2)) = r.map id := by
        apply List.map_congr_left
        intro x hx
        simp only [Function.comp_apply, id_eq]
        have := hrHigh x hx
        omega
      _ = r := List.map_id r
  have hprimitiveZ : primitive z (n - 2) := by
    intro j hj hjn hjcut
    obtain ⟨u, v, heq, hulength, hu, hv⟩ := hjcut
    cases u with
    | nil =>
      simp at hulength
      omega
    | cons a us =>
      change z = a :: us ++ v at heq
      have ha : a = 1 := by
        have h := congrArg List.head? heq
        rw [hz] at h
        simpa using h.symm
      subst a
      have hrMap : r.map (fun x => x - 2) = us ++ v := by
        rw [hz] at heq
        simpa using heq
      have hrEq : r = shift 2 us ++ shift 2 v := by
        rw [← hrestore, hrMap]
        simp [shift, List.map_append]
      have hword : w = ([2, 1, 3, 2, 1] ++ shift 2 us) ++ shift 2 v := by
        rw [hprefix, hrEq]
        simp
      have hcutW : valueCut w (j + 2) := by
        refine ⟨[2, 1, 3, 2, 1] ++ shift 2 us, shift 2 v,
          hword, ?_, ?_, ?_⟩
        · simp [shift] at hulength ⊢
          omega
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            have hy' := hu y (by simp [hy])
            omega
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          have hy' := hv y hy
          omega
      exact hprimitive (j + 2) (by omega) (by omega) hcutW
  refine ⟨hprimitiveZ, ?_⟩
  have hshift : shift 2 z = 3 :: r := by
    rw [hz]
    change 3 :: shift 2 (r.map (fun x => x - 2)) = 3 :: r
    rw [hrestore]
  change w = [2, 1, 3, 2, 1] ++ (shift 2 z).tail
  rw [hshift]
  exact hprefix

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoTail

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoTail.primitive_two_tail
