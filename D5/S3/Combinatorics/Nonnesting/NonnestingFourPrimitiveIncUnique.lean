/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveIncUnique
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveIncUnique
   mirror-E: none(waiver:row-four-primitive-increasing-uniqueness)
   anchors: []
   utility: none
   digest: Proves uniqueness of primitive increasing-order row-four words. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveInc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveIncUnique

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing
open D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert
open D5.S3.Combinatorics.Nonnesting.NonnestingFourRecursive
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveInc
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount

theorem primitive_increasing_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ w : increasingWords n, primitive w.1 n := by
  have crossing_primitive_iff (r : List ℕ) (n : ℕ)
      (hv : (1 :: r) ∈ NonnestingDefs.avoiders n
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
      (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
        ((1 :: r)).idxOf a < ((1 :: r)).idxOf b)
      (hn : 1 ≤ n) :
      primitive (1 :: 2 :: 1 :: shift 1 r) (n + 1) ↔
        primitive (1 :: r) n := by
    have crossing_cut_iff (r : List ℕ) (n k : ℕ)
        (hv : (1 :: r) ∈ NonnestingDefs.avoiders n
          [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
        (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
          ((1 :: r)).idxOf a < ((1 :: r)).idxOf b)
        (hk : 2 ≤ k ∧ k < n + 1) :
        valueCut (1 :: 2 :: 1 :: shift 1 r) k ↔ valueCut (1 :: r) (k - 1) := by
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
      let v := 1 :: r
      let w := 1 :: 2 :: 1 :: shift 1 r
      have hw : w ∈ NonnestingDefs.avoiders (n + 1)
          [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] :=
        crossing_insert r n hv
      have hfirstW : ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
          (w).idxOf a < (w).idxOf b :=
        crossing_insert_first_order r n hfirst
      have hj : 1 ≤ k - 1 ∧ k - 1 < n := by omega
      have hs : secondPos k w = secondPos (k - 1) v + 2 := by
        have hp := (crossing_positions r n (k - 1) hv ⟨by omega, by omega⟩).2
        have heq : k - 1 + 1 = k := by omega
        simpa [v, w, heq] using hp
      have hfk : (w).idxOf (k + 1) = (v).idxOf k + 2 := by
        have hp := (crossing_positions r n k hv ⟨by omega, by omega⟩).1
        have hneq : (v).idxOf k ≠ 0 := by
          intro heq
          have hkcount : v.count k = 2 := by
            apply doubled_count n k v hv.1
            rw [List.mem_range'_1]
            omega
          have hval := (count_two_positions k v hkcount).2.1
          rw [heq] at hval
          simp [v] at hval
          omega
        simpa [v, w, hneq] using hp
      rw [increasing_cut_iff w (n + 1) k hw hfirstW (by omega)]
      rw [increasing_cut_iff v n (k - 1) hv hfirst hj]
      rw [hs, hfk]
      have hkval : k - 1 + 1 = k := by omega
      rw [hkval]
      omega
    let v := 1 :: r
    let w := 1 :: 2 :: 1 :: shift 1 r
    have hw : w ∈ NonnestingDefs.avoiders (n + 1)
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] :=
      crossing_insert r n hv
    have hfirstW : ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
        (w).idxOf a < (w).idxOf b :=
      crossing_insert_first_order r n hfirst
    constructor
    · intro hp j hj hjn hjcut
      have hiff := crossing_cut_iff r n (j + 1) hv hfirst
        (by omega : 2 ≤ j + 1 ∧ j + 1 < n + 1)
      have hcutW : valueCut w (j + 1) := by
        apply hiff.mpr
        simpa [v, Nat.add_sub_cancel_right] using hjcut
      exact hp (j + 1) (by omega) (by omega) hcutW
    · intro hp k hk hkn hkcut
      by_cases hk1 : k = 1
      · subst k
        have hsep := (increasing_cut_iff w (n + 1) 1 hw hfirstW
          (by omega : 1 ≤ 1 ∧ 1 < n + 1)).mp hkcut
        have hs : secondPos 1 w = 2 := by
          simp [w, secondPos]
        have hf : (w).idxOf 2 = 1 := by simp [w]
        rw [hs, hf] at hsep
        omega
      · have hiff := crossing_cut_iff r n k hv hfirst (by omega)
        have hcutV : valueCut v (k - 1) := hiff.mp hkcut
        exact hp (k - 1) (by omega) (by omega) hcutV
  induction n, hn using Nat.le_induction with
  | base =>
    have hsmall : [1, 1] ∈ NonnestingDefs.avoiders 1
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] := by
      have hno (σ : List ℕ) (hlen : σ.length = 4) :
          ¬ NonnestingDefs.Occurs σ [1, 1] := by
        intro hocc
        obtain ⟨x, _, _, hsub, _⟩ := hocc
        have hle := hsub.length_le
        simp [hlen] at hle
      refine ⟨by simp, hno _ (by decide), hno _ (by decide), ?_⟩
      intro σ hσ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with hσ | hσ | hσ | hσ <;> subst σ <;> exact hno _ (by decide)
    let w : increasingWords 1 := ⟨[1, 1], hsmall, by
      intro a b ha hab hb
      omega⟩
    exact ⟨w, by intro k hk hlt; omega⟩
  | succ j hj ih =>
    obtain ⟨v, hvprim⟩ := ih
    have hhead : v.1 = 1 :: v.1.tail := by
      have hlen : v.1.length = 2 * j := by
        simpa [Nat.mul_comm] using v.2.1.1.length_eq
      cases heq : v.1 with
      | nil => simp [heq] at hlen; omega
      | cons x r =>
        have hxb : 1 ≤ x ∧ x ≤ j := by
          have hxbase : x ∈ (List.range' 1 j).flatMap (fun i => [i, i]) :=
            v.2.1.1.mem_iff.mp (by rw [heq]; simp)
          obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
          have hx : x = i := by simpa using hxi
          subst x
          rw [List.mem_range'_1] at hi
          omega
        have hx : x = 1 := by
          by_contra hne
          have hlt := v.2.2 1 x (by omega) (by omega) hxb.2
          rw [heq] at hlt
          have hf : ((x :: r)).idxOf x = 0 := by simp []
          omega
        simp [hx]
    let r := v.1.tail
    have hv : (1 :: r) ∈ NonnestingDefs.avoiders j
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] :=
      hhead ▸ v.2.1
    have hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ j →
        ((1 :: r)).idxOf a < ((1 :: r)).idxOf b :=
      hhead ▸ v.2.2
    let w : increasingWords (j + 1) :=
      ⟨1 :: 2 :: 1 :: shift 1 r, crossing_insert r j hv,
        crossing_insert_first_order r j hfirst⟩
    refine ⟨w, ?_⟩
    exact (crossing_primitive_iff r j hv hfirst hj).mpr (hhead ▸ hvprim)

theorem primitive_increasing_unique (n : ℕ) (hn : 1 ≤ n)
    (u v : increasingWords n) (hu : primitive u.1 n) (hv : primitive v.1 n) :
    u = v := by
  have crossing_primitive_iff (r : List ℕ) (n : ℕ)
      (hv : (1 :: r) ∈ NonnestingDefs.avoiders n
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
      (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
        ((1 :: r)).idxOf a < ((1 :: r)).idxOf b)
      (hn : 1 ≤ n) :
      primitive (1 :: 2 :: 1 :: shift 1 r) (n + 1) ↔
        primitive (1 :: r) n := by
    have crossing_cut_iff (r : List ℕ) (n k : ℕ)
        (hv : (1 :: r) ∈ NonnestingDefs.avoiders n
          [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
        (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
          ((1 :: r)).idxOf a < ((1 :: r)).idxOf b)
        (hk : 2 ≤ k ∧ k < n + 1) :
        valueCut (1 :: 2 :: 1 :: shift 1 r) k ↔ valueCut (1 :: r) (k - 1) := by
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
      let v := 1 :: r
      let w := 1 :: 2 :: 1 :: shift 1 r
      have hw : w ∈ NonnestingDefs.avoiders (n + 1)
          [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] :=
        crossing_insert r n hv
      have hfirstW : ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
          (w).idxOf a < (w).idxOf b :=
        crossing_insert_first_order r n hfirst
      have hj : 1 ≤ k - 1 ∧ k - 1 < n := by omega
      have hs : secondPos k w = secondPos (k - 1) v + 2 := by
        have hp := (crossing_positions r n (k - 1) hv ⟨by omega, by omega⟩).2
        have heq : k - 1 + 1 = k := by omega
        simpa [v, w, heq] using hp
      have hfk : (w).idxOf (k + 1) = (v).idxOf k + 2 := by
        have hp := (crossing_positions r n k hv ⟨by omega, by omega⟩).1
        have hneq : (v).idxOf k ≠ 0 := by
          intro heq
          have hkcount : v.count k = 2 := by
            apply doubled_count n k v hv.1
            rw [List.mem_range'_1]
            omega
          have hval := (count_two_positions k v hkcount).2.1
          rw [heq] at hval
          simp [v] at hval
          omega
        simpa [v, w, hneq] using hp
      rw [increasing_cut_iff w (n + 1) k hw hfirstW (by omega)]
      rw [increasing_cut_iff v n (k - 1) hv hfirst hj]
      rw [hs, hfk]
      have hkval : k - 1 + 1 = k := by omega
      rw [hkval]
      omega
    let v := 1 :: r
    let w := 1 :: 2 :: 1 :: shift 1 r
    have hw : w ∈ NonnestingDefs.avoiders (n + 1)
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] :=
      crossing_insert r n hv
    have hfirstW : ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
        (w).idxOf a < (w).idxOf b :=
      crossing_insert_first_order r n hfirst
    constructor
    · intro hp j hj hjn hjcut
      have hiff := crossing_cut_iff r n (j + 1) hv hfirst
        (by omega : 2 ≤ j + 1 ∧ j + 1 < n + 1)
      have hcutW : valueCut w (j + 1) := by
        apply hiff.mpr
        simpa [v, Nat.add_sub_cancel_right] using hjcut
      exact hp (j + 1) (by omega) (by omega) hcutW
    · intro hp k hk hkn hkcut
      by_cases hk1 : k = 1
      · subst k
        have hsep := (increasing_cut_iff w (n + 1) 1 hw hfirstW
          (by omega : 1 ≤ 1 ∧ 1 < n + 1)).mp hkcut
        have hs : secondPos 1 w = 2 := by
          simp [w, secondPos]
        have hf : (w).idxOf 2 = 1 := by simp [w]
        rw [hs, hf] at hsep
        omega
      · have hiff := crossing_cut_iff r n k hv hfirst (by omega)
        have hcutV : valueCut v (k - 1) := hiff.mp hkcut
        exact hp (k - 1) (by omega) (by omega) hcutV
  have increasing_delete_lowest (w : List ℕ) (n : ℕ)
      (hw : w ∈ NonnestingDefs.avoiders (n + 1)
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
      (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
        (w).idxOf a < (w).idxOf b) :
      let v := (w.filter (fun x => decide (1 < x))).map (fun x => x - 1)
      v ∈ NonnestingDefs.avoiders n
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] ∧
        ∀ a b, 1 ≤ a → a < b → b ≤ n → (v).idxOf a < (v).idxOf b := by
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
    let u := w.filter (fun x => decide (1 < x))
    let v := u.map (fun x => x - 1)
    have huPositive : ∀ x ∈ u, 1 < x := by
      intro x hx
      simpa [u] using (List.mem_filter.mp hx).2
    have hrestore : v.map (fun x => x + 1) = u := by
      unfold v
      rw [List.map_map]
      calc
        u.map ((fun x => x + 1) ∘ (fun x => x - 1)) = u.map id := by
          apply List.map_congr_left
          intro x hx
          simp only [Function.comp_apply, id_eq]
          have := huPositive x hx
          omega
        _ = u := List.map_id u
    have hidx (l : List ℕ) (a : ℕ) :
        (l.map (fun x => x + 1)).idxOf (a + 1) = l.idxOf a := by
      induction l with
      | nil => simp
      | cons x xs ih =>
        by_cases hxa : x = a
        · subst x
          simp
        · have hne : x + 1 ≠ a + 1 := by omega
          simp [List.idxOf_cons_ne _ hne, List.idxOf_cons_ne _ hxa, ih]
    have hv : v ∈ NonnestingDefs.avoiders n Λ :=
      delete_lowest_avoider w n Λ hw
    change v ∈ NonnestingDefs.avoiders n Λ ∧ _
    refine ⟨hv, ?_⟩
    intro a b ha hab hbn
    have hmem (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n + 1) : x ∈ w := by
      have hrange : x ∈ List.range' 1 (n + 1) := by
        rw [List.mem_range'_1]
        omega
      exact List.mem_of_getElem?
        (count_two_positions x w (doubled_count (n + 1) x w hw.1 hrange)).2.1
    have horder := first_order_after_filter w 1 (a + 1) (b + 1)
      (by omega) (by omega)
      (hmem (a + 1) ⟨by omega, by omega⟩)
      (hmem (b + 1) ⟨by omega, by omega⟩)
      (hfirst (a + 1) (b + 1) (by omega) (by omega) (by omega))
    change u.idxOf (a + 1) < u.idxOf (b + 1) at horder
    rw [← hrestore, hidx v a, hidx v b] at horder
    exact horder
  induction n, hn using Nat.le_induction with
  | base =>
    have hone (t : increasingWords 1) : t.1 = [1, 1] := by
      have hlen : t.1.length = 2 := by
        simpa using t.2.1.1.length_eq
      obtain ⟨a, b, heq⟩ := List.length_eq_two.mp hlen
      have hval (x : ℕ) (hx : x ∈ t.1) : x = 1 := by
        have hbase := t.2.1.1.mem_iff.mp hx
        simpa using hbase
      have ha := hval a (by rw [heq]; simp)
      have hb := hval b (by rw [heq]; simp)
      simp [heq, ha, hb]
    exact Subtype.ext ((hone u).trans (hone v).symm)
  | succ j hj ih =>
    have hcross (t : increasingWords (j + 1)) (ht : primitive t.1 (j + 1)) :
        ∃ r : List ℕ,
          t.1 = 1 :: 2 :: 1 :: shift 1 r ∧
          (1 :: r) ∈ NonnestingDefs.avoiders j
            [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] ∧
          (∀ a b, 1 ≤ a → a < b → b ≤ j →
            ((1 :: r)).idxOf a < ((1 :: r)).idxOf b) ∧
          primitive (1 :: r) j := by
      let low := (t.1.filter (fun x => decide (1 < x))).map (fun x => x - 1)
      have hsmall := increasing_delete_lowest t.1 j t.2.1 t.2.2
      have hrec := increasing_reconstruct t.1 j t.2.1 hj t.2.2
      rcases hrec with hcut | ⟨r, hr, hword⟩
      · have hpos : ∀ x ∈ low, 1 ≤ x := by
          intro x hx
          have hxbase : x ∈ (List.range' 1 j).flatMap (fun i => [i, i]) :=
            hsmall.1.1.mem_iff.mp hx
          obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
          have heq : x = i := by simpa using hxi
          subst x
          rw [List.mem_range'_1] at hi
          omega
        have hvalueCut : valueCut t.1 1 := by
          rw [hcut]
          refine ⟨[1, 1], shift 1 low, rfl, by decide, by simp, ?_⟩
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          have := hpos y hy
          omega
        exact False.elim (ht 1 (by omega) (by omega) hvalueCut)
      · have hsmall' : (1 :: r) ∈ NonnestingDefs.avoiders j
            [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] := by
          simpa [low, hr] using hsmall.1
        have hfirst' : ∀ a b, 1 ≤ a → a < b → b ≤ j →
            ((1 :: r)).idxOf a < ((1 :: r)).idxOf b := by
          simpa [low, hr] using hsmall.2
        have hprimitive' : primitive (1 :: r) j :=
          (crossing_primitive_iff r j hsmall' hfirst' hj).mp (hword ▸ ht)
        exact ⟨r, hword, hsmall', hfirst', hprimitive'⟩
    obtain ⟨r, huword, hur, hufirst, huprim⟩ := hcross u hu
    obtain ⟨s, hvword, hvs, hvfirst, hvprim⟩ := hcross v hv
    let u' : increasingWords j := ⟨1 :: r, hur, hufirst⟩
    let v' : increasingWords j := ⟨1 :: s, hvs, hvfirst⟩
    have hsmallEq : u' = v' := ih u' v' huprim hvprim
    have hrs : r = s := by
      have hval := congrArg Subtype.val hsmallEq
      simp [u', v'] at hval
      exact hval
    apply Subtype.ext
    rw [huword, hvword, hrs]

#print axioms primitive_increasing_unique
#print axioms primitive_increasing_exists

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveIncUnique
