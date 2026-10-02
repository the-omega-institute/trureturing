/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowConverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingRoyalLowConverse
   mirror-E: none(waiver:royal-low-gap-converse)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Converts good gaps and first-order restrictions into low-row pattern avoidance. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBijection
import D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowGap
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalShape
import Mathlib.Combinatorics.Enumerative.DyckWord
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBlocks
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
namespace D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowConverse
open scoped symmDiff
open DyckStep
open NonnestingBasicRoyalEncoding
open DyckStep NonnestingBasicRoyalEncoding NonnestingBasicRoyalShape NonnestingBasicOrders
open DyckStep NonnestingBasicRoyalEncoding NonnestingBasicRoyalShape
open NonnestingBasicRoyalBlocks
local notation "toggle" =>
  (fun (active : Finset ℕ) (letter : ℕ) => active ∆ Singleton.singleton letter)
theorem good_gaps_avoid_low (d : DyckWord) (w p : List ℕ)
    (hscan : scan ∅ w = d.toList)
    (hcount : ∀ a ∈ w, w.count a = 2)
    (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧ ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
    (hU : select U d.toList w = p) (hD : select D d.toList w = p)
    (hp : p.Nodup)
    (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
    (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p)
    (hgood : ∀ u v z : List DyckStep, d.toList = u ++ [D] ++ v ++ [D] ++ z → v.count D = 0 →
      (ht : u.count D + 1 < p.length) → p[u.count D] < p[u.count D + 1] →
      v = [] ∨ (v = [U] ∧ u.count U = u.count D + 1)) : ¬ NonnestingDefs.Occurs [1, 1, 3, 2] w ∧
    ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w := by
  classical
  have occurrencePositions (word : List ℕ) (letter index : ℕ) (copies : word.count letter = 2)
      (entry : word[index]? = some letter) :
      index = word.idxOf letter ∨ index = secondPos letter word := by
    obtain ⟨leading, between, suffix, absentP, absentB, absentS, rfl⟩ :=
      count_two_decomposition letter word copies
    have first : (leading ++ [letter] ++ between ++ [letter] ++ suffix).idxOf letter =
        leading.length := by simp [List.idxOf_append, absentP]
    have second : secondPos letter (leading ++ [letter] ++ between ++ [letter] ++ suffix) =
        leading.length + 1 + between.length := by
      simp [secondPos, List.idxOf_append, absentP, absentB, List.drop_append,
        List.drop_eq_nil_iff.mpr (by omega : leading.length ≤ leading.length + 1)]
    rw [first, second]
    have absentPrefix (offset : ℕ) : leading[offset]? ≠ some letter :=
      fun value => absentP (List.mem_of_getElem? value)
    have absentBetween (offset : ℕ) : between[offset]? ≠ some letter :=
      fun value => absentB (List.mem_of_getElem? value)
    have absentSuffix (offset : ℕ) : suffix[offset]? ≠ some letter :=
      fun value => absentS (List.mem_of_getElem? value)
    simp only [List.append_assoc, List.singleton_append, List.getElem?_append,
      List.getElem?_cons, List.length_cons, List.length_append] at entry
    split_ifs at entry <;> first
      | exact (absentPrefix _ entry).elim
      | exact (absentBetween _ entry).elim
      | exact (absentSuffix _ entry).elim
      | omega
  have secondOccurrence (word : List ℕ) (letter : ℕ)
      (copies : word.count letter = 2) : word[secondPos letter word]? = some letter := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition letter word copies
    have hs : secondPos letter (u ++ [letter] ++ v ++ [letter] ++ z) = u.length + 1 + v.length := by
      have hd : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr; omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hd]
    rw [hs]
    have hle : ¬ u.length + 1 + v.length < u.length := (by omega); simp [List.getElem?_append, hle]
    have heq : u.length + 1 + v.length - u.length = v.length + 1 := (by omega); rw [heq]; simp
  have occursTriple (word pattern : List ℕ) (size : NonnestingDefs.letters pattern = 3)
      (entries : pattern.all (fun label => decide (label = 1 ∨ label = 2 ∨ label = 3)) = true) :
      NonnestingDefs.Occurs pattern word ↔
        ∃ lower middle upper : ℕ, lower < middle ∧ middle < upper ∧
          lower ∈ word ∧ middle ∈ word ∧ upper ∈ word ∧
          (pattern.map fun label => if label = 1 then lower
            else if label = 2 then middle else upper).Sublist word := by
    simp only [List.all_eq_true, decide_eq_true_eq] at entries
    classical
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains; rw [size]
    constructor
    · rintro ⟨values, ordered, members, sublist, _⟩
      refine ⟨values 1, values 2, values 3, ordered 1 (by omega) (by omega),
        ordered 2 (by omega) (by omega), members 1 (by omega) (by omega),
        members 2 (by omega) (by omega), members 3 (by omega) (by omega), ?_⟩
      have image : (pattern.map fun label => if label = 1 then values 1
          else if label = 2 then values 2 else values 3) = pattern.map values := by
        apply List.map_congr_left; intro label member
        rcases entries label member with rfl | rfl | rfl <;> simp
      rw [image]; exact sublist
    · rintro ⟨lower, middle, upper, orderedLM, orderedMU, memberL, memberM, memberU, sublist⟩
      let values : ℕ → ℕ := fun label => if label = 1 then lower
        else if label = 2 then middle else upper
      refine ⟨values, ?_, ?_, sublist, by simp⟩
      · intro label positive bounded
        have alternatives : label = 1 ∨ label = 2 := (by omega)
        rcases alternatives with rfl | rfl <;> simp [values, orderedLM, orderedMU]
      · intro label positive bounded
        have alternatives : label = 1 ∨ label = 2 ∨ label = 3 := (by omega)
        rcases alternatives with rfl | rfl | rfl <;>
          simp [values, memberL, memberM, memberU]
  have low_local_test (w : List ℕ) (hcount : ∀ x ∈ w, w.count x = 2)
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧ ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) :
(∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
        ¬ (w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b) ∧
        ¬ (w.idxOf b < w.idxOf a ∧ w.idxOf a < w.idxOf c) ∧
        ¬ (w.idxOf a < w.idxOf b ∧ w.idxOf b < w.idxOf c ∧
          secondPos a w < w.idxOf c ∧ w.idxOf c < secondPos b w) ∧
        ¬ (w.idxOf b < w.idxOf c ∧ w.idxOf c < w.idxOf a ∧
          secondPos b w < w.idxOf a ∧ w.idxOf a < secondPos c w)) →
      (¬ NonnestingDefs.Occurs [1, 1, 3, 2] w ∧ ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w) := by
    classical
    have double_first_sublist_iff (w : List ℕ) (a b c : ℕ) (ha : w.count a = 2) :
        List.Sublist [a, a, c, b] w ↔ ∃ i j : ℕ, secondPos a w < i ∧ i < j ∧
            w[i]? = some c ∧ w[j]? = some b := by
      have secondAt (x : ℕ) (hx : w.count x = 2) : w[secondPos x w]? = some x := by
        exact secondOccurrence w x hx
      have occurrencePos (x i : ℕ) (hx : w.count x = 2)
          (hi : w[i]? = some x) : i = w.idxOf x ∨ i = secondPos x w := by
        exact occurrencePositions w x i hx hi
      constructor
      · intro hsub
        obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        have h0 : w[(f 0).val]? = some a := by
          rw [List.getElem?_eq_getElem (f 0).isLt]; simpa using congrArg some (hf (0 : Fin 4)).symm
        have h1 : w[(f 1).val]? = some a := by
          rw [List.getElem?_eq_getElem (f 1).isLt]; simpa using congrArg some (hf (1 : Fin 4)).symm
        have h2 : w[(f 2).val]? = some c := by
          rw [List.getElem?_eq_getElem (f 2).isLt]; simpa using congrArg some (hf (2 : Fin 4)).symm
        have h3 : w[(f 3).val]? = some b := by
          rw [List.getElem?_eq_getElem (f 3).isLt]; simpa using congrArg some (hf (3 : Fin 4)).symm
        have h01 : (f 0).val < (f 1).val := f.strictMono (show (0 : Fin 4) < 1 by decide)
        have h12 : (f 1).val < (f 2).val := f.strictMono (show (1 : Fin 4) < 2 by decide)
        have h23 : (f 2).val < (f 3).val := f.strictMono (show (2 : Fin 4) < 3 by decide)
        have hp0 := occurrencePos a _ ha h0; have hp1 := occurrencePos a _ ha h1
        have hfs : w.idxOf a < secondPos a w := by
          unfold secondPos; omega
        have heq1 : (f 1).val = secondPos a w := by
          rcases hp0 with hp0 | hp0 <;> rcases hp1 with hp1 | hp1 <;> omega
        exact ⟨(f 2).val, (f 3).val, by omega, h23, h2, h3⟩
      · rintro ⟨i, j, hsi, hij, hci, hbj⟩
        have hfirst : a ∈ w := by
          by_contra hnot
          have hz := List.count_eq_zero.mpr hnot; omega
        have hfaVal : w[w.idxOf a]? = some a := List.getElem?_idxOf hfirst
        have hsaVal := secondAt a ha
        have hfs : w.idxOf a < secondPos a w := by
          unfold secondPos; omega
        have hfi : w.idxOf a < i := hfs.trans hsi; have hfa : w.idxOf a < w.length :=
          (List.getElem?_eq_some_iff.mp hfaVal).1
        have hsa : secondPos a w < w.length := (List.getElem?_eq_some_iff.mp hsaVal).1
        have hii : i < w.length := (List.getElem?_eq_some_iff.mp hci).1
        have hjj : j < w.length := (List.getElem?_eq_some_iff.mp hbj).1
        have vfa : w[w.idxOf a] = a := (List.getElem?_eq_some_iff.mp hfaVal).2
        have vsa : w[secondPos a w] = a := (List.getElem?_eq_some_iff.mp hsaVal).2
        have vi : w[i] = c := (List.getElem?_eq_some_iff.mp hci).2
        have vj : w[j] = b := (List.getElem?_eq_some_iff.mp hbj).2; let p : Fin 4 → ℕ := fun k =>
          if k.val = 0 then w.idxOf a else
          if k.val = 1 then secondPos a w else
          if k.val = 2 then i else j
        have hp : ∀ k : Fin 4, p k < w.length := by
          intro k
          fin_cases k <;> simp [p, hfa, hsa, hii, hjj]
        let f : Fin 4 ↪o Fin w.length := OrderEmbedding.ofMapLEIff (fun k => ⟨p k, hp k⟩) (by
            intro k l
            fin_cases k <;> fin_cases l <;> simp [p] <;> omega)
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨f, ?_⟩
        intro k
        fin_cases k <;> simp [f, p, vfa, vsa, vi, vj]
    have occurs1132_iff (w : List ℕ) (hw : ∀ a ∈ w, w.count a = 2) :
        NonnestingDefs.Occurs [1, 1, 3, 2] w ↔ ∃ a b c : ℕ, a < b ∧ b < c ∧ a ∈ w ∧
            ∃ i j : ℕ, secondPos a w < i ∧ i < j ∧ w[i]? = some c ∧ w[j]? = some b := by
      rw [occursTriple w [1, 1, 3, 2] (by decide)
        (by decide)]
      constructor
      · rintro ⟨a, b, c, hab, hbc, ha, hb, hc, sublist⟩
        have positions := (double_first_sublist_iff w a b c (hw a ha)).mp
          (by simpa using sublist)
        exact ⟨a, b, c, hab, hbc, ha, positions⟩
      · rintro ⟨a, b, c, hab, hbc, ha, i, j, hsi, hij, hci, hbj⟩
        refine ⟨a, b, c, hab, hbc, (ha), (List.mem_of_getElem? hbj), (List.mem_of_getElem? hci), ?_⟩
        have sublist := (double_first_sublist_iff w a b c (hw a ha)).mpr
          ⟨i, j, hsi, hij, hci, hbj⟩
        simpa using sublist
    have occurs2213_iff (w : List ℕ) (hw : ∀ a ∈ w, w.count a = 2) :
        NonnestingDefs.Occurs [2, 2, 1, 3] w ↔ ∃ a b c : ℕ, a < b ∧ b < c ∧ b ∈ w ∧
            ∃ i j : ℕ, secondPos b w < i ∧ i < j ∧ w[i]? = some a ∧ w[j]? = some c := by
      rw [occursTriple w [2, 2, 1, 3] (by decide)
        (by decide)]
      constructor
      · rintro ⟨a, b, c, hab, hbc, ha, hb, hc, sublist⟩
        have positions := (double_first_sublist_iff w b c a (hw b hb)).mp
          (by simpa using sublist)
        exact ⟨a, b, c, hab, hbc, hb, positions⟩
      · rintro ⟨a, b, c, hab, hbc, hb, i, j, hsi, hij, hai, hcj⟩
        refine ⟨a, b, c, hab, hbc, (List.mem_of_getElem? hai), (hb), (List.mem_of_getElem? hcj), ?_⟩
        have sublist := (double_first_sublist_iff w b c a (hw b hb)).mpr
          ⟨i, j, hsi, hij, hai, hcj⟩
        simpa using sublist
    have horders := (nonnesting_iff_equal_orders w hcount).mp hnn
    have position (x i : ℕ) (hx : x ∈ w) (hi : w[i]? = some x) :
        i = w.idxOf x ∨ i = secondPos x w := by
      exact occurrencePositions w x i (hcount x hx) hi
    have firstNe (x y : ℕ) (hx : x ∈ w) (hy : y ∈ w) (hxy : x ≠ y) : w.idxOf x ≠ w.idxOf y := by
      intro h; have hfx := List.getElem?_idxOf hx; have hfy := List.getElem?_idxOf hy
      rw [h] at hfx; exact hxy (Option.some.inj (hfx.symm.trans hfy))
    have firstSecond (x : ℕ) : w.idxOf x < secondPos x w := by
      unfold secondPos; omega
    have orderedPositions (left right : ℕ) (left_mem : left ∈ w)
        (right_mem : right ∈ w) (different : left ≠ right) :
        (w.idxOf left < w.idxOf right ∧ secondPos left w < secondPos right w) ∨
        (w.idxOf right < w.idxOf left ∧ secondPos right w < secondPos left w) := by
      have indices_differ := firstNe left right left_mem right_mem different
      by_cases order : w.idxOf left < w.idxOf right
      · exact Or.inl ⟨order, horders left left_mem right right_mem order⟩
      · have opposite : w.idxOf right < w.idxOf left := by omega
        exact Or.inr ⟨opposite, horders right right_mem left left_mem opposite⟩
    intro htest
    constructor
    · intro hocc
      obtain ⟨a, b, c, hab, hbc, ha, i, j, hsi, hij, hci, hbj⟩ :=
        (occurs1132_iff w hcount).mp hocc
      have hc : c ∈ w := List.mem_of_getElem? hci; have hb : b ∈ w := List.mem_of_getElem? hbj
      have obstruction := htest a b c ha hb hc hab hbc
      have orderAB := orderedPositions a b ha hb (by omega)
      have orderAC := orderedPositions a c ha hc (by omega)
      have orderBC := orderedPositions b c hb hc (by omega); have posI := position c i hc hci
      have posJ := position b j hb hbj; have firstA := firstSecond a; have firstB := firstSecond b
      have firstC := firstSecond c; omega
    · intro hocc
      obtain ⟨a, b, c, hab, hbc, hb, i, j, hsi, hij, hai, hcj⟩ :=
        (occurs2213_iff w hcount).mp hocc
      have ha : a ∈ w := List.mem_of_getElem? hai; have hc : c ∈ w := List.mem_of_getElem? hcj
      have obstruction := htest a b c ha hb hc hab hbc
      have orderAB := orderedPositions a b ha hb (by omega)
      have orderAC := orderedPositions a c ha hc (by omega)
      have orderBC := orderedPositions b c hb hc (by omega); have posI := position a i ha hai
      have posJ := position c j hc hcj; have firstA := firstSecond a; have firstB := firstSecond b
      have firstC := firstSecond c; omega
  have foldl_toggle_parity (s : Finset ℕ) (w : List ℕ) (a : ℕ) : a ∈ w.foldl toggle s ↔
        if w.count a % 2 = 0 then a ∈ s else a ∉ s := by
    have toggle_eq (active : Finset ℕ) (letter : ℕ) : toggle active letter =
          if letter ∈ active then active.erase letter else insert letter active := by
      ext value
      by_cases present : letter ∈ active <;>
        by_cases same : value = letter <;>
        simp [Finset.mem_symmDiff, present, same]
    have mem_toggle_iff (s : Finset ℕ) (a b : ℕ) :
        a ∈ toggle s b ↔ if a = b then a ∉ s else a ∈ s := by
      by_cases hab : a = b
      · subst b
        by_cases ha : a ∈ s <;> simp [toggle_eq, ha]
      · by_cases hb : b ∈ s <;> simp [toggle_eq, hab, hb]
    induction w generalizing s with
    | nil => simp
    | cons b w ih =>
      simp only [List.foldl_cons, ih, mem_toggle_iff]
      by_cases hab : a = b
      · subst b
        by_cases hpar : w.count a % 2 = 0
        · have hnext : (w.count a + 1) % 2 = 1 := by omega
          simp [hpar, hnext]
        · have hnext : (w.count a + 1) % 2 = 0 := by
            have hbound := Nat.mod_lt (w.count a) (by omega : 0 < 2); omega
          simp [hpar, hnext]
      · simp [hab, Ne.symm hab]
  have scan_getElem? (s : Finset ℕ) (w : List ℕ) (i : ℕ) : (scan s w)[i]? =
        (w[i]?).map (fun a => if a ∈ (w.take i).foldl toggle s then D else U) := by
    induction w generalizing s i with
    | nil => simp [scan]
    | cons b w ih =>
      cases i with
      | zero => by_cases h : b ∈ s <;> simp [scan, h]
      | succ i => by_cases h : b ∈ s <;> simp [scan, h, ih] <;> rfl
  have scan_length (s : Finset ℕ) (w : List ℕ) : (scan s w).length = w.length := by
    induction w generalizing s with
    | nil => rfl
    | cons a w ih =>
      by_cases h : a ∈ s <;> simp [scan, h, ih]
  have select_position (t : DyckStep) (d : List DyckStep) (w : List ℕ)
      (i : ℕ) (ht : d[i]? = some t) : (select t d w)[(d.take i).count t]? = w[i]? := by
    induction d generalizing w i with
    | nil => simp at ht
    | cons s d ih =>
      cases w with
      | nil =>
        cases i with
        | zero => simp [select]
        | succ i => simp [select]
      | cons a w =>
        cases i with
        | zero =>
          have hs : s = t := (by simpa using ht); subst s; simp [select]
        | succ i =>
          have ht' : d[i]? = some t := (by simpa using ht)
          by_cases hs : s = t
          · subst s
            simpa [select, List.take_succ_cons] using ih w i ht'
          · simpa [select, hs, List.take_succ_cons] using ih w i ht'
  have crossing_has_later_upstep (d : List DyckStep) (w p : List ℕ)
      (hscan : scan ∅ w = d) (hcount : ∀ a ∈ w, w.count a = 2)
      (hU : select U d w = p) (hD : select D d w = p) (hp : p.Nodup)
      (u v z : List DyckStep) (hsplit : d = u ++ [D] ++ v ++ [D] ++ z)
      (hnoD : v.count D = 0) (ht : u.count D + 1 < p.length)
      (k : ℕ) (hk : k < p.length) (hlater : u.count D + 1 < k)
      (hcross : secondPos (p[u.count D]'(by omega)) w < w.idxOf (p[k]'hk) ∧
        w.idxOf (p[k]'hk) < secondPos (p[u.count D + 1]'ht) w) :
      ∃ q, q < v.length ∧ v[q]? = some U ∧ u.count D + 1 < u.count U + (v.take q).count U := by
    have select_sublist (t : DyckStep) (d : List DyckStep) (w : List ℕ) :
        List.Sublist (select t d w) w := by
      induction d generalizing w with
      | nil => simp [select]
      | cons x d ih =>
        cases w with
        | nil => simp [select]
        | cons a w =>
          by_cases hx : x = t
          · simpa [select, hx] using (ih w).cons_cons a
          · simpa [select, hx] using (ih w).cons a
    have toggle_eq (active : Finset ℕ) (letter : ℕ) : toggle active letter =
          if letter ∈ active then active.erase letter else insert letter active := by
      ext value
      by_cases present : letter ∈ active <;>
        by_cases same : value = letter <;>
        simp [Finset.mem_symmDiff, present, same]
    have mem_toggle_iff (s : Finset ℕ) (a b : ℕ) :
        a ∈ toggle s b ↔ if a = b then a ∉ s else a ∈ s := by
      by_cases hab : a = b
      · subst b
        by_cases ha : a ∈ s <;> simp [toggle_eq, ha]
      · by_cases hb : b ∈ s <;> simp [toggle_eq, hab, hb]
    have scan_first_second (a : ℕ) (w : List ℕ) (hw : w.count a = 2) :
        (scan ∅ w)[w.idxOf a]? = some U ∧
          (scan ∅ w)[NonnestingBasicOrders.secondPos a w]? = some D := by
      obtain ⟨u, v, z, hu, hv, _, rfl⟩ := NonnestingBasicOrders.count_two_decomposition a w hw
      have hf : (u ++ [a] ++ v ++ [a] ++ z).idxOf a = u.length := by
        simp [List.idxOf_append, hu]
      have hs : NonnestingBasicOrders.secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
          u.length + 1 + v.length := by
        have hdrop : u.drop (u.length + 1) = [] := by
          apply List.drop_eq_nil_iff.mpr; omega
        simp [NonnestingBasicOrders.secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
      constructor
      · rw [hf, scan_getElem?]
        simp [List.count_eq_zero.mpr hu, foldl_toggle_parity]
      · rw [hs, scan_getElem?]
        have hlen : (u ++ [a] ++ v).length = u.length + 1 + v.length := by
          simp; omega
        have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) := by
          simp [List.append_assoc]
        have ht : (u ++ [a] ++ v ++ [a] ++ z).take (u.length + 1 + v.length) = u ++ [a] ++ v := by
          rw [hword, ← hlen]; exact List.take_left
        have hget : (u ++ [a] ++ v ++ [a] ++ z)[u.length + 1 + v.length]? = some a := by
          rw [hword, ← hlen]; simp
        have hu0 : u.count a = 0 := List.count_eq_zero.mpr hu
        have hv0 : v.count a = 0 := List.count_eq_zero.mpr hv
        have hbefore : a ∉ u.foldl toggle ∅ := by
          have hpar := foldl_toggle_parity ∅ u a; simpa [hu0] using hpar
        have hafter : a ∈ toggle (u.foldl toggle ∅) a := by
          simp [mem_toggle_iff, hbefore]
        rw [hget, Option.map_some, ht]; simp [foldl_toggle_parity, hv0, hafter]
    have scan_tag_position (t : DyckStep) (w : List ℕ) (a i : ℕ)
        (hc : w.count a = 2) (hwi : w[i]? = some a)
        (hti : (scan ∅ w)[i]? = some t) : i = if t = U then w.idxOf a
            else NonnestingBasicOrders.secondPos a w := by
      have hposition : i = w.idxOf a ∨ i = NonnestingBasicOrders.secondPos a w := by
        obtain ⟨u, v, z, hu, hv, hz, rfl⟩ := NonnestingBasicOrders.count_two_decomposition a w hc
        have hfirst : (u ++ [a] ++ v ++ [a] ++ z).idxOf a = u.length := by
          simp [List.idxOf_append, hu]
        have hsecond : NonnestingBasicOrders.secondPos a
            (u ++ [a] ++ v ++ [a] ++ z) = u.length + 1 + v.length := by
          have hdrop : u.drop (u.length + 1) = [] := by
            apply List.drop_eq_nil_iff.mpr; omega
          simp [NonnestingBasicOrders.secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
        rw [hfirst, hsecond]
        by_cases h0 : i < u.length
        · have hmem : a ∈ u := by
            have h : u[i]? = some a := by
              simpa [List.getElem?_append, h0] using hwi
            exact List.mem_of_getElem? h
          exact (hu hmem).elim
        by_cases h1 : i = u.length
        · exact Or.inl h1
        by_cases h2 : i < u.length + 1 + v.length
        · have hmem : a ∈ v := by
            have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
              simpa [List.getElem?_append, h0] using hwi
            have heq : i - u.length = (i - u.length - 1) + 1 := (by omega); rw [heq] at hi'
            have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
              simpa using hi'
            have hlt : i - u.length - 1 < v.length := (by omega)
            have hiv : v[i - u.length - 1]? = some a := by
              simpa [List.getElem?_append, hlt] using hi''
            exact List.mem_of_getElem? hiv
          exact (hv hmem).elim
        by_cases h3 : i = u.length + 1 + v.length
        · exact Or.inr h3
        · have hmem : a ∈ z := by
            have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
              simpa [List.getElem?_append, h0] using hwi
            have heq : i - u.length = (i - u.length - 1) + 1 := (by omega); rw [heq] at hi'
            have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
              simpa using hi'
            have hle : ¬ i - u.length - 1 < v.length := (by omega)
            have hi''' : (a :: z)[i - u.length - 1 - v.length]? = some a := by
              simpa [List.getElem?_append, hle] using hi''
            have heq' : i - u.length - 1 - v.length =
                (i - u.length - 1 - v.length - 1) + 1 := by omega
            rw [heq'] at hi'''
            have hiz : z[i - u.length - 1 - v.length - 1]? = some a := by
              simpa using hi'''
            exact List.mem_of_getElem? hiz
          exact (hz hmem).elim
      obtain ⟨hfirst, hsecond⟩ := scan_first_second a w hc
      rcases hposition with hi | hi
      · cases t with
        | U => simpa using hi
        | D => rw [hi, hfirst] at hti; cases hti
      · cases t with
        | U => rw [hi, hsecond] at hti; cases hti
        | D => simpa using hi
    let i := u.length; let j := w.idxOf p[k]; let l := u.length + 1 + v.length
    have hlen : d.length = w.length := (by rw [← hscan]; exact scan_length ∅ w)
    have hdi : d[i]? = some D := (by simp [hsplit, i])
    have hdl : d[l]? = some D := by
      have hsplit' : d = (u ++ [D] ++ v) ++ [D] ++ z := by
        simpa [List.append_assoc] using hsplit
      rw [hsplit']
      have hl : l = (u ++ [D] ++ v).length := (by simp [l]; omega); rw [hl]; simp
    have hri : (d.take i).count D = u.count D := (by simp [hsplit, i])
    have hrl : (d.take l).count D = u.count D + 1 := by
      have hsplit' : d = (u ++ [D] ++ v) ++ [D] ++ z := by
        simpa [List.append_assoc] using hsplit
      rw [hsplit']
      have hl : l = (u ++ [D] ++ v).length := (by simp [l]; omega)
      have htake : ((u ++ [D] ++ v) ++ [D] ++ z).take l = u ++ [D] ++ v := by
        rw [hl]; simpa [List.append_assoc] using
          (List.take_left : ((u ++ [D] ++ v) ++ ([D] ++ z)).take
            (u ++ [D] ++ v).length = u ++ [D] ++ v)
      rw [htake]; simp [hnoD]
    have hpos (m r : ℕ) (htag : d[m]? = some D)
        (hrank : (d.take m).count D = r) (hr : r < p.length) : m = secondPos p[r] w := by
      have hs := select_position D d w m htag; rw [hD, hrank] at hs
      have hw : w[m]? = some p[r] := by
        rw [← hs]; exact List.getElem?_eq_getElem hr
      have hc : w.count p[r] = 2 := hcount p[r] (List.mem_of_getElem? hw)
      have htag' : (scan ∅ w)[m]? = some D := (by simpa [hscan] using htag)
      simpa using scan_tag_position D w p[r] m hc hw htag'
    have hwi := hpos i (u.count D) hdi hri (by omega); have hwl := hpos l (u.count D + 1) hdl hrl ht
    have hij : i < j := (by simpa [j, hwi] using hcross.1)
    have hjl : j < l := (by simpa [j, hwl] using hcross.2); let q := j - (i + 1)
    have hj : j = i + 1 + q := (by dsimp [q]; omega)
    have hq : q < v.length := (by dsimp [i, l] at *; omega); have hpmem : p[k] ∈ w :=
      (select_sublist U d w).subset (by rw [hU]; exact List.getElem_mem hk)
    have htag : d[j]? = some U := by
      rw [← hscan]; simpa [j] using (scan_first_second p[k] w (hcount p[k] hpmem)).1
    have hvq : v[q]? = some U := by
      have hsplit' : d = u ++ (D :: v ++ [D] ++ z) := by
        simpa [List.append_assoc] using hsplit
      have hj' : j - u.length = q + 1 := (by dsimp [i] at hj; omega)
      rw [hsplit', List.getElem?_append_right (by dsimp [i] at hij; omega), hj'] at htag
      simpa [List.getElem?_append_left hq] using htag
    have hrj : (d.take j).count U = u.count U + (v.take q).count U := by
      have hsplit' : d = (u ++ [D]) ++ (v ++ [D] ++ z) := by
        simpa [List.append_assoc] using hsplit
      have hj' : j = (u ++ [D]).length + q := (by simp [hj, i])
      have htake : d.take j = (u ++ [D]) ++ v.take q := by
        rw [hsplit', hj', List.take_append, Nat.add_sub_cancel_left]
        have hv : (v ++ [D] ++ z).take q = v.take q := by
          simpa [List.append_assoc] using
            (List.take_append_of_le_length (by omega : q ≤ v.length) :
              (v ++ ([D] ++ z)).take q = v.take q)
        rw [hv]; have hprefix : (u ++ [D]).take ((u ++ [D]).length + q) = u ++ [D] :=
          List.take_of_length_le (by omega)
        rw [hprefix]
      rw [htake]; simp
    have hrank : (d.take j).count U = k := by
      have hs := select_position U d w j htag; rw [hU] at hs
      have hval : p[(d.take j).count U]? = some p[k] := by
        rw [hs]; simpa [j] using List.getElem?_idxOf hpmem
      obtain ⟨hrlen, hrval⟩ := List.getElem?_eq_some_iff.mp hval
      exact (hp.getElem_inj_iff (hi := hrlen) (hj := hk)).mp hrval
    refine ⟨q, hq, hvq, ?_⟩
    rw [← hrj]; omega
  have indexed_downstep_gap (s : List DyckStep) (k : ℕ) (hk : k + 1 < s.count D) :
      ∃ u v z : List DyckStep, s = u ++ [D] ++ v ++ [D] ++ z ∧ v.count D = 0 ∧ u.count D = k := by
    have firstD : ∀ (t : List DyckStep), 0 < t.count D →
        ∃ v z : List DyckStep, t = v ++ D :: z ∧ v.count D = 0 := by
      intro t
      induction t with
      | nil => simp
      | cons a t ih =>
        cases a with
        | D =>
          intro _; exact ⟨[], t, rfl, rfl⟩
        | U =>
          intro h
          have ht : 0 < t.count D := (by simpa using h)
          obtain ⟨v, z, hv, hzero⟩ := ih ht
          exact ⟨U :: v, z, by simp [hv], by simpa using hzero⟩
    induction s generalizing k with
    | nil => simp at hk
    | cons a s ih =>
      cases a with
      | U =>
        have hs : k + 1 < s.count D := (by simpa using hk)
        obtain ⟨u, v, z, hsplit, hzero, hcount⟩ := ih k hs
        exact ⟨U :: u, v, z, by simp [hsplit], hzero, by simpa using hcount⟩
      | D =>
        cases k with
        | zero =>
          have hs : 0 < s.count D := (by simpa using hk)
          obtain ⟨v, z, hsplit, hzero⟩ := firstD s hs
          exact ⟨[], v, z, by simp [hsplit], hzero, rfl⟩
        | succ k =>
          have hs : k + 1 < s.count D := (by simpa using hk)
          obtain ⟨u, v, z, hsplit, hzero, hcount⟩ := ih k hs
          exact ⟨D :: u, v, z, by simp [hsplit], hzero, by simpa using hcount⟩
  have scan_append (s : Finset ℕ) (u v : List ℕ) :
      scan s (u ++ v) = scan s u ++ scan (u.foldl toggle s) v := by
    induction u generalizing s with
    | nil => simp [scan]
    | cons a u ih =>
      by_cases h : a ∈ s <;> simp [scan, h, ih, List.foldl_cons]
  have select_append (t : DyckStep) (d e : List DyckStep) (u v : List ℕ) (h : d.length = u.length) :
      select t (d ++ e) (u ++ v) = select t d u ++ select t e v := by
    induction d generalizing u with
    | nil =>
      have : u = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm); subst u; simp [select]
    | cons x d ih =>
      cases u with
      | nil => simp at h
      | cons a u =>
        have ht : d.length = u.length := (by simpa using h)
        by_cases hx : x = t <;> simp [select, hx, ih u ht]
  have select_length (t : DyckStep) (d : List DyckStep) (w : List ℕ)
      (h : d.length = w.length) : (select t d w).length = d.count t := by
    induction d generalizing w with
    | nil =>
      have : w = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm); subst w; simp [select]
    | cons x d ih =>
      cases w with
      | nil => simp at h
      | cons a w =>
        have ht : d.length = w.length := (by simpa using h)
        by_cases hx : x = t <;> simp [select, hx, ih w ht]
  have tagged_select_sublist (t : DyckStep) (d : List DyckStep) (w : List ℕ) :
      List.Sublist ((select t d w).map (t, ·)) (d.zip w) := by
    induction d generalizing w with
    | nil => simp [select]
    | cons x d ih =>
      cases w with
      | nil => simp [select]
      | cons a w =>
        by_cases hx : x = t
        · subst x
          simpa [select] using (ih w).cons_cons (t, a)
        · simpa [select, hx] using (ih w).cons (x, a)
  have good_gaps_exclude_crossings (d : DyckWord) (w p : List ℕ) (hscan : scan ∅ w = d.toList)
      (hcount : ∀ a ∈ w, w.count a = 2)
      (hU : select U d.toList w = p) (hD : select D d.toList w = p)
      (hp : p.Nodup)
      (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
      (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p)
      (hgood : ∀ u v z : List DyckStep, d.toList = u ++ [D] ++ v ++ [D] ++ z → v.count D = 0 →
        (ht : u.count D + 1 < p.length) → p[u.count D] < p[u.count D + 1] →
        v = [] ∨ (v = [U] ∧ u.count U = u.count D + 1)) : ∀ i j k (hij : i < j) (_hjk : j < k)
        (hjlen : j < p.length) (hk : k < p.length), p[i] < p[j] →
        ¬ (secondPos p[i] w < w.idxOf p[k] ∧ w.idxOf p[k] < secondPos p[j] w) := by
    have crossing_consecutive_gap (s : ℕ → ℕ) (f i j : ℕ)
        (hij : i < j) (hleft : s i < f) (hright : f < s j)
        (hneq : ∀ t, i < t → t < j → f ≠ s t) :
        ∃ t, i ≤ t ∧ t + 1 ≤ j ∧ s t < f ∧ f < s (t + 1) := by
      have step : ∀ b, i < b → f < s b → (∀ t, i < t → t < b → f ≠ s t) →
          ∃ t, i ≤ t ∧ t + 1 ≤ b ∧ s t < f ∧ f < s (t + 1) := by
        intro b
        induction b with
        | zero =>
          intro hib; omega
        | succ b ih =>
          intro hib hfb hne
          by_cases heq : i = b
          · refine ⟨i, le_refl _, by omega, hleft, ?_⟩
            simpa [heq] using hfb
          · have hib' : i < b := by omega
            by_cases hbefore : s b < f
            · exact ⟨b, by omega, by omega, hbefore, hfb⟩
            · have hdistinct : f ≠ s b := hne b hib' (by omega)
              have hfb' : f < s b := (by omega)
              obtain ⟨t, hit, htb, hlt, hgt⟩ := ih hib' hfb'
                (by intro t hit htb; exact hne t hit (by omega))
              exact ⟨t, hit, by omega, hlt, hgt⟩
      exact step j hij hright hneq
    have low_crossing_iff_ascent_gaps (p : List ℕ) (f s : ℕ → ℕ) (hp : p.Nodup)
        (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
        (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p)
        (hdisjoint : ∀ k t, f k ≠ s t) :
        (∀ i j k (hij : i < j) (_hjk : j < k) (hjlen : j < p.length),
          p[i] < p[j] → ¬ (s i < f k ∧ f k < s j)) ↔
        (∀ t k (ht : t + 1 < p.length) (_htk : t + 1 < k),
          p[t] < p[t + 1] → ¬ (s t < f k ∧ f k < s (t + 1))) := by
      constructor
      · intro hglobal t k ht htk hasc hcross
        exact hglobal t (t + 1) k (by omega) htk ht hasc hcross
      · intro hlocal i j k hij hjk hjlen hinc hcross
        obtain ⟨t, hit, htj, hst, hfs⟩ := crossing_consecutive_gap s (f k) i j hij hcross.1 hcross.2
            (by intro t _ _; exact hdisjoint k t)
        have htlen : t + 1 < p.length := (by omega)
        have hne : p[t] ≠ p[t + 1] := by
          intro heq
          have hidx := (hp.getElem_inj_iff (hi := (by omega : t < p.length)) (hj := htlen)).mp heq
          omega
        have hasc : p[t] < p[t + 1] := by
          by_contra hnot
          have hdesc : p[t + 1] < p[t] := (by omega)
          have hsep := descent_separates p hp h132 h213 t i j htlen hdesc
            hit (by omega) hjlen
          omega
        exact hlocal t k htlen (by omega) hasc ⟨hst, hfs⟩
    have select_sublist (t : DyckStep) (d : List DyckStep) (w : List ℕ) :
        List.Sublist (select t d w) w := by
      induction d generalizing w with
      | nil => simp [select]
      | cons x d ih =>
        cases w with
        | nil => simp [select]
        | cons a w =>
          by_cases hx : x = t
          · simpa [select, hx] using (ih w).cons_cons a
          · simpa [select, hx] using (ih w).cons a
    have toggle_eq (active : Finset ℕ) (letter : ℕ) : toggle active letter =
          if letter ∈ active then active.erase letter else insert letter active := by
      ext value
      by_cases present : letter ∈ active <;>
        by_cases same : value = letter <;>
        simp [Finset.mem_symmDiff, present, same]
    have mem_toggle_iff (s : Finset ℕ) (a b : ℕ) :
        a ∈ toggle s b ↔ if a = b then a ∉ s else a ∈ s := by
      by_cases hab : a = b
      · subst b
        by_cases ha : a ∈ s <;> simp [toggle_eq, ha]
      · by_cases hb : b ∈ s <;> simp [toggle_eq, hab, hb]
    have scan_first_second (a : ℕ) (w : List ℕ) (hw : w.count a = 2) :
        (scan ∅ w)[w.idxOf a]? = some U ∧
          (scan ∅ w)[NonnestingBasicOrders.secondPos a w]? = some D := by
      obtain ⟨u, v, z, hu, hv, _, rfl⟩ := NonnestingBasicOrders.count_two_decomposition a w hw
      have hf : (u ++ [a] ++ v ++ [a] ++ z).idxOf a = u.length := by
        simp [List.idxOf_append, hu]
      have hs : NonnestingBasicOrders.secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
          u.length + 1 + v.length := by
        have hdrop : u.drop (u.length + 1) = [] := by
          apply List.drop_eq_nil_iff.mpr; omega
        simp [NonnestingBasicOrders.secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
      constructor
      · rw [hf, scan_getElem?]
        simp [List.count_eq_zero.mpr hu, foldl_toggle_parity]
      · rw [hs, scan_getElem?]
        have hlen : (u ++ [a] ++ v).length = u.length + 1 + v.length := by
          simp; omega
        have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) := by
          simp [List.append_assoc]
        have ht : (u ++ [a] ++ v ++ [a] ++ z).take (u.length + 1 + v.length) = u ++ [a] ++ v := by
          rw [hword, ← hlen]; exact List.take_left
        have hget : (u ++ [a] ++ v ++ [a] ++ z)[u.length + 1 + v.length]? = some a := by
          rw [hword, ← hlen]; simp
        have hu0 : u.count a = 0 := List.count_eq_zero.mpr hu
        have hv0 : v.count a = 0 := List.count_eq_zero.mpr hv
        have hbefore : a ∉ u.foldl toggle ∅ := by
          have hpar := foldl_toggle_parity ∅ u a; simpa [hu0] using hpar
        have hafter : a ∈ toggle (u.foldl toggle ∅) a := by
          simp [mem_toggle_iff, hbefore]
        rw [hget, Option.map_some, ht]; simp [foldl_toggle_parity, hv0, hafter]
    let f : ℕ → ℕ := fun k =>
      if hk : k < p.length then w.idxOf p[k] else w.length + 1
    let s : ℕ → ℕ := fun t =>
      if ht : t < p.length then secondPos p[t] w else w.length + 2
    have hmem (r : ℕ) (hr : r < p.length) : p[r] ∈ w := (select_sublist U d.toList w).subset
        (by rw [hU]; exact List.getElem_mem hr)
    have hfirstlen (r : ℕ) (hr : r < p.length) : w.idxOf p[r] < w.length :=
      List.idxOf_lt_length_of_mem (hmem r hr)
    have hsecondlen (r : ℕ) (hr : r < p.length) : secondPos p[r] w < w.length := by
      have hd := (scan_first_second p[r] w (hcount p[r] (hmem r hr))).2
      have hl : secondPos p[r] w < (scan ∅ w).length := (List.getElem?_eq_some_iff.mp hd).1
      simpa [scan_length] using hl
    have hdisjoint : ∀ k t, f k ≠ s t := by
      intro k t heq
      by_cases hk : k < p.length
      · by_cases ht : t < p.length
        · have heq' : w.idxOf p[k] = secondPos p[t] w := by
            simpa [f, s, hk, ht] using heq
          have hu := (scan_first_second p[k] w (hcount p[k] (hmem k hk))).1
          have hd := (scan_first_second p[t] w (hcount p[t] (hmem t ht))).2
          rw [heq', hd] at hu; cases hu
        · have heq' : w.idxOf p[k] = w.length + 2 := by
            simpa [f, s, hk, ht] using heq
          have hl := hfirstlen k hk; omega
      · by_cases ht : t < p.length
        · have heq' : w.length + 1 = secondPos p[t] w := by
            simpa [f, s, hk, ht] using heq
          have hl := hsecondlen t ht; omega
        · have heq' : w.length + 1 = w.length + 2 := by
            simp [f, s, hk, ht] at heq
          omega
    have hglobal := (low_crossing_iff_ascent_gaps p f s hp h132 h213 hdisjoint).mpr
    have hlocal : ∀ t k (ht : t + 1 < p.length) (_htk : t + 1 < k),
        p[t] < p[t + 1] → ¬ (s t < f k ∧ f k < s (t + 1)) := by
      intro t k ht htk hasc hcross
      by_cases hk : k < p.length
      swap
      · have hslen : s (t + 1) < w.length := by
          simpa [s, ht] using hsecondlen (t + 1) ht
        have hfout : f k = w.length + 1 := (by simp [f, hk]); omega
      have hlength : d.toList.length = w.length := by
        rw [← hscan, scan_length]
      have hdown : d.toList.count D = p.length := by
        rw [← select_length D d.toList w hlength, hD]
      obtain ⟨u, v, z, hsplit, hnoD, hrank⟩ := indexed_downstep_gap d.toList t (by omega)
      have htrank : u.count D + 1 < p.length := (by omega)
      have hasc' : p[u.count D] < p[u.count D + 1] := by
        simpa only [hrank] using hasc
      have hgood' := hgood u v z hsplit hnoD htrank hasc'
      have hnone : ∀ q, q < v.length → u.count U + q ≤ u.count D + 1 := by
        intro q hq
        rcases hgood' with hnil | ⟨hsingle, hground⟩
        · simp [hnil] at hq
        · rw [hsingle] at hq
          have hq0 : q = 0 := (by simp at hq; omega); subst q; omega
      have hcross' : secondPos (p[u.count D]'(by omega)) w < w.idxOf (p[k]'(by omega)) ∧
          w.idxOf (p[k]'(by omega)) <
          secondPos (p[u.count D + 1]'htrank) w := by
        simpa [f, s, hk, show t < p.length by omega, ht, hrank] using hcross
      obtain ⟨q, hq, _, hlater⟩ := crossing_has_later_upstep d.toList w p hscan hcount hU hD hp
          u v z hsplit hnoD htrank k (by omega) (by omega) hcross'
      have hcountle : (v.take q).count U ≤ q :=
        (List.count_le_length).trans (List.length_take_le q v)
      have hbound := hnone q hq; omega
    intro i j k hij hjk hj hk hinc hcross
    have hcross' : s i < f k ∧ f k < s j := by
      simpa [f, s, hk, hj, show i < p.length by omega] using hcross
    exact hglobal hlocal i j k hij hjk hj hinc hcross'
  have select_sublist (t : DyckStep) (d : List DyckStep) (w : List ℕ) :
      List.Sublist (select t d w) w := by
    induction d generalizing w with
    | nil => simp [select]
    | cons x d ih =>
      cases w with
      | nil => simp [select]
      | cons a w =>
        by_cases hx : x = t
        · simpa [select, hx] using (ih w).cons_cons a
        · simpa [select, hx] using (ih w).cons a
  have toggle_eq (active : Finset ℕ) (letter : ℕ) : toggle active letter =
        if letter ∈ active then active.erase letter else insert letter active := by
    ext value
    by_cases present : letter ∈ active <;>
      by_cases same : value = letter <;>
      simp [Finset.mem_symmDiff, present, same]
  have tagged_pair_positions (t : DyckStep) (d : List DyckStep) (w : List ℕ) (a b : ℕ)
      (hab : List.Sublist [(t, a), (t, b)] (d.zip w)) :
      ∃ i j : ℕ, i < j ∧ d[i]? = some t ∧ w[i]? = some a ∧ d[j]? = some t ∧ w[j]? = some b := by
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hab
    let i := (f 0).val; let j := (f 1).val
    have hij : i < j := f.strictMono (show (0 : Fin 2) < 1 by decide)
    have hi : (d.zip w)[i]? = some (t, a) := by
      rw [List.getElem?_eq_getElem (f 0).isLt]; simpa using congrArg some (hf (0 : Fin 2)).symm
    have hj : (d.zip w)[j]? = some (t, b) := by
      rw [List.getElem?_eq_getElem (f 1).isLt]; simpa using congrArg some (hf (1 : Fin 2)).symm
    obtain ⟨hdi, hwi⟩ := List.getElem?_zip_eq_some.mp hi
    obtain ⟨hdj, hwj⟩ := List.getElem?_zip_eq_some.mp hj
    exact ⟨i, j, hij, hdi, hwi, hdj, hwj⟩
  have mem_toggle_iff (s : Finset ℕ) (a b : ℕ) :
      a ∈ toggle s b ↔ if a = b then a ∉ s else a ∈ s := by
    by_cases hab : a = b
    · subst b
      by_cases ha : a ∈ s <;> simp [toggle_eq, ha]
    · by_cases hb : b ∈ s <;> simp [toggle_eq, hab, hb]
  have scan_first_second (a : ℕ) (w : List ℕ) (hw : w.count a = 2) :
      (scan ∅ w)[w.idxOf a]? = some U ∧
        (scan ∅ w)[NonnestingBasicOrders.secondPos a w]? = some D := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := NonnestingBasicOrders.count_two_decomposition a w hw
    have hf : (u ++ [a] ++ v ++ [a] ++ z).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hs : NonnestingBasicOrders.secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr; omega
      simp [NonnestingBasicOrders.secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hf, scan_getElem?]
      simp [List.count_eq_zero.mpr hu, foldl_toggle_parity]
    · rw [hs, scan_getElem?]
      have hlen : (u ++ [a] ++ v).length = u.length + 1 + v.length := by
        simp; omega
      have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) := by
        simp [List.append_assoc]
      have ht : (u ++ [a] ++ v ++ [a] ++ z).take (u.length + 1 + v.length) = u ++ [a] ++ v := by
        rw [hword, ← hlen]; exact List.take_left
      have hget : (u ++ [a] ++ v ++ [a] ++ z)[u.length + 1 + v.length]? = some a := by
        rw [hword, ← hlen]; simp
      have hu0 : u.count a = 0 := List.count_eq_zero.mpr hu
      have hv0 : v.count a = 0 := List.count_eq_zero.mpr hv
      have hbefore : a ∉ u.foldl toggle ∅ := by
        have hpar := foldl_toggle_parity ∅ u a; simpa [hu0] using hpar
      have hafter : a ∈ toggle (u.foldl toggle ∅) a := by
        simp [mem_toggle_iff, hbefore]
      rw [hget, Option.map_some, ht]; simp [foldl_toggle_parity, hv0, hafter]
  have scan_tag_position (t : DyckStep) (w : List ℕ) (a i : ℕ)
      (hc : w.count a = 2) (hwi : w[i]? = some a)
      (hti : (scan ∅ w)[i]? = some t) : i = if t = U then w.idxOf a
          else NonnestingBasicOrders.secondPos a w := by
    have hposition := occurrencePositions w a i hc hwi
    obtain ⟨hfirst, hsecond⟩ := scan_first_second a w hc
    rcases hposition with hi | hi
    · cases t with
      | U => simpa using hi
      | D => rw [hi, hfirst] at hti; cases hti
    · cases t with
      | U => rw [hi, hsecond] at hti; cases hti
      | D => simpa using hi
  have queue_pairwise_position (t : DyckStep) (w : List ℕ) (hw : ∀ a ∈ w, w.count a = 2) :
      (select t (scan ∅ w) w).Pairwise
        (fun a b => (if t = U then w.idxOf a else NonnestingBasicOrders.secondPos a w) <
           (if t = U then w.idxOf b else NonnestingBasicOrders.secondPos b w)) := by
    apply List.pairwise_iff_forall_sublist.mpr; intro a b hab
    have hpair : List.Sublist [(t, a), (t, b)] ((select t (scan ∅ w) w).map (t, ·)) := by
      simpa using hab.map (t, ·)
    have htag : List.Sublist [(t, a), (t, b)] ((scan ∅ w).zip w) :=
      hpair.trans (tagged_select_sublist t (scan ∅ w) w)
    obtain ⟨i, j, hij, hti, hwi, htj, hwj⟩ := tagged_pair_positions t (scan ∅ w) w a b htag
    have hca : w.count a = 2 := hw a (List.mem_of_getElem? hwi)
    have hcb : w.count b = 2 := hw b (List.mem_of_getElem? hwj)
    have hia := scan_tag_position t w a i hca hwi hti
    have hjb := scan_tag_position t w b j hcb hwj htj; simpa [← hia, ← hjb] using hij
  have count_select_of_not_mem (t : DyckStep) (d : List DyckStep)
      (w : List ℕ) (a : ℕ) (ha : a ∉ w) : (select t d w).count a = 0 := by
    apply List.count_eq_zero.mpr; exact fun hm => ha ((select_sublist t d w).subset hm)
  have doubled_queue_count (w : List ℕ) (a : ℕ) (hw : w.count a = 2) :
      (select U (scan ∅ w) w).count a = 1 ∧ (select D (scan ∅ w) w).count a = 1 := by
    obtain ⟨u, v, z, hu, hv, hz, rfl⟩ := NonnestingBasicOrders.count_two_decomposition a w hw
    have hfold_u : a ∉ u.foldl toggle ∅ := by
      have h := foldl_toggle_parity ∅ u a; simpa [List.count_eq_zero.mpr hu] using h
    have hfold_v : a ∈ v.foldl toggle (toggle (u.foldl toggle ∅) a) := by
      have h := foldl_toggle_parity (toggle (u.foldl toggle ∅) a) v a
      have ht : a ∈ toggle (u.foldl toggle ∅) a := by
        simp [mem_toggle_iff, hfold_u]
      simpa [List.count_eq_zero.mpr hv, ht] using h
    have hlen_u : (scan ∅ u).length = u.length := scan_length ∅ u
    have hlen_uav : (scan ∅ (u ++ [a] ++ v)).length =
        (u ++ [a] ++ v).length := scan_length ∅ (u ++ [a] ++ v)
    have hscan_first : scan (u.foldl toggle ∅) (a :: v) =
        U :: scan (toggle (u.foldl toggle ∅) a) v := by
      simp [scan, hfold_u]
    have hscan_second : scan (v.foldl toggle (toggle (u.foldl toggle ∅) a)) (a :: z) = D :: scan
          (toggle (v.foldl toggle (toggle (u.foldl toggle ∅) a)) a) z := by
      simp [scan, hfold_v]
    have hfold_uav : (u ++ [a] ++ v).foldl toggle ∅ =
        v.foldl toggle (toggle (u.foldl toggle ∅) a) := by
      simp [List.foldl_append]
    have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) := by
      simp [List.append_assoc]
    have hscan_uav : scan ∅ (u ++ [a] ++ v) =
        scan ∅ u ++ U :: scan (toggle (u.foldl toggle ∅) a) v := by
      rw [show u ++ [a] ++ v = u ++ (a :: v) by simp [List.append_assoc], scan_append, hscan_first]
    rw [hword, scan_append, select_append U _ _ _ _ hlen_uav, select_append D _ _ _ _ hlen_uav]
    rw [hfold_uav, hscan_second]
    simp only [select, reduceCtorEq, ite_false, ite_true,
      List.count_append, List.count_cons, beq_self_eq_true]
    rw [hscan_uav, show u ++ [a] ++ v = u ++ (a :: v) by simp [List.append_assoc],
        select_append U _ _ _ _ hlen_u, select_append D _ _ _ _ hlen_u]
    simp [select, count_select_of_not_mem, hu, hv, hz]
  have first_order_restrictions (w p : List ℕ) (hcount : ∀ a ∈ w, w.count a = 2)
      (hU : select U (scan ∅ w) w = p)
      (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
      (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p) : ∀ a b c : ℕ,
        a ∈ w → b ∈ w → c ∈ w → a < b → b < c → ¬ (w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b) ∧
        ¬ (w.idxOf b < w.idxOf a ∧ w.idxOf a < w.idxOf c) := by
    have hmemP (a : ℕ) (ha : a ∈ w) : a ∈ p := by
      have hc := (doubled_queue_count w a (hcount a ha)).1
      rw [hU] at hc; exact List.count_pos_iff.mp (by omega : 0 < p.count a)
    have hpair := queue_pairwise_position U w hcount; rw [hU] at hpair
    have hindex (a b : ℕ) (ha : a ∈ p) (hb : b ∈ p)
        (hab : w.idxOf a < w.idxOf b) : p.idxOf a < p.idxOf b := by
      have hia : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
      have hib : p.idxOf b < p.length := List.idxOf_lt_length_of_mem hb
      by_contra hnot
      by_cases heq : p.idxOf a = p.idxOf b
      · have hopt := congrArg (fun r => p[r]?) heq
        rw [List.getElem?_idxOf ha, List.getElem?_idxOf hb] at hopt
        have hab' := Option.some.inj hopt; subst b; omega
      · have hrev := (List.pairwise_iff_getElem.mp hpair)
          (p.idxOf b) (p.idxOf a) hib hia (by omega)
        have hva : p[p.idxOf a] = a := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf ha)).2
        have hvb : p[p.idxOf b] = b := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hb)).2
        simp only [ite_true, hvb, hva] at hrev; omega
    have triple_sublist (a b c : ℕ) (i j k : ℕ)
        (hi : i < p.length) (hj : j < p.length) (hk : k < p.length)
        (hij : i < j) (hjk : j < k)
        (hpi : p[i] = a) (hpj : p[j] = b) (hpk : p[k] = c) : List.Sublist [a, b, c] p := by
      let f : Fin 3 ↪o Fin p.length := OrderEmbedding.ofMapLEIff
          (fun q => if hq : q.val = 0 then ⟨i, hi⟩ else if hq : q.val = 1 then ⟨j, hj⟩ else ⟨k, hk⟩)
          (by intro q r; fin_cases q <;> fin_cases r <;> simp <;> omega)
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨f, ?_⟩
      intro q
      fin_cases q <;> simp [f, hpi, hpj, hpk]
    intro a b c ha hb hc hab hbc; have hpA := hmemP a ha; have hpB := hmemP b hb
    have hpC := hmemP c hc; have hiA := List.idxOf_lt_length_of_mem hpA
    have hiB := List.idxOf_lt_length_of_mem hpB; have hiC := List.idxOf_lt_length_of_mem hpC
    have hvA : p[p.idxOf a] = a := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hpA)).2
    have hvB : p[p.idxOf b] = b := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hpB)).2
    have hvC : p[p.idxOf c] = c := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hpC)).2
    constructor
    · rintro ⟨hac, hcb⟩
      have hia := hindex a c hpA hpC hac; have hib := hindex c b hpC hpB hcb; apply h132
      let x : ℕ → ℕ := fun q => if q = 1 then a else if q = 2 then b else c
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro q hq hq'
        have : q = 1 ∨ q = 2 := (by simp [NonnestingDefs.letters] at hq'; omega)
        rcases this with rfl | rfl
        · simpa [x] using hab
        · simpa [x] using hbc
      · intro q hq hq'
        have : q = 1 ∨ q = 2 ∨ q = 3 := by
          simp [NonnestingDefs.letters] at hq'; omega
        rcases this with rfl | rfl | rfl <;> simp [x, hpA, hpB, hpC]
      · simpa [x] using
          triple_sublist a c b (p.idxOf a) (p.idxOf c) (p.idxOf b)
            hiA hiC hiB hia hib hvA hvC hvB
    · rintro ⟨hba, hac⟩
      have hia := hindex b a hpB hpA hba; have hib := hindex a c hpA hpC hac; apply h213
      let x : ℕ → ℕ := fun q => if q = 1 then a else if q = 2 then b else c
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro q hq hq'
        have : q = 1 ∨ q = 2 := (by simp [NonnestingDefs.letters] at hq'; omega)
        rcases this with rfl | rfl
        · simpa [x] using hab
        · simpa [x] using hbc
      · intro q hq hq'
        have : q = 1 ∨ q = 2 ∨ q = 3 := by
          simp [NonnestingDefs.letters] at hq'; omega
        rcases this with rfl | rfl | rfl <;> simp [x, hpA, hpB, hpC]
      · simpa [x] using
          triple_sublist b a c (p.idxOf b) (p.idxOf a) (p.idxOf c)
            hiB hiA hiC hia hib hvB hvA hvC
  have hfirst := first_order_restrictions w p hcount
    (by simpa [hscan] using hU) h132 h213
  have hglobal := good_gaps_exclude_crossings d w p hscan hcount
    hU hD hp h132 h213 hgood
  have hmemP (a : ℕ) (ha : a ∈ w) : a ∈ p := by
    have hc := (doubled_queue_count w a (hcount a ha)).1
    rw [hscan, hU] at hc; exact List.count_pos_iff.mp (by omega : 0 < p.count a)
  have hpair := queue_pairwise_position U w hcount; rw [hscan, hU] at hpair
  have hindex (a b : ℕ) (ha : a ∈ p) (hb : b ∈ p)
      (hab : w.idxOf a < w.idxOf b) : p.idxOf a < p.idxOf b := by
    have hia : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
    have hib : p.idxOf b < p.length := List.idxOf_lt_length_of_mem hb
    have hva : p[p.idxOf a] = a := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf ha)).2
    have hvb : p[p.idxOf b] = b := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hb)).2
    by_contra hnot
    by_cases heq : p.idxOf a = p.idxOf b
    · have hab' : a = b := by
        have hopt := congrArg (fun r => p[r]?) heq
        rw [List.getElem?_idxOf ha, List.getElem?_idxOf hb] at hopt; exact Option.some.inj hopt
      subst b; omega
    · have hrev := (List.pairwise_iff_getElem.mp hpair)
        (p.idxOf b) (p.idxOf a) hib hia (by omega)
      simp only [ite_true, hvb, hva] at hrev; omega
  apply low_local_test w hcount hnn; intro a b c ha hb hc hab hbc; have hpA := hmemP a ha
  have hpB := hmemP b hb; have hpC := hmemP c hc; have hlenA := List.idxOf_lt_length_of_mem hpA
  have hlenB := List.idxOf_lt_length_of_mem hpB; have hlenC := List.idxOf_lt_length_of_mem hpC
  have hia : p[p.idxOf a] = a := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hpA)).2
  have hib : p[p.idxOf b] = b := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hpB)).2
  have hic : p[p.idxOf c] = c := (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hpC)).2
  refine ⟨(hfirst a b c ha hb hc hab hbc).1, (hfirst a b c ha hb hc hab hbc).2, ?_, ?_⟩
  · rintro ⟨hfab, hfbc, hsa, hcsb⟩
    have hij : p.idxOf a < p.idxOf b := hindex a b hpA hpB hfab
    have hjk : p.idxOf b < p.idxOf c := hindex b c hpB hpC hfbc
    have hcross := hglobal (p.idxOf a) (p.idxOf b) (p.idxOf c)
      hij hjk hlenB hlenC
      (by rw [hia, hib]; exact hab)
      (by simpa only [hia, hib, hic] using And.intro hsa hcsb)
    exact hcross
  · rintro ⟨hfbc, hfca, hsb, hac⟩
    have hij : p.idxOf b < p.idxOf c := hindex b c hpB hpC hfbc
    have hjk : p.idxOf c < p.idxOf a := hindex c a hpC hpA hfca
    have hcross := hglobal (p.idxOf b) (p.idxOf c) (p.idxOf a)
      hij hjk hlenC hlenA
      (by rw [hib, hic]; exact hbc)
      (by simpa only [hia, hib, hic] using And.intro hsb hac)
    exact hcross
#print axioms good_gaps_avoid_low
end D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowConverse
