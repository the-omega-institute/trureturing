/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber
   mirror-E: none(waiver:royal-low-dyck-fiber)
   anchors: [mathlib/module/Mathlib.Data.Finset.Interval]
   utility: none
   digest: Counts low Royal avoiders over one Dyck shape by its good gaps. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncConverse
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBijection
import D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowConverse
import Mathlib.Data.Finset.Interval
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalShape
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowFiber

open scoped symmDiff
open DyckStep NonnestingDefs NonnestingBasicOrders NonnestingBasicRoyalEncoding
  NonnestingBasicRoyalShape NonnestingBasicRoyalBijection NonnestingBasicRoyalIncBlocks
  NonnestingBasicRoyalIncConverse NonnestingRoyalLowGap
  NonnestingRoyalLowConverse

noncomputable def goodPositions (n : ℕ) (d : DyckWord) : Finset (Fin (n - 1)) := by
  classical
  exact Finset.univ.filter fun i =>
    ∀ u v z : List DyckStep,
      d.toList = u ++ [D] ++ v ++ [D] ++ z →
      v.count D = 0 → u.count D = i.val →
      v = [] ∨ (v = [U] ∧ u.count U = u.count D + 1)
local notation "toggle" =>
  (fun (active : Finset ℕ) (letter : ℕ) => active ∆ Singleton.singleton letter)
set_option maxHeartbeats 2000000 in
noncomputable def lowFiberEncoding (n : ℕ) (d : DyckWord) (hd : d.semilength = n) :
    {c : Composition n //
      ∀ t (ht : t + 1 < n),
        (incBlocks n c.blocks)[t]'(by
          have length_eq (size : ℕ) (blocks : List ℕ) :
              (incBlocks size blocks).length = blocks.sum := by
            induction blocks generalizing size <;> simp [incBlocks, *]
          rw [length_eq, c.blocks_sum]; omega) <
        (incBlocks n c.blocks)[t + 1]'(by
          have length_eq (size : ℕ) (blocks : List ℕ) :
              (incBlocks size blocks).length = blocks.sum := by
            induction blocks generalizing size <;> simp [incBlocks, *]
          rw [length_eq, c.blocks_sum]; omega) →
        (⟨t, by omega⟩ : Fin (n - 1)) ∈ goodPositions n d} ≃
    {x : {w : List ℕ // w ∈ avoiders n []} //
      ((royalEncoding n).symm x).1.2 = d ∧
      x.1 ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]} := by
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
  have occursTriple (word pattern : List ℕ) (size : NonnestingDefs.letters pattern = 3) :
      (∃ lower middle upper : ℕ, lower < middle ∧ middle < upper ∧
        lower ∈ word ∧ middle ∈ word ∧ upper ∈ word ∧
        (pattern.map fun label => if label = 1 then lower
          else if label = 2 then middle else upper).Sublist word) →
      NonnestingDefs.Occurs pattern word := by
    rintro ⟨lower, middle, upper, orderedLM, orderedMU, memberL, memberM, memberU, sublist⟩
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    rw [size]
    let values : ℕ → ℕ := fun label => if label = 1 then lower
      else if label = 2 then middle else upper
    refine ⟨values, ?_, ?_, sublist, by simp⟩
    · intro label positive bounded
      have alternatives : label = 1 ∨ label = 2 := by omega
      rcases alternatives with rfl | rfl <;> simp [values, orderedLM, orderedMU]
    · intro label positive bounded
      have alternatives : label = 1 ∨ label = 2 ∨ label = 3 := by omega
      rcases alternatives with rfl | rfl | rfl <;> simp [values, memberL, memberM, memberU]
  have quadruplePositions (word : List ℕ) (one two three four : ℕ) :
      (∃ first second third fourth : ℕ, first < second ∧ second < third ∧ third < fourth ∧
          word[first]? = some one ∧ word[second]? = some two ∧
          word[third]? = some three ∧ word[fourth]? = some four) →
      [one, two, three, four].Sublist word := by
    rintro ⟨first, second, third, fourth, orderFS, orderST, orderTF,
      valueF, valueS, valueT, valueL⟩
    let positions : Fin 4 → ℕ := ![first, second, third, fourth]
    have bounds (slot : Fin 4) : positions slot < word.length := by
      fin_cases slot <;> simp [positions] <;>
        exact (List.getElem?_eq_some_iff.mp (by assumption)).1
    let embedding : Fin 4 ↪o Fin word.length :=
      OrderEmbedding.ofMapLEIff (fun slot => ⟨positions slot, bounds slot⟩)
        (by intro left right; fin_cases left <;> fin_cases right <;> simp [positions] <;> omega)
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨embedding, ?_⟩
    intro slot
    fin_cases slot <;> simp [embedding, positions] <;>
      exact (List.getElem?_eq_some_iff.mp (by assumption)).2.symm
  have low_local_test (w : List ℕ) (hcount : ∀ x ∈ w, w.count x = 2)
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
      (havoid : ¬ NonnestingDefs.Occurs [1, 1, 3, 2] w ∧
        ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w) :
      ∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
        ¬ (w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b) ∧
        ¬ (w.idxOf b < w.idxOf a ∧ w.idxOf a < w.idxOf c) := by
    intro a b c ha hb hc hab hbc
    have horders := (nonnesting_iff_equal_orders w hcount).mp hnn
    constructor
    · intro order
      apply havoid.1
      apply (occursTriple w [1, 1, 3, 2] (by decide))
      refine ⟨a, b, c, hab, hbc, ha, hb, hc, ?_⟩
      have sublist := (quadruplePositions w a a c b)
        ⟨w.idxOf a, secondPos a w, secondPos c w, secondPos b w,
          by unfold secondPos; omega, horders a ha c hc order.1, horders c hc b hb order.2,
          List.getElem?_idxOf ha,
          secondOccurrence w a (hcount a ha),
          secondOccurrence w c (hcount c hc),
          secondOccurrence w b (hcount b hb)⟩
      simpa using sublist
    · intro order
      apply havoid.2
      apply (occursTriple w [2, 2, 1, 3] (by decide))
      refine ⟨a, b, c, hab, hbc, ha, hb, hc, ?_⟩
      have sublist := (quadruplePositions w b b a c)
        ⟨w.idxOf b, secondPos b w, secondPos a w, secondPos c w,
          by unfold secondPos; omega, horders b hb a ha order.1, horders a ha c hc order.2,
          List.getElem?_idxOf hb,
          secondOccurrence w b (hcount b hb),
          secondOccurrence w a (hcount a ha),
          secondOccurrence w c (hcount c hc)⟩
      simpa using sublist
  have foldl_toggle_parity (s : Finset ℕ) (w : List ℕ) (a : ℕ) :
      a ∈ w.foldl toggle s ↔
        if w.count a % 2 = 0 then a ∈ s else a ∉ s := by
    have toggle_eq (active : Finset ℕ) (letter : ℕ) :
        toggle active letter =
          if letter ∈ active then active.erase letter else insert letter active := by
      ext value
      by_cases present : letter ∈ active <;>
        simp [Finset.mem_symmDiff, present] <;> grind
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
  have scan_getElem? (s : Finset ℕ) (w : List ℕ) (i : ℕ) :
      (scan s w)[i]? =
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
  have incBlocks_unique (n : ℕ) (ks ls : List ℕ)
      (hkpos : ∀ k ∈ ks, 0 < k) (hlpos : ∀ l ∈ ls, 0 < l)
      (hksum : ks.sum = n) (hlsum : ls.sum = n)
      (heq : incBlocks n ks = incBlocks n ls) : ks = ls := by
    induction ks generalizing n ls with
    | nil =>
      cases ls with
      | nil => rfl
      | cons l ls =>
        have hl : 0 < l := hlpos l (by simp)
        simp only [List.sum_nil] at hksum; simp only [List.sum_cons] at hlsum; omega
    | cons k ks ih =>
      cases ls with
      | nil =>
        have hk : 0 < k := hkpos k (by simp)
        simp only [List.sum_cons] at hksum; simp only [List.sum_nil] at hlsum; omega
      | cons l ls =>
        have hk : 0 < k := hkpos k (by simp); have hl : 0 < l := hlpos l (by simp)
        have hkn : k ≤ n := by
          simp only [List.sum_cons] at hksum; omega
        have hln : l ≤ n := by
          simp only [List.sum_cons] at hlsum; omega
        have hheadk : (incBlocks n (k :: ks)).head? = some (n - k + 1) := by
          simp [incBlocks, List.head?_append, List.head?_range', Nat.ne_of_gt hk]
        have hheadl : (incBlocks n (l :: ls)).head? = some (n - l + 1) := by
          simp [incBlocks, List.head?_append, List.head?_range', Nat.ne_of_gt hl]
        have hkl : k = l := by
          have hv := congrArg List.head? heq; rw [hheadk, hheadl] at hv
          have hval := Option.some.inj hv; omega
        subst l
        have htail : incBlocks (n - k) ks = incBlocks (n - k) ls := by
          have h := heq; simp only [incBlocks] at h; exact List.append_cancel_left h
        have hksum' : ks.sum = n - k := by
          simp only [List.sum_cons] at hksum; omega
        have hlsum' : ls.sum = n - k := by
          simp only [List.sum_cons] at hlsum; omega
        have hkpos' : ∀ j ∈ ks, 0 < j := by
          intro j hj; exact hkpos j (by simp [hj])
        have hlpos' : ∀ j ∈ ls, 0 < j := by
          intro j hj; exact hlpos j (by simp [hj])
        exact congrArg (k :: ·) (ih (n - k) ls hkpos' hlpos' hksum' hlsum' htail)
  have scan_append (s : Finset ℕ) (u v : List ℕ) :
      scan s (u ++ v) = scan s u ++ scan (u.foldl toggle s) v := by
    induction u generalizing s with
    | nil => simp [scan]
    | cons a u ih =>
      by_cases h : a ∈ s <;> simp [scan, h, ih, List.foldl_cons]
  have select_append (t : DyckStep) (d e : List DyckStep) (u v : List ℕ)
      (h : d.length = u.length) :
      select t (d ++ e) (u ++ v) = select t d u ++ select t e v := by
    induction d generalizing u with
    | nil =>
      have : u = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm); subst u; simp [select]
    | cons x d ih =>
      cases u with
      | nil => simp at h
      | cons a u =>
        have ht : d.length = u.length := by simpa using h
        by_cases hx : x = t <;> simp [select, hx, ih u ht]
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
  have incBlocks_perm (n : ℕ) (ks : List ℕ)
      (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n) :
      (incBlocks n ks).Perm (List.range' 1 n) := by
    induction ks generalizing n with
    | nil =>
      have hn : n = 0 := by simpa using hsum.symm
      simp [incBlocks, hn]
    | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have hpos' : ∀ x ∈ ks, 0 < x := by
        intro x hx; exact hpos x (by simp [hx])
      have hsum' : ks.sum = n - k := by
        simp only [List.sum_cons] at hsum; omega
      have hkn : k ≤ n := by
        simp only [List.sum_cons] at hsum; omega
      have htail := ih (n - k) hpos' hsum'; have hrange : List.range' 1 n =
          List.range' 1 (n - k) ++ List.range' (n - k + 1) k := by
        have hn : n - k + k = n := by omega
        simpa [hn, Nat.add_comm] using
          (List.range'_append (s := 1) (m := n - k) (n := k) (step := 1)).symm
      change (List.range' (n - k + 1) k ++ incBlocks (n - k) ks).Perm
        (List.range' 1 n)
      refine (htail.append_left _).trans ?_
      rw [hrange]; exact List.perm_append_comm
  have toggle_eq (active : Finset ℕ) (letter : ℕ) :
      toggle active letter =
        if letter ∈ active then active.erase letter else insert letter active := by
    ext value
    by_cases present : letter ∈ active <;>
      simp [Finset.mem_symmDiff, present] <;> grind
  have scan_encode (n : ℕ) (p : List ℕ) (d : DyckWord)
      (hp : p.Perm (List.range' 1 n)) (hlen : p.length = d.semilength) :
      scan ∅ ((weave p p d.toList).getD []) = d.toList := by
    let parameter : royalPairs n := ⟨(p, d), hp, hlen⟩
    have inverse := (royalEncoding n).symm_apply_apply parameter
    have path := congrArg (fun pair : royalPairs n => pair.1.2) inverse
    exact congrArg DyckWord.toList path
  have tagged_pair_positions (t : DyckStep) (d : List DyckStep) (w : List ℕ)
      (a b : ℕ)
      (hab : List.Sublist [(t, a), (t, b)] (d.zip w)) :
      ∃ i j : ℕ, i < j ∧ d[i]? = some t ∧ w[i]? = some a ∧
        d[j]? = some t ∧ w[j]? = some b := by
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hab
    let i := (f 0).val; let j := (f 1).val
    have hij : i < j := f.strictMono (show (0 : Fin 2) < 1 by decide)
    have hi : (d.zip w)[i]? = some (t, a) := by
      rw [List.getElem?_eq_getElem (f 0).isLt]
      simpa using congrArg some (hf (0 : Fin 2)).symm
    have hj : (d.zip w)[j]? = some (t, b) := by
      rw [List.getElem?_eq_getElem (f 1).isLt]
      simpa using congrArg some (hf (1 : Fin 2)).symm
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
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ :=
      NonnestingBasicOrders.count_two_decomposition a w hw
    have hf : (u ++ [a] ++ v ++ [a] ++ z).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hs : NonnestingBasicOrders.secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr; omega
      simp [NonnestingBasicOrders.secondPos, List.idxOf_append, hu, hv,
        List.drop_append, hdrop]
    constructor
    · rw [hf, scan_getElem?]
      simp [List.count_eq_zero.mpr hu, foldl_toggle_parity]
    · rw [hs, scan_getElem?]
      have hlen : (u ++ [a] ++ v).length = u.length + 1 + v.length := by
        simp; omega
      have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) := by
        simp [List.append_assoc]
      have ht : (u ++ [a] ++ v ++ [a] ++ z).take (u.length + 1 + v.length) =
          u ++ [a] ++ v := by
        rw [hword, ← hlen]; exact List.take_left
      have hget : (u ++ [a] ++ v ++ [a] ++ z)[u.length + 1 + v.length]? = some a := by
        rw [hword, ← hlen]; simp
      have hu0 : u.count a = 0 := List.count_eq_zero.mpr hu
      have hv0 : v.count a = 0 := List.count_eq_zero.mpr hv
      have hbefore : a ∉ u.foldl toggle ∅ := by
        have hpar := foldl_toggle_parity ∅ u a
        simpa [hu0] using hpar
      have hafter : a ∈ toggle (u.foldl toggle ∅) a := by
        simp [mem_toggle_iff, hbefore]
      rw [hget, Option.map_some, ht]; simp [foldl_toggle_parity, hv0, hafter]
  have scan_tag_position (t : DyckStep) (w : List ℕ) (a i : ℕ)
      (hc : w.count a = 2) (hwi : w[i]? = some a)
      (hti : (scan ∅ w)[i]? = some t) :
      i = if t = U then w.idxOf a
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
  have queue_pairwise_position (t : DyckStep) (w : List ℕ)
      (hw : ∀ a ∈ w, w.count a = 2) :
      (select t (scan ∅ w) w).Pairwise
        (fun a b =>
          (if t = U then w.idxOf a
           else NonnestingBasicOrders.secondPos a w) <
           (if t = U then w.idxOf b
           else NonnestingBasicOrders.secondPos b w)) := by
    apply List.pairwise_iff_forall_sublist.mpr; intro a b hab
    have hpair : List.Sublist [(t, a), (t, b)]
        ((select t (scan ∅ w) w).map (t, ·)) := by
      simpa using hab.map (t, ·)
    have htag : List.Sublist [(t, a), (t, b)] ((scan ∅ w).zip w) :=
      hpair.trans (tagged_select_sublist t (scan ∅ w) w)
    obtain ⟨i, j, hij, hti, hwi, htj, hwj⟩ :=
      tagged_pair_positions t (scan ∅ w) w a b htag
    have hca : w.count a = 2 := hw a (List.mem_of_getElem? hwi)
    have hcb : w.count b = 2 := hw b (List.mem_of_getElem? hwj)
    have hia := scan_tag_position t w a i hca hwi hti
    have hjb := scan_tag_position t w b j hcb hwj htj
    simpa [← hia, ← hjb] using hij
  have count_select_of_not_mem (t : DyckStep) (d : List DyckStep)
      (w : List ℕ) (a : ℕ) (ha : a ∉ w) :
      (select t d w).count a = 0 := by
    apply List.count_eq_zero.mpr; exact fun hm => ha ((select_sublist t d w).subset hm)
  have doubled_queue_count (w : List ℕ) (a : ℕ) (hw : w.count a = 2) :
      (select U (scan ∅ w) w).count a = 1 ∧
        (select D (scan ∅ w) w).count a = 1 := by
    obtain ⟨u, v, z, hu, hv, hz, rfl⟩ :=
      NonnestingBasicOrders.count_two_decomposition a w hw
    have hfold_u : a ∉ u.foldl toggle ∅ := by
      have h := foldl_toggle_parity ∅ u a
      simpa [List.count_eq_zero.mpr hu] using h
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
    have hscan_second : scan (v.foldl toggle (toggle (u.foldl toggle ∅) a))
        (a :: z) = D :: scan
          (toggle (v.foldl toggle (toggle (u.foldl toggle ∅) a)) a) z := by
      simp [scan, hfold_v]
    have hfold_uav : (u ++ [a] ++ v).foldl toggle ∅ =
        v.foldl toggle (toggle (u.foldl toggle ∅) a) := by
      simp [List.foldl_append]
    have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) := by
      simp [List.append_assoc]
    have hscan_uav : scan ∅ (u ++ [a] ++ v) =
        scan ∅ u ++ U :: scan (toggle (u.foldl toggle ∅) a) v := by
      rw [show u ++ [a] ++ v = u ++ (a :: v) by simp [List.append_assoc],
        scan_append, hscan_first]
    rw [hword, scan_append, select_append U _ _ _ _ hlen_uav,
        select_append D _ _ _ _ hlen_uav]
    rw [hfold_uav, hscan_second]
    simp only [select, reduceCtorEq, ite_false, ite_true,
      List.count_append, List.count_cons, beq_self_eq_true]
    rw [hscan_uav,
        show u ++ [a] ++ v = u ++ (a :: v) by simp [List.append_assoc],
        select_append U _ _ _ _ hlen_u,
        select_append D _ _ _ _ hlen_u]
    simp [select, count_select_of_not_mem, hu, hv, hz]
  have encode_data (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n))
      (d : DyckWord) (hlen : p.length = d.semilength) :
      let w := (weave p p d.toList).getD []
      ∃ hw : w.Perm ((List.range' 1 n).flatMap fun a => [a, a]),
        (¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
          ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) ∧
        shape (List.range' 1 n) w hw = d ∧ select U (scan ∅ w) w = p := by
    let parameter : royalPairs n := ⟨(p, d), hp, hlen⟩; let word := royalEncoding n parameter
    have inverse := (royalEncoding n).symm_apply_apply parameter
    have path := congrArg (fun pair : royalPairs n => pair.1.2) inverse
    have queue := congrArg (fun pair : royalPairs n => pair.1.1) inverse
    change shape (List.range' 1 n) ((weave p p d.toList).getD []) word.2.1 = d at path
    change select U (scan ∅ ((weave p p d.toList).getD []))
      ((weave p p d.toList).getD []) = p at queue
    exact ⟨word.2.1, ⟨word.2.2.1, word.2.2.2.1⟩, path, queue⟩
  have doubled_queues_perm (w : List ℕ)
      (hw : ∀ a ∈ w, w.count a = 2) :
      (select U (scan ∅ w) w).Perm (select D (scan ∅ w) w) := by
    apply List.perm_iff_count.mpr; intro a
    by_cases ha : a ∈ w
    · exact (doubled_queue_count w a (hw a ha)).1.trans
        (doubled_queue_count w a (hw a ha)).2.symm
    · rw [count_select_of_not_mem U _ w a ha,
        count_select_of_not_mem D _ w a ha]
  have equal_queues_of_nonnesting (w : List ℕ)
      (hw : ∀ a ∈ w, w.count a = 2)
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) :
      select U (scan ∅ w) w = select D (scan ∅ w) w := by
    let first := fun a (w : List ℕ) => w.idxOf a; let second := NonnestingBasicOrders.secondPos
    have horder := (NonnestingBasicOrders.nonnesting_iff_equal_orders w hw).mp hnn
    have hU : (select U (scan ∅ w) w).Pairwise
        (fun a b => first a w ≤ first b w) := by
      apply (queue_pairwise_position U w hw).imp; intro a b h
      exact Nat.le_of_lt (by simpa [first] using h)
    have hD : (select D (scan ∅ w) w).Pairwise
        (fun a b => first a w ≤ first b w) := by
      apply List.pairwise_iff_forall_sublist.mpr; intro a b hab
      have ha : a ∈ w := (select_sublist D (scan ∅ w) w).subset
        (hab.subset (by simp))
      have hb : b ∈ w := (select_sublist D (scan ∅ w) w).subset
        (hab.subset (by simp))
      have hsa : second a w < second b w := by
        simpa [second] using
          (queue_pairwise_position D w hw).forall_sublist hab
      have hca := hw a ha; have hcb := hw b hb
      have hne : first a w ≠ first b w := by
        intro heq; have hfa : w[first a w]? = some a := List.getElem?_idxOf ha
        have hfb : w[first b w]? = some b := List.getElem?_idxOf hb; rw [heq] at hfa
        have hab' : a = b := Option.some.inj (hfa.symm.trans hfb)
        subst b; exact (Nat.lt_irrefl _ hsa)
      by_contra hnot
      have hba : first b w < first a w := by omega
      have hsba : second b w < second a w := horder b hb a ha hba; exact (Nat.lt_asymm hsa hsba)
    apply (doubled_queues_perm w hw).eq_of_pairwise
      (le := fun a b => first a w ≤ first b w) _ hU hD
    intro a b ha hb hab hba; have ha' : a ∈ w := (select_sublist U (scan ∅ w) w).subset ha
    have hb' : b ∈ w := (select_sublist D (scan ∅ w) w).subset hb
    have hfa : w[first a w]? = some a := List.getElem?_idxOf ha'
    have hfb : w[first b w]? = some b := List.getElem?_idxOf hb'
    rw [Nat.le_antisymm hab hba] at hfa; exact Option.some.inj (hfa.symm.trans hfb)
  have low_first_order_avoids (d : DyckWord) (w p : List ℕ)
      (hscan : scan ∅ w = d.toList)
      (hcount : ∀ a ∈ w, w.count a = 2)
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
      (havoid : ¬ NonnestingDefs.Occurs [1, 1, 3, 2] w ∧
        ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w)
      (hU : select U d.toList w = p) :
      ¬ NonnestingDefs.Occurs [1, 3, 2] p ∧
      ¬ NonnestingDefs.Occurs [2, 1, 3] p := by
    have htest := low_local_test w hcount hnn havoid
    have hpair := queue_pairwise_position U w hcount; rw [hscan, hU] at hpair
    have hfirst_sublist (a b c : ℕ)
        (hsub : List.Sublist [a, b, c] p) :
        w.idxOf a < w.idxOf b ∧ w.idxOf b < w.idxOf c := by
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
      have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
      have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
      have hvi : p[i] = a := by simpa [i] using (hf (0 : Fin 3)).symm
      have hvj : p[j] = b := by simpa [j] using (hf (1 : Fin 3)).symm
      have hvk : p[k] = c := by simpa [k] using (hf (2 : Fin 3)).symm
      have hab := (List.pairwise_iff_getElem.mp hpair) i j
        (f 0).isLt (f 1).isLt hij
      have hbc := (List.pairwise_iff_getElem.mp hpair) j k
        (f 1).isLt (f 2).isLt hjk
      constructor
      · simpa [hvi, hvj] using hab
      · simpa [hvj, hvk] using hbc
    have hmem_sublist (a b c : ℕ)
        (hsub : List.Sublist [a, b, c] p) :
        a ∈ w ∧ b ∈ w ∧ c ∈ w := by
      have hsubw : List.Sublist [a, b, c] w :=
        hsub.trans (by rw [← hU]; exact select_sublist U d.toList w)
      exact ⟨hsubw.subset (by simp), hsubw.subset (by simp),
        hsubw.subset (by simp)⟩
    have h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p := by
      rintro ⟨x, hxlt, _, hsub, _⟩
      change List.Sublist [x 1, x 3, x 2] p at hsub; have hm := hmem_sublist (x 1) (x 3) (x 2) hsub
      have horder := hfirst_sublist (x 1) (x 3) (x 2) hsub
      have h12 : x 1 < x 2 := hxlt 1 (by omega) (by decide)
      have h23 : x 2 < x 3 := hxlt 2 (by omega) (by decide)
      exact (htest (x 1) (x 2) (x 3) hm.1 hm.2.2 hm.2.1
        h12 h23).1 ⟨horder.1, horder.2⟩
    have h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p := by
      rintro ⟨x, hxlt, _, hsub, _⟩
      change List.Sublist [x 2, x 1, x 3] p at hsub; have hm := hmem_sublist (x 2) (x 1) (x 3) hsub
      have horder := hfirst_sublist (x 2) (x 1) (x 3) hsub
      have h12 : x 1 < x 2 := hxlt 1 (by omega) (by decide)
      have h23 : x 2 < x 3 := hxlt 2 (by omega) (by decide)
      exact (htest (x 1) (x 2) (x 3) hm.2.1 hm.1 hm.2.2
        h12 h23).2 ⟨horder.1, horder.2⟩
    exact ⟨h132, h213⟩
  let good := goodPositions n d
  let C := {c : Composition n //
    ∀ t (ht : t + 1 < n),
      (incBlocks n c.blocks)[t]'(by
        have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
          c.blocks_sum).length_eq
        simp only [List.length_range'] at hl
        omega) <
      (incBlocks n c.blocks)[t + 1]'(by
        have hl := (incBlocks_perm n c.blocks (fun _ h => c.blocks_pos h)
          c.blocks_sum).length_eq
        simp only [List.length_range'] at hl
        omega) → (⟨t, by omega⟩ : Fin (n - 1)) ∈ good}
  let W := {pd : royalPairs n // pd.1.2 = d ∧
    (royalEncoding n pd).1 ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]}
  let Y := {x : {w : List ℕ // w ∈ avoiders n []} //
    ((royalEncoding n).symm x).1.2 = d ∧
    x.1 ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]}
  have hencode (p : List ℕ) (hp : p.Perm (List.range' 1 n))
      (hlen : p.length = d.semilength)
      (hfirst : ¬ Occurs [1, 3, 2] p ∧ ¬ Occurs [2, 1, 3] p)
      (hgood : ∀ t (ht : t + 1 < n),
        p[t]'(by have h := hp.length_eq; omega) <
        p[t + 1]'(by have h := hp.length_eq; omega) →
        (⟨t, by omega⟩ : Fin (n - 1)) ∈ good) :
      (weave p p d.toList).getD [] ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]] := by
    let w := (weave p p d.toList).getD []
    obtain ⟨hbase, hnn, _, hU⟩ := encode_data n p hp d hlen
    have hcount : ∀ a ∈ w, w.count a = 2 := by
      intro a ha
      have hb : a ∈ List.range' 1 n := by
        have hm := hbase.subset ha
        simpa using hm
      exact doubled_count n a w hbase hb
    have hscan : scan ∅ w = d.toList :=
      scan_encode n p d hp hlen
    have hU' : select U d.toList w = p := by
      rw [← hscan]; exact hU
    have hD : select D d.toList w = p := by
      have heq := equal_queues_of_nonnesting w hcount hnn
      rw [hscan] at heq; exact heq.symm.trans hU'
    have hgap : ∀ u v z : List DyckStep,
        d.toList = u ++ [D] ++ v ++ [D] ++ z → v.count D = 0 →
        (ht : u.count D + 1 < p.length) →
        p[u.count D] < p[u.count D + 1] →
        v = [] ∨ (v = [U] ∧ u.count U = u.count D + 1) := by
      intro u v z hs hv ht hasc
      have htn : u.count D + 1 < n := by
        have hl := hp.length_eq; omega
      have hg : (⟨u.count D, by omega⟩ : Fin (n - 1)) ∈ good :=
        hgood (u.count D) htn (by simpa using hasc)
      exact (Finset.mem_filter.mp hg).2 u v z hs hv rfl
    have hlow := good_gaps_avoid_low d w p hscan hcount hnn
      hU' hD
      ((hp.nodup_iff).mpr List.nodup_range') hfirst.1 hfirst.2 hgap
    exact ⟨hbase, hnn.1, hnn.2, by
      intro σ hσ; simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with rfl | rfl
      · exact hlow.1
      · exact hlow.2⟩
  let toW : C → W := fun c => by
    let p := incBlocks n c.1.blocks; have hp : p.Perm (List.range' 1 n) :=
      incBlocks_perm n c.1.blocks (fun _ h => c.1.blocks_pos h) c.1.blocks_sum
    have hplen : p.length = n := by simpa using hp.length_eq
    have hlen : p.length = d.semilength := hplen.trans hd.symm
    let pd : royalPairs n := ⟨(p, d), hp, hlen⟩
    refine ⟨pd, rfl, ?_⟩
    change (weave p p d.toList).getD [] ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]
    exact hencode p hp hlen
      (incBlocks_avoids n c.1.blocks (fun _ h => c.1.blocks_pos h) c.1.blocks_sum)
      c.2
  have hclass (x : W) :
      ∃ ks : List ℕ, (∀ k ∈ ks, 0 < k) ∧ ks.sum = n ∧
        x.1.1.1 = incBlocks n ks := by
    let pd := x.1; let p := pd.1.1; let w := (royalEncoding n pd).1
    have hp : p.Perm (List.range' 1 n) := pd.2.1
    have hw : w ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]] := x.2.2
    have hscan : scan ∅ w = pd.1.2.toList :=
      scan_encode n p pd.1.2 hp pd.2.2
    have hU0 : select U (scan ∅ w) w = p :=
      (encode_data n p hp pd.1.2 pd.2.2).choose_spec.2.2
    have hcount : ∀ a ∈ w, w.count a = 2 := by
      intro a ha
      have hb : a ∈ List.range' 1 n := by
        have hm := hw.1.subset ha
        simpa using hm
      exact doubled_count n a w hw.1 hb
    have hfirst := low_first_order_avoids pd.1.2 w p hscan hcount
      ⟨hw.2.1, hw.2.2.1⟩
      ⟨hw.2.2.2 _ (by simp), hw.2.2.2 _ (by simp)⟩
      (by rw [← hscan]; exact hU0)
    exact avoids_has_inc_blocks n p hp hfirst.1 hfirst.2
  let fromW : W → C := fun x => by
    let pd := x.1; let p := pd.1.1; let w := (royalEncoding n pd).1
    have hp : p.Perm (List.range' 1 n) := pd.2.1
    have hlen : p.length = d.semilength := pd.2.2.trans (by rw [x.2.1])
    have hw : w ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]] := x.2.2
    have hscan : scan ∅ w = d.toList := by
      change scan ∅ ((weave p p pd.1.2.toList).getD []) = d.toList
      rw [scan_encode n p pd.1.2 hp pd.2.2,
        x.2.1]
    have hU0 : select U (scan ∅ w) w = p := by
      exact (encode_data n p hp pd.1.2 pd.2.2).choose_spec.2.2
    have hU : select U d.toList w = p := by
      rw [← hscan]; exact hU0
    have hcount : ∀ a ∈ w, w.count a = 2 := by
      intro a ha
      have hb : a ∈ List.range' 1 n := by
        have hm := hw.1.subset ha
        simpa using hm
      exact doubled_count n a w hw.1 hb
    have hD : select D d.toList w = p := by
      have heq := equal_queues_of_nonnesting w hcount ⟨hw.2.1, hw.2.2.1⟩
      rw [hscan] at heq; exact heq.symm.trans hU
    let hex := hclass x; let ks := Classical.choose hex; have hpos := (Classical.choose_spec hex).1
    have hsum := (Classical.choose_spec hex).2.1; have hform := (Classical.choose_spec hex).2.2
    let c : Composition n := ⟨ks, fun h => hpos _ h, hsum⟩
    refine ⟨c, ?_⟩
    intro t ht hasc
    have hpt : t + 1 < p.length := by have hl := hp.length_eq; omega
    have hq : (incBlocks n ks).length = n := by
      simpa using (incBlocks_perm n ks hpos hsum).length_eq
    have hval0 : p[t] = (incBlocks n ks)[t] := by
      apply Option.some.inj
      calc
        some p[t] = p[t]? := (List.getElem?_eq_getElem (by omega)).symm
        _ = (incBlocks n ks)[t]? := congrArg (fun l : List ℕ => l[t]?) hform
        _ = some (incBlocks n ks)[t] := List.getElem?_eq_getElem (by omega)
    have hval1 : p[t + 1] = (incBlocks n ks)[t + 1] := by
      apply Option.some.inj
      calc
        some p[t + 1] = p[t + 1]? := (List.getElem?_eq_getElem hpt).symm
        _ = (incBlocks n ks)[t + 1]? :=
          congrArg (fun l : List ℕ => l[t + 1]?) hform
        _ = some (incBlocks n ks)[t + 1] := List.getElem?_eq_getElem (by omega)
    have hasc' : p[t] < p[t + 1] := by
      rw [hval0, hval1]; exact hasc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro u v z hs hv hrank
    have ht' : u.count D + 1 < p.length := by omega
    have hasc'' : p[u.count D] < p[u.count D + 1] := by
      simpa only [hrank] using hasc'
    exact ascent_forces_good_gap d w p hscan hcount
      ⟨hw.2.1, hw.2.2.1⟩
      ⟨hw.2.2.2 _ (by simp), hw.2.2.2 _ (by simp)⟩
      hU hD ((hp.nodup_iff).mpr List.nodup_range')
      u v z hs hv ht' hasc''
  have hfromW (x : W) : x.1.1.1 = incBlocks n (fromW x).1.blocks := by
    change x.1.1.1 = incBlocks n (Classical.choose (hclass x))
    exact (Classical.choose_spec (hclass x)).2.2
  have hinv₁ : ∀ c : C, fromW (toW c) = c := by
    intro c; apply Subtype.ext
    have heq : incBlocks n (fromW (toW c)).1.blocks = incBlocks n c.1.blocks := by
      simpa only [toW] using (hfromW (toW c)).symm
    apply Composition.ext; exact incBlocks_unique n (fromW (toW c)).1.blocks c.1.blocks
      (fun _ h => (fromW (toW c)).1.blocks_pos h)
      (fun _ h => c.1.blocks_pos h)
      (fromW (toW c)).1.blocks_sum c.1.blocks_sum heq
  have hinv₂ : ∀ x : W, toW (fromW x) = x := by
    intro x; apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · exact (hfromW x).symm
    · exact x.2.1.symm
  have e : C ≃ W :=
    { toFun := toW, invFun := fromW, left_inv := hinv₁, right_inv := hinv₂ }
  have eWord : W ≃ Y := by
    refine Equiv.subtypeEquiv (royalEncoding n) ?_
    intro pd; simp only [Equiv.symm_apply_apply]
  exact e.trans eWord
end D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowFiber
