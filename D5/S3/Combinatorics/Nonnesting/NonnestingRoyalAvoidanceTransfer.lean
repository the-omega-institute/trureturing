/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingRoyalAvoidanceTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingRoyalAvoidanceTransfer
   mirror-E: none(waiver:royal-occurrence-rank-transfer)
   anchors: []
   utility: none
   digest: Transfers Royal avoidance between block words with reflected occurrence positions. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncConverse
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHookBlocks
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBijection
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
namespace D5.S3.Combinatorics.Nonnesting.NonnestingRoyalAvoidanceTransfer
open scoped symmDiff
open DyckStep NonnestingDefs NonnestingBasicOrders NonnestingBasicRoyalEncoding
  NonnestingBasicRoyalShape NonnestingBasicRoyalIncBlocks NonnestingBasicRoyalHookBlocks
  NonnestingBasicRoyalIncConverse
local notation "toggle" =>
  (fun (active : Finset ℕ) (letter : ℕ) => active ∆ Singleton.singleton letter)
set_option maxHeartbeats 2000000 in
theorem avoidance_transfer (n : ℕ) (ks : List ℕ)
    (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n) (w v : List ℕ)
    (hw : ∀ a ∈ w, w.count a = 2) (hv : ∀ a ∈ v, v.count a = 2)
    (hnw : ¬ Occurs [1, 2, 2, 1] w ∧ ¬ Occurs [2, 1, 1, 2] w)
    (hnv : ¬ Occurs [1, 2, 2, 1] v ∧ ¬ Occurs [2, 1, 1, 2] v)
    (hqw : select U (scan ∅ w) w = incBlocks n ks)
    (hqv : select U (scan ∅ v) v = hookBlocks n ks.reverse)
    (hfv : ∀ i, i < n → v.idxOf (hookBlocks n ks.reverse)[n - 1 - i]! +
        secondPos (incBlocks n ks)[i]! w + 1 = w.length)
    (hsv : ∀ i, i < n → secondPos (hookBlocks n ks.reverse)[n - 1 - i]! v +
        w.idxOf (incBlocks n ks)[i]! + 1 = w.length) :
    (¬ Occurs [1, 1, 3, 2] w ∧ ¬ Occurs [2, 2, 1, 3] w) ↔
      (¬ Occurs [1, 2, 3, 3] v ∧ ¬ Occurs [1, 3, 2, 2] v) := by
  classical
  have member (t : List ℕ) (a i : ℕ) (hi : i < t.length) (hv : t[i]! = a) : a ∈ t := by
    have hval : t[i] = a := by
      simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some] using hv
    exact hval ▸ List.getElem_mem hi
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
      have hd : u.drop (u.length + 1) = [] := by apply List.drop_eq_nil_iff.mpr; omega
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
  have quadruplePositions (word : List ℕ) (one two three four : ℕ) :
      [one, two, three, four].Sublist word ↔
        ∃ first second third fourth : ℕ, first < second ∧ second < third ∧ third < fourth ∧
          word[first]? = some one ∧ word[second]? = some two ∧
          word[third]? = some three ∧ word[fourth]? = some four := by
    constructor
    · intro sublist
      obtain ⟨embedding, values⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp sublist
      refine ⟨(embedding 0).val, (embedding 1).val, (embedding 2).val, (embedding 3).val,
        embedding.strictMono (by decide : (0 : Fin 4) < 1),
        embedding.strictMono (by decide : (1 : Fin 4) < 2),
        embedding.strictMono (by decide : (2 : Fin 4) < 3), ?_⟩
      have atPosition (slot : Fin 4) : word[(embedding slot).val]? =
          some ([one, two, three, four].get slot) := by
        rw [List.getElem?_eq_getElem (embedding slot).isLt]
        exact congrArg some (values slot).symm
      exact ⟨by simpa using atPosition 0, by simpa using atPosition 1,
        by simpa using atPosition 2, by simpa using atPosition 3⟩
    · rintro ⟨first, second, third, fourth, orderFS, orderST, orderTF,
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
  have orderedPositions (word : List ℕ) (copies : ∀ x ∈ word, word.count x = 2)
      (hnn : ¬ Occurs [1, 2, 2, 1] word ∧ ¬ Occurs [2, 1, 1, 2] word)
      (left right : ℕ) (left_mem : left ∈ word) (right_mem : right ∈ word)
      (different : left ≠ right) :
      (word.idxOf left < word.idxOf right ∧ secondPos left word < secondPos right word) ∨
      (word.idxOf right < word.idxOf left ∧ secondPos right word < secondPos left word) := by
    have orders := (nonnesting_iff_equal_orders word copies).mp hnn
    have indices_differ : word.idxOf left ≠ word.idxOf right := by
      intro equality; have values := congrArg (fun index => word[index]?) equality
      rw [List.getElem?_idxOf left_mem, List.getElem?_idxOf right_mem] at values
      exact different (Option.some.inj values)
    by_cases order : word.idxOf left < word.idxOf right
    · exact Or.inl ⟨order, orders left left_mem right right_mem order⟩
    · have opposite : word.idxOf right < word.idxOf left := by omega
      exact Or.inr ⟨opposite, orders right right_mem left left_mem opposite⟩
  have low_local_test (w : List ℕ) (hcount : ∀ x ∈ w, w.count x = 2)
      (hnn : ¬ Occurs [1, 2, 2, 1] w ∧ ¬ Occurs [2, 1, 1, 2] w)
      (hfirst : ∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
        ¬ (w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b) ∧
        ¬ (w.idxOf b < w.idxOf a ∧ w.idxOf a < w.idxOf c)) :
      (¬ Occurs [1, 1, 3, 2] w ∧ ¬ Occurs [2, 2, 1, 3] w) ↔
      ∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
        ¬ (w.idxOf a < w.idxOf b ∧ w.idxOf b < w.idxOf c ∧
        secondPos a w < w.idxOf c ∧ w.idxOf c < secondPos b w) ∧
        ¬ (w.idxOf b < w.idxOf c ∧ w.idxOf c < w.idxOf a ∧
        secondPos b w < w.idxOf a ∧ w.idxOf a < secondPos c w) := by
    constructor
    · intro havoid a b c ha hb hc hab hbc
      constructor
      · intro crossing
        apply havoid.1
        apply (occursTriple w [1, 1, 3, 2] (by decide) (by decide)).mpr
        refine ⟨a, b, c, hab, hbc, ha, hb, hc, ?_⟩
        have sublist := (quadruplePositions w a a c b).mpr
          ⟨w.idxOf a, secondPos a w, w.idxOf c, secondPos b w,
            by unfold secondPos; omega, crossing.2.2.1, crossing.2.2.2,
            List.getElem?_idxOf ha,
            secondOccurrence w a (hcount a ha),
            List.getElem?_idxOf hc,
            secondOccurrence w b (hcount b hb)⟩
        simpa using sublist
      · intro crossing
        apply havoid.2
        apply (occursTriple w [2, 2, 1, 3] (by decide) (by decide)).mpr
        refine ⟨a, b, c, hab, hbc, ha, hb, hc, ?_⟩
        have sublist := (quadruplePositions w b b a c).mpr
          ⟨w.idxOf b, secondPos b w, w.idxOf a, secondPos c w,
            by unfold secondPos; omega, crossing.2.2.1, crossing.2.2.2,
            List.getElem?_idxOf hb,
            secondOccurrence w b (hcount b hb),
            List.getElem?_idxOf ha,
            secondOccurrence w c (hcount c hc)⟩
        simpa using sublist
    · intro htest
      constructor
      · intro occurrence
        obtain ⟨a, b, c, hab, hbc, ha, hb, hc, sublist⟩ :=
          (occursTriple w [1, 1, 3, 2] (by decide) (by decide)).mp occurrence
        obtain ⟨first, second, third, fourth, orderFS, orderST, orderTF,
          entryF, entryS, entryT, entryL⟩ :=
          (quadruplePositions w a a c b).mp (by simpa using sublist)
        have repeatF := occurrencePositions w a first
          (hcount a ha) entryF
        have repeatS := occurrencePositions w a second
          (hcount a ha) entryS
        have repeated : first = w.idxOf a ∧
            second = secondPos a w := by
          have less : w.idxOf a < secondPos a w := by unfold secondPos; omega
          omega
        have position0 := occurrencePositions w c third
          (hcount c hc) entryT
        have position1 := occurrencePositions w b fourth
          (hcount b hb) entryL
        have orderAB := orderedPositions w hcount hnn a b ha hb (by omega)
        have orderAC := orderedPositions w hcount hnn a c ha hc (by omega)
        have orderBC := orderedPositions w hcount hnn b c hb hc (by omega)
        have restricted := hfirst a b c ha hb hc hab hbc
        have obstruction := htest a b c ha hb hc hab hbc
        have less : w.idxOf a < secondPos a w ∧ w.idxOf b < secondPos b w ∧
            w.idxOf c < secondPos c w := by simp only [secondPos]; omega
        omega
      · intro occurrence
        obtain ⟨a, b, c, hab, hbc, ha, hb, hc, sublist⟩ :=
          (occursTriple w [2, 2, 1, 3] (by decide) (by decide)).mp occurrence
        obtain ⟨first, second, third, fourth, orderFS, orderST, orderTF,
          entryF, entryS, entryT, entryL⟩ :=
          (quadruplePositions w b b a c).mp (by simpa using sublist)
        have repeatF := occurrencePositions w b first
          (hcount b hb) entryF
        have repeatS := occurrencePositions w b second
          (hcount b hb) entryS
        have repeated : first = w.idxOf b ∧
            second = secondPos b w := by
          have less : w.idxOf b < secondPos b w := by unfold secondPos; omega
          omega
        have position0 := occurrencePositions w a third
          (hcount a ha) entryT
        have position1 := occurrencePositions w c fourth
          (hcount c hc) entryL
        have orderAB := orderedPositions w hcount hnn a b ha hb (by omega)
        have orderAC := orderedPositions w hcount hnn a c ha hc (by omega)
        have orderBC := orderedPositions w hcount hnn b c hb hc (by omega)
        have restricted := hfirst a b c ha hb hc hab hbc
        have obstruction := htest a b c ha hb hc hab hbc
        have less : w.idxOf a < secondPos a w ∧ w.idxOf b < secondPos b w ∧
            w.idxOf c < secondPos c w := by simp only [secondPos]; omega
        omega
  have high_local_test (w : List ℕ) (hcount : ∀ x ∈ w, w.count x = 2)
      (hnn : ¬ Occurs [1, 2, 2, 1] w ∧ ¬ Occurs [2, 1, 1, 2] w)
      (hfirst : ∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
        ¬ (w.idxOf a < w.idxOf b ∧ w.idxOf b < w.idxOf c) ∧
        ¬ (w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b)) :
      (¬ Occurs [1, 2, 3, 3] w ∧ ¬ Occurs [1, 3, 2, 2] w) ↔
      ∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
        ¬ (w.idxOf b < w.idxOf a ∧ w.idxOf a < w.idxOf c ∧
        w.idxOf a < secondPos b w ∧ secondPos b w < w.idxOf c) ∧
        ¬ (w.idxOf c < w.idxOf a ∧ w.idxOf a < w.idxOf b ∧
        w.idxOf a < secondPos c w ∧ secondPos c w < w.idxOf b) := by
    constructor
    · intro havoid a b c ha hb hc hab hbc
      constructor
      · intro crossing
        apply havoid.1
        apply (occursTriple w [1, 2, 3, 3] (by decide) (by decide)).mpr
        refine ⟨a, b, c, hab, hbc, ha, hb, hc, ?_⟩
        have sublist := (quadruplePositions w a b c c).mpr
          ⟨w.idxOf a, secondPos b w, w.idxOf c, secondPos c w,
            crossing.2.2.1, crossing.2.2.2, by unfold secondPos; omega,
            List.getElem?_idxOf ha,
            secondOccurrence w b (hcount b hb),
            List.getElem?_idxOf hc,
            secondOccurrence w c (hcount c hc)⟩
        simpa using sublist
      · intro crossing
        apply havoid.2
        apply (occursTriple w [1, 3, 2, 2] (by decide) (by decide)).mpr
        refine ⟨a, b, c, hab, hbc, ha, hb, hc, ?_⟩
        have sublist := (quadruplePositions w a c b b).mpr
          ⟨w.idxOf a, secondPos c w, w.idxOf b, secondPos b w,
            crossing.2.2.1, crossing.2.2.2, by unfold secondPos; omega,
            List.getElem?_idxOf ha,
            secondOccurrence w c (hcount c hc),
            List.getElem?_idxOf hb,
            secondOccurrence w b (hcount b hb)⟩
        simpa using sublist
    · intro htest
      constructor
      · intro occurrence
        obtain ⟨a, b, c, hab, hbc, ha, hb, hc, sublist⟩ :=
          (occursTriple w [1, 2, 3, 3] (by decide) (by decide)).mp occurrence
        obtain ⟨first, second, third, fourth, orderFS, orderST, orderTF,
          entryF, entryS, entryT, entryL⟩ :=
          (quadruplePositions w a b c c).mp (by simpa using sublist)
        have repeatF := occurrencePositions w c third
          (hcount c hc) entryT
        have repeatS := occurrencePositions w c fourth
          (hcount c hc) entryL
        have repeated : third = w.idxOf c ∧
            fourth = secondPos c w := by
          have less : w.idxOf c < secondPos c w := by unfold secondPos; omega
          omega
        have position0 := occurrencePositions w a first
          (hcount a ha) entryF
        have position1 := occurrencePositions w b second
          (hcount b hb) entryS
        have orderAB := orderedPositions w hcount hnn a b ha hb (by omega)
        have orderAC := orderedPositions w hcount hnn a c ha hc (by omega)
        have orderBC := orderedPositions w hcount hnn b c hb hc (by omega)
        have restricted := hfirst a b c ha hb hc hab hbc
        have obstruction := htest a b c ha hb hc hab hbc
        have less : w.idxOf a < secondPos a w ∧ w.idxOf b < secondPos b w ∧
            w.idxOf c < secondPos c w := by simp only [secondPos]; omega
        omega
      · intro occurrence
        obtain ⟨a, b, c, hab, hbc, ha, hb, hc, sublist⟩ :=
          (occursTriple w [1, 3, 2, 2] (by decide) (by decide)).mp occurrence
        obtain ⟨first, second, third, fourth, orderFS, orderST, orderTF,
          entryF, entryS, entryT, entryL⟩ :=
          (quadruplePositions w a c b b).mp (by simpa using sublist)
        have repeatF := occurrencePositions w b third
          (hcount b hb) entryT
        have repeatS := occurrencePositions w b fourth
          (hcount b hb) entryL
        have repeated : third = w.idxOf b ∧
            fourth = secondPos b w := by
          have less : w.idxOf b < secondPos b w := by unfold secondPos; omega
          omega
        have position0 := occurrencePositions w a first
          (hcount a ha) entryF
        have position1 := occurrencePositions w c second
          (hcount c hc) entryS
        have orderAB := orderedPositions w hcount hnn a b ha hb (by omega)
        have orderAC := orderedPositions w hcount hnn a c ha hc (by omega)
        have orderBC := orderedPositions w hcount hnn b c hb hc (by omega)
        have restricted := hfirst a b c ha hb hc hab hbc
        have obstruction := htest a b c ha hb hc hab hbc
        have less : w.idxOf a < secondPos a w ∧ w.idxOf b < secondPos b w ∧
            w.idxOf c < secondPos c w := by simp only [secondPos]; omega
        omega
  have block_crossing_transfer (n : ℕ) (ks : List ℕ)
      (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n) (f s : ℕ → ℕ)
      (hs : ∀ i j, i < j → j < n → s i < s j) : (∃ i j k : ℕ, i < j ∧ j < k ∧ k < n ∧
        (incBlocks n ks)[i]! < (incBlocks n ks)[j]! ∧ s i < f k ∧ f k < s j) ↔
      (∃ i j k : ℕ, i < j ∧ j < k ∧ k < n ∧ ((hookBlocks n ks.reverse).reverse)[j]! <
          ((hookBlocks n ks.reverse).reverse)[i]! ∧ ((hookBlocks n ks.reverse).reverse)[j]! <
          ((hookBlocks n ks.reverse).reverse)[k]! ∧ s i < f k ∧ f k < s j) := by
    have hshift : ∀ (xs : List ℕ) (m a : ℕ), (∀ x ∈ xs, 0 < x) → xs.sum = m →
        hookBlocks (m + a) xs = (hookBlocks m xs).map (· + a) := by
      intro xs; induction xs with
      | nil => intro m a hp hm; simp [hookBlocks]
      | cons r xs ih =>
        intro m a hp hm; have hr : 0 < r := hp r (by simp)
        have hrm : r ≤ m := (by simp only [List.sum_cons] at hm; omega)
        have hp' : ∀ x ∈ xs, 0 < x := (by intro x hx; exact hp x (by simp [hx]))
        have hm' : xs.sum = m - r := (by simp only [List.sum_cons] at hm; omega)
        have he : m + a - r = m - r + a := (by omega)
        simp only [hookBlocks, List.map_append, List.map_singleton, he, ih (m - r) a hp' hm']
        congr 2; rw [List.map_ofFn]; apply congrArg List.ofFn
        funext i; simp only [Function.comp_apply]; omega
    have happend : ∀ (xs ys : List ℕ) (m : ℕ), (∀ x ∈ xs, 0 < x) →
        hookBlocks (xs.sum + m) (xs ++ ys) = hookBlocks (xs.sum + m) xs ++ hookBlocks m ys := by
      intro xs; induction xs with
      | nil => intro ys m hp; simp [hookBlocks]
      | cons r xs ih =>
        intro ys m hp; have hp' : ∀ x ∈ xs, 0 < x := (by intro x hx; exact hp x (by simp [hx]))
        have he : (r :: xs).sum + m - r = xs.sum + m := (by simp; omega)
        simp only [List.cons_append, hookBlocks, he, ih ys m hp', List.append_assoc]
    have hsplit (r : ℕ) (xs : List ℕ) (m : ℕ)
        (hr : 0 < r) (hp : ∀ x ∈ xs, 0 < x) (hm : xs.sum = m) :
        (hookBlocks (r + m) (r :: xs).reverse).reverse = ([r] ++ List.range' 1 (r - 1)) ++
            ((hookBlocks m xs.reverse).reverse.map (· + r)) := by
      have hpr : ∀ x ∈ xs.reverse, 0 < x := (by intro x hx; exact hp x (by simpa using hx))
      have hrange : (List.ofFn (fun i : Fin (r - 1) => r - i.val - 1)).reverse =
            List.range' 1 (r - 1) := by
        apply List.ext_getElem
        · simp
        · intro i hi hj
          simp only [List.getElem_reverse, List.getElem_ofFn, List.getElem_range', List.length_ofFn]
          have hib : i < r - 1 := (by simpa using hj); omega
      have he : r + m = xs.reverse.sum + r := (by simp [hm, Nat.add_comm])
      rw [List.reverse_cons, he, happend xs.reverse [r] r hpr]
      simp only [hookBlocks, List.append_nil, List.reverse_append, List.reverse_singleton, hrange]
      rw [show xs.reverse.sum + r = m + r by simp [hm],
        hshift xs.reverse m r hpr (by simpa using hm), List.map_reverse]
    have hdata : ∀ (xs : List ℕ) (m : ℕ), (∀ x ∈ xs, 0 < x) → xs.sum = m →
        let p := incBlocks m xs; let q := (hookBlocks m xs.reverse).reverse
        p.length = m ∧ q.length = m ∧ (∀ a ∈ p, 1 ≤ a ∧ a ≤ m) ∧ (∀ a ∈ q, 1 ≤ a ∧ a ≤ m) ∧
        (∀ i j, i < j → j < m → q[j]! < q[i]! → p[i]! < p[j]!) ∧
        (∀ i j, i < j → j < m → p[i]! < p[j]! → ∃ b, b ≤ i ∧ b < j ∧ q[j]! < q[b]!) ∧
        (∀ i j k, i < j → j < k → k < m → q[j]! < q[i]! → q[j]! < q[k]!) := by
      intro xs; induction xs with
      | nil =>
        intro m hp hm
        have he : m = 0 := (by simpa using hm.symm); subst m; simp [incBlocks, hookBlocks]
      | cons r xs ih =>
        intro m hp hm; have hr : 0 < r := hp r (by simp)
        have hrm : r ≤ m := (by simp only [List.sum_cons] at hm; omega)
        have hp' : ∀ x ∈ xs, 0 < x := (by intro x hx; exact hp x (by simp [hx]))
        have hm' : xs.sum = m - r := (by simp only [List.sum_cons] at hm; omega)
        obtain ⟨hpl, hql, hpb, hqb, hdesc, hmin, hafter⟩ := ih (m - r) hp' hm'
        let p := incBlocks (m - r) xs; let q := (hookBlocks (m - r) xs.reverse).reverse
        change ∀ a ∈ p, 1 ≤ a ∧ a ≤ m - r at hpb; change ∀ a ∈ q, 1 ≤ a ∧ a ≤ m - r at hqb
        change ∀ i j, i < j → j < m - r → q[j]! < q[i]! → p[i]! < p[j]! at hdesc
        change ∀ i j, i < j → j < m - r → p[i]! < p[j]! → ∃ b, b ≤ i ∧ b < j ∧ q[j]! < q[b]! at hmin
        change ∀ i j k, i < j → j < k → k < m - r → q[j]! < q[i]! → q[j]! < q[k]! at hafter
        have hshape : (hookBlocks m (r :: xs).reverse).reverse =
            ([r] ++ List.range' 1 (r - 1)) ++ q.map (· + r) := by
          have he : r + (m - r) = m := (by omega)
          simpa [he, q] using hsplit r xs (m - r) hr hp' hm'
        have hqlen : q.length = m - r := hql; have hplen : p.length = m - r := hpl
        have hP (a : ℕ) (ha : a < m) : (incBlocks m (r :: xs))[a]! =
              if a < r then m - r + 1 + a else p[a - r]! := by
          by_cases har : a < r
          · simp only [incBlocks, List.getElem!_eq_getElem?_getD,
              List.getElem?_append, List.length_range', if_pos har,
              List.getElem?_range' har, Option.getD_some, Nat.one_mul]
          · simp only [incBlocks, List.getElem!_eq_getElem?_getD,
              List.getElem?_append, List.length_range', if_neg har, p]
        have hQ (a : ℕ) (ha : a < m) : ((hookBlocks m (r :: xs).reverse).reverse)[a]! =
              if a < r then (if a = 0 then r else a) else q[a - r]! + r := by
          rw [hshape]
          by_cases har : a < r
          · have hlen : ([r] ++ List.range' 1 (r - 1)).length = r := by simp; omega
            simp only [if_pos har, List.getElem!_eq_getElem?_getD]
            rw [List.getElem?_append_left (by simpa only [hlen] using har)]
            by_cases ha0 : a = 0
            · simp [ha0]
            · have hsub : a - 1 < r - 1 := by omega
              rw [List.getElem?_append_right (by simp; omega)]
              simp only [List.length_singleton, List.getElem?_range' hsub,
                Option.getD_some, if_neg ha0, Nat.one_mul]
              omega
          · have hab : a - r < q.length := by omega
            have hlen : ([r] ++ List.range' 1 (r - 1)).length = r := (by simp; omega)
            simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append, hlen,
              if_neg har, List.getElem?_map, List.getElem?_eq_getElem hab,
              Option.map_some, Option.getD_some]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [incBlocks, List.length_append, List.length_range', hpl]; omega
        · rw [hshape]; simp [hqlen]; omega
        · intro a ha
          change a ∈ List.range' (m - r + 1) r ++ p at ha
          rcases List.mem_append.mp ha with ha | ha
          · have := List.mem_range'_1.mp ha; omega
          · have := hpb a ha; omega
        · intro a ha
          rw [hshape] at ha
          rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_append.mp ha with ha | ha
            · simp only [List.mem_singleton] at ha
              omega
            · have := List.mem_range'_1.mp ha; omega
          · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
            have := hqb b hb; omega
        · intro i j hij hj hqi
          rw [hQ i (by omega), hQ j hj] at hqi; rw [hP i (by omega), hP j hj]
          by_cases hjr : j < r
          · have hir : i < r := by omega
            simp [hir, hjr]; omega
          · by_cases hir : i < r
            · have hb := hqb q[j - r]! (member q _ (j - r) (by omega) rfl)
              simp [hir, hjr] at hqi
              split_ifs at hqi <;> omega
            · simp only [if_neg hir, if_neg hjr] at hqi ⊢
              exact hdesc (i - r) (j - r) (by omega) (by omega) (by omega)
        · intro i j hij hj hpij
          rw [hP i (by omega), hP j hj] at hpij
          by_cases hjr : j < r
          · have hir : i < r := by omega
            refine ⟨0, by omega, by omega, ?_⟩
            rw [hQ j hj, hQ 0 (by omega)]; simp [hjr, show j ≠ 0 by omega, hr]
          · by_cases hir : i < r
            · have hb := hpb p[j - r]! (member p _ (j - r) (by omega) rfl)
              simp only [if_pos hir, if_neg hjr] at hpij; omega
            · simp only [if_neg hir, if_neg hjr] at hpij
              obtain ⟨b, hbi, hbj, hqb⟩ := hmin (i - r) (j - r) (by omega) (by omega) hpij
              refine ⟨r + b, by omega, by omega, ?_⟩
              rw [hQ j hj, hQ (r + b) (by omega)]
              simp only [if_neg hjr, if_neg (show ¬ r + b < r by omega), Nat.add_sub_cancel_left]
              omega
        · intro i j k hij hjk hk hqij
          rw [hQ i (by omega), hQ j (by omega)] at hqij; rw [hQ j (by omega), hQ k hk]
          by_cases hjr : j < r
          · have hir : i < r := by omega
            have hj0 : j ≠ 0 := (by omega)
            by_cases hkr : k < r
            · simp [hjr, hkr, hj0, show k ≠ 0 by omega]; omega
            · have hb := hqb q[k - r]! (member q _ (k - r) (by omega) rfl)
              simp [hjr, hkr, hj0]; omega
          · have hkr : ¬ k < r := by omega
            by_cases hir : i < r
            · have hb := hqb q[j - r]! (member q _ (j - r) (by omega) rfl)
              simp [hir, hjr] at hqij
              split_ifs at hqij <;> omega
            · simp only [if_neg hir, if_neg hjr] at hqij
              simp only [if_neg hjr, if_neg hkr]; have ht := hafter (i - r) (j - r) (k - r)
                (by omega) (by omega) (by omega) (by omega)
              omega
    obtain ⟨_, _, _, _, hdesc, hmin, hafter⟩ := hdata ks n hpos hsum
    constructor
    · rintro ⟨i, j, k, hij, hjk, hkn, hpij, hsi, hfj⟩
      obtain ⟨b, hbi, hbj, hqbj⟩ := hmin i j hij (by omega) hpij
      refine ⟨b, j, k, hbj, hjk, hkn, hqbj, hafter b j k hbj hjk hkn hqbj, ?_, hfj⟩
      by_cases he : b = i
      · simpa [he] using hsi
      · exact (hs b i (by omega) (by omega)).trans hsi
    · rintro ⟨i, j, k, hij, hjk, hkn, hqij, _, hsi, hfj⟩
      exact ⟨i, j, k, hij, hjk, hkn, hdesc i j hij (by omega) hqij, hsi, hfj⟩
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
  have foldl_toggle_parity (s : Finset ℕ) (w : List ℕ) (a : ℕ) : a ∈ w.foldl toggle s ↔
        if w.count a % 2 = 0 then a ∈ s else a ∉ s := by
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
  have hookBlocks_avoids (n : ℕ) (ks : List ℕ) (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n) :
      ¬ NonnestingDefs.Occurs [1, 2, 3] (hookBlocks n ks) ∧
        ¬ NonnestingDefs.Occurs [1, 3, 2] (hookBlocks n ks) := by
    have bounded : ∀ (m : ℕ) (xs : List ℕ), (∀ x ∈ xs, 0 < x) → xs.sum ≤ m →
        ∀ a ∈ hookBlocks m xs, a ≤ m := by
      intro m xs; induction xs generalizing m with
      | nil =>
        intro _ _ a ha; simp [hookBlocks] at ha
      | cons r xs ih =>
        intro hp hs a ha
        have hr : r ≤ m := by
          simp only [List.sum_cons] at hs; omega
        have hpos' : ∀ x ∈ xs, 0 < x := by
          intro x hx; exact hp x (by simp [hx])
        have hsum' : xs.sum ≤ m - r := by
          simp only [List.sum_cons] at hs; omega
        change a ∈ (List.ofFn (fun i : Fin (r - 1) => m - i.val - 1) ++ [m]) ++
          hookBlocks (m - r) xs at ha
        rcases List.mem_append.mp ha with hhead | htail
        · rcases List.mem_append.mp hhead with hpre | hmax
          · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpre
            rw [← hi]; omega
          · simp at hmax
            omega
        · have hb := ih (m - r) hpos' hsum' a htail
          omega
    have outer : ∀ (m : ℕ) (xs : List ℕ), (∀ x ∈ xs, 0 < x) → xs.sum ≤ m →
        ∀ i j k (hi : i < (hookBlocks m xs).length)
          (hj : j < (hookBlocks m xs).length)
          (hk : k < (hookBlocks m xs).length), i < j → j < k →
          (hookBlocks m xs)[i] > (hookBlocks m xs)[j] ∨
            (hookBlocks m xs)[i] > (hookBlocks m xs)[k] := by
      intro m xs; induction xs generalizing m with
      | nil =>
        intro _ _ i j k hi; simp [hookBlocks] at hi
      | cons r xs ih =>
        intro hp hs i j k hi hj hk hij hjk; let q := hookBlocks (m - r) xs
        have hr : r ≤ m := by
          simp only [List.sum_cons] at hs; omega
        have hrpos : 0 < r := hp r (by simp)
        have hpos' : ∀ x ∈ xs, 0 < x := by
          intro x hx; exact hp x (by simp [hx])
        have hsum' : xs.sum ≤ m - r := by
          simp only [List.sum_cons] at hs; omega
        have hlen : (hookBlocks m (r :: xs)).length = r + q.length := by
          simp [hookBlocks, q]; omega
        have hpre (a : ℕ) (ha : a < r - 1) : (hookBlocks m (r :: xs))[a] = m - a - 1 := by
          simp [hookBlocks, ha]
        have hmax : (hookBlocks m (r :: xs))[r - 1] = m := by
          simp [hookBlocks]
        have htail (a : ℕ) (ha : r ≤ a) (hal : a < (hookBlocks m (r :: xs)).length) :
            (hookBlocks m (r :: xs))[a] = q[a - r] := by
          have hindex : a - (r - 1) = (a - r) + 1 := (by omega)
          simp [hookBlocks, List.getElem_append, q, show ¬ a < r - 1 by omega, hindex]
        have hfirst (a : ℕ) (ha : a < r) (hal : a < (hookBlocks m (r :: xs)).length) :
            m - r + 1 ≤ (hookBlocks m (r :: xs))[a] := by
          by_cases hbefore : a < r - 1
          · rw [hpre a hbefore]
            omega
          · have heq : a = r - 1 := by omega
            subst a; rw [hmax]; omega
        by_cases hir : i < r
        · by_cases hjpre : j < r - 1
          · have hipre : i < r - 1 := by omega
            left
            rw [hpre i hipre, hpre j hjpre]; omega
          · by_cases hjmax : j = r - 1
            · right
              have hkr : r ≤ k := (by omega)
              have hkq : k - r < q.length := (by rw [hlen] at hk; omega)
              have hb := bounded (m - r) xs hpos' hsum'
                q[k - r] (List.getElem_mem hkq)
              rw [htail k hkr hk]; have hli := hfirst i hir hi; omega
            · left
              have hjr : r ≤ j := (by omega)
              have hjq : j - r < q.length := (by rw [hlen] at hj; omega)
              have hb := bounded (m - r) xs hpos' hsum'
                q[j - r] (List.getElem_mem hjq)
              rw [htail j hjr hj]; have hli := hfirst i hir hi; omega
        · have hir' : r ≤ i := by omega
          have hjr : r ≤ j := (by omega); have hkr : r ≤ k := (by omega)
          have hiq : i - r < q.length := (by rw [hlen] at hi; omega)
          have hjq : j - r < q.length := (by rw [hlen] at hj; omega)
          have hkq : k - r < q.length := (by rw [hlen] at hk; omega)
          have hshift : i - r < j - r ∧ j - r < k - r := (by omega)
          have hrec := ih (m - r) hpos' hsum' (i - r) (j - r) (k - r)
            hiq hjq hkq hshift.1 hshift.2
          rw [htail i hir' hi, htail j hjr hj, htail k hkr hk]; exact hrec
    have hbad : ∀ (a b c : ℕ), a < b → a < c → ¬ List.Sublist [a, b, c] (hookBlocks n ks) := by
      intro a b c hab hac hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
      have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
      have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
      have hvalI : (hookBlocks n ks)[i] = a := by
        simpa [i] using (hf (0 : Fin 3)).symm
      have hvalJ : (hookBlocks n ks)[j] = b := by
        simpa [j] using (hf (1 : Fin 3)).symm
      have hvalK : (hookBlocks n ks)[k] = c := by
        simpa [k] using (hf (2 : Fin 3)).symm
      have houter := outer n ks hpos (by omega) i j k
        (f 0).isLt (f 1).isLt (f 2).isLt hij hjk
      rw [hvalI, hvalJ, hvalK] at houter; omega
    constructor
    · intro hocc
      obtain ⟨x, hxlt, _, hsub, _⟩ := hocc
      change List.Sublist [x 1, x 2, x 3] (hookBlocks n ks) at hsub
      have h12 : x 1 < x 2 := (by simpa using hxlt 1 (by omega) (by decide))
      have h23 : x 2 < x 3 := (by simpa using hxlt 2 (by omega) (by decide))
      exact hbad (x 1) (x 2) (x 3) h12 (h12.trans h23) hsub
    · intro hocc
      obtain ⟨x, hxlt, _, hsub, _⟩ := hocc
      change List.Sublist [x 1, x 3, x 2] (hookBlocks n ks) at hsub
      have h12 : x 1 < x 2 := (by simpa using hxlt 1 (by omega) (by decide))
      have h23 : x 2 < x 3 := (by simpa using hxlt 2 (by omega) (by decide))
      exact hbad (x 1) (x 3) (x 2) (h12.trans h23) h12 hsub
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
  have tagged_pair_positions (t : DyckStep) (d : List DyckStep) (w : List ℕ) (a b : ℕ)
      (hab : List.Sublist [(t, a), (t, b)] (d.zip w)) :
      ∃ i j : ℕ, i < j ∧ d[i]? = some t ∧ w[i]? = some a ∧ d[j]? = some t ∧ w[j]? = some b := by
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hab; let i := (f 0).val
    let j := (f 1).val; have hij : i < j := f.strictMono (show (0 : Fin 2) < 1 by decide)
    have hi : (d.zip w)[i]? = some (t, a) := by
      rw [List.getElem?_eq_getElem (f 0).isLt]; simpa using congrArg some (hf (0 : Fin 2)).symm
    have hj : (d.zip w)[j]? = some (t, b) := by
      rw [List.getElem?_eq_getElem (f 1).isLt]; simpa using congrArg some (hf (1 : Fin 2)).symm
    obtain ⟨hdi, hwi⟩ := List.getElem?_zip_eq_some.mp hi
    obtain ⟨hdj, hwj⟩ := List.getElem?_zip_eq_some.mp hj
    exact ⟨i, j, hij, hdi, hwi, hdj, hwj⟩
  have scan_first_second (a : ℕ) (w : List ℕ) (hw : w.count a = 2) :
      (scan ∅ w)[w.idxOf a]? = some U ∧
        (scan ∅ w)[NonnestingBasicOrders.secondPos a w]? = some D := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := NonnestingBasicOrders.count_two_decomposition a w hw
    have hf : (u ++ [a] ++ v ++ [a] ++ z).idxOf a = u.length := (by simp [List.idxOf_append, hu])
    have hs : NonnestingBasicOrders.secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := (by apply List.drop_eq_nil_iff.mpr; omega)
      simp [NonnestingBasicOrders.secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hf, scan_getElem?]
      simp [List.count_eq_zero.mpr hu, foldl_toggle_parity]
    · rw [hs, scan_getElem?]
      have hlen : (u ++ [a] ++ v).length = u.length + 1 + v.length := (by simp; omega)
      have hword : u ++ [a] ++ v ++ [a] ++ z = (u ++ [a] ++ v) ++ (a :: z) :=
        by simp [List.append_assoc]
      have ht : (u ++ [a] ++ v ++ [a] ++ z).take (u.length + 1 + v.length) = u ++ [a] ++ v := by
        rw [hword, ← hlen]; exact List.take_left
      have hget : (u ++ [a] ++ v ++ [a] ++ z)[u.length + 1 + v.length]? = some a := by
        rw [hword, ← hlen]; simp
      have hu0 : u.count a = 0 := List.count_eq_zero.mpr hu
      have hv0 : v.count a = 0 := List.count_eq_zero.mpr hv
      have hbefore : a ∉ u.foldl toggle ∅ := by
        have hpar := foldl_toggle_parity ∅ u a; simpa [hu0] using hpar
      have hafter : a ∈ toggle (u.foldl toggle ∅) a := (by simp [mem_toggle_iff, hbefore])
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
  have selectMember (tag : DyckStep) (steps : List DyckStep) (word : List ℕ) (index letter : ℕ)
      (step : steps[index]? = some tag) (entry : word[index]? = some letter) :
      letter ∈ select tag steps word := by
    induction steps generalizing word index with
    | nil => simp at step
    | cons head tail ih =>
      cases word with
      | nil => simp at entry
      | cons value rest =>
        cases index with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at step entry
                  subst head; subst value; simp [select]
        | succ index =>
          simp only [List.getElem?_cons_succ] at step entry
          have member := ih rest index step entry
          by_cases matched : head = tag <;> simp [select, matched, member]
  let p := incBlocks n ks; let r := hookBlocks n ks.reverse
  change select U (scan ∅ w) w = p at hqw; change select U (scan ∅ v) v = r at hqv
  have hp : p.length = n := by
    have length_eq (size : ℕ) (blocks : List ℕ) : (incBlocks size blocks).length = blocks.sum := by
      induction blocks generalizing size with
      | nil => rfl
      | cons part blocks ih => simp [incBlocks, ih]
    simpa [p, hsum] using length_eq n ks
  have hr : r.length = n := by
    have hlength : ∀ (xs : List ℕ) (m : ℕ),
        (∀ x ∈ xs, 0 < x) → (hookBlocks m xs).length = xs.sum := by
      intro xs; induction xs with
      | nil => intro m _; simp [hookBlocks]
      | cons k xs ih =>
        intro m h; have hk : 0 < k := h k (by simp)
        have ht : ∀ a ∈ xs, 0 < a := (by intro a ha; exact h a (by simp [ha]))
        simp only [hookBlocks, List.length_append, List.length_ofFn,
          List.length_singleton, ih (m - k) ht, List.sum_cons]
        omega
    simpa [r, hsum] using hlength ks.reverse n (by intro k hk; exact hpos k (by simpa using hk))
  have rankData (z t : List ℕ) (hz : ∀ a ∈ z, z.count a = 2)
      (hq : select U (scan ∅ z) z = t) (ht : t.length = n) :
      (∀ a ∈ z, t.idxOf a < n ∧ t[t.idxOf a]! = a) ∧ (∀ i, i < n → t[i]! ∈ z) ∧
      (∀ i j, i < j → j < n → z.idxOf t[i]! < z.idxOf t[j]!) ∧
      (∀ a b, a ∈ z → b ∈ z → z.idxOf a < z.idxOf b → t.idxOf a < t.idxOf b) := by
    have hm (a : ℕ) (ha : a ∈ z) : a ∈ t := by
      have selected := selectMember U (scan ∅ z) z (z.idxOf a) a
        (scan_first_second a z (hz a ha)).1 (List.getElem?_idxOf ha)
      rwa [hq] at selected
    have hpair := queue_pairwise_position U z hz; rw [hq] at hpair
    have hvals (i : ℕ) (hi : i < n) : t[i]! = t[i]'(by omega) := by
      simp only [List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : i < t.length), Option.getD_some]
    have horder (i j : ℕ) (hij : i < j) (hj : j < n) : z.idxOf t[i]! < z.idxOf t[j]! := by
      rw [hvals i (by omega), hvals j hj]; simpa only [ite_true] using
        (List.pairwise_iff_getElem.mp hpair) i j (by omega) (by omega) hij
    have hindex (a : ℕ) (ha : a ∈ z) : t.idxOf a < n ∧ t[t.idxOf a]! = a := by
      have htmem := hm a ha; have hi := List.idxOf_lt_length_of_mem htmem
      refine ⟨by omega, ?_⟩
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_idxOf htmem, Option.getD_some]
    refine ⟨hindex, ?_, horder, ?_⟩
    · intro i hi
      rw [hvals i hi]
      exact (select_sublist U (scan ∅ z) z).subset (by rw [hq]; exact List.getElem_mem _)
    · intro a b ha hb hab
      obtain ⟨hia, hva⟩ := hindex a ha; obtain ⟨hib, hvb⟩ := hindex b hb
      by_contra hnot
      by_cases he : t.idxOf a = t.idxOf b
      · have heab : a = b := by simpa only [he, hvb] using hva.symm
        subst b; omega
      · have hrev := horder (t.idxOf b) (t.idxOf a) (by omega) hia
        rw [hva, hvb] at hrev; omega
  obtain ⟨hwi, hwm, hwo, hwr⟩ := rankData w p hw hqw hp
  obtain ⟨hvi, hvm, hvo, hvr⟩ := rankData v r hv hqv hr
  have hlow := incBlocks_avoids n ks hpos hsum; have hhigh := hookBlocks_avoids n ks.reverse
    (by intro k hk; exact hpos k (by simpa using hk)) (by simpa using hsum)
  have triple (t : List ℕ) (ht : t.length = n) (a b c ia ib ic : ℕ)
      (hia : ia < n) (hib : ib < n) (hic : ic < n)
      (hab : ia < ib) (hbc : ib < ic)
      (hva : t[ia]! = a) (hvb : t[ib]! = b) (hvc : t[ic]! = c) : [a, b, c].Sublist t := by
    let e : Fin 3 ↪o Fin t.length := OrderEmbedding.ofMapLEIff
      (fun q => if q.val = 0 then ⟨ia, by omega⟩ else
        if q.val = 1 then ⟨ib, by omega⟩ else ⟨ic, by omega⟩)
      (by intro q t; fin_cases q <;> fin_cases t <;> simp <;> omega)
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨e, ?_⟩; intro q
    have hget (j : ℕ) (hj : j < t.length) : t[j]! = t[j] := by
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    simp only [hget ia (by omega)] at hva; simp only [hget ib (by omega)] at hvb
    simp only [hget ic (by omega)] at hvc
    fin_cases q <;> simp [e, hva, hvb, hvc]
  have firstTriple (word queue : List ℕ) (length_eq : queue.length = n)
      (indices : ∀ a ∈ word, queue.idxOf a < n ∧ queue[queue.idxOf a]! = a)
      (orders : ∀ a b, a ∈ word → b ∈ word →
        word.idxOf a < word.idxOf b → queue.idxOf a < queue.idxOf b)
      (a b c : ℕ) (ha : a ∈ word) (hb : b ∈ word) (hc : c ∈ word)
      (firstAB : word.idxOf a < word.idxOf b) (firstBC : word.idxOf b < word.idxOf c) :
      a ∈ queue ∧ b ∈ queue ∧ c ∈ queue ∧ [a, b, c].Sublist queue := by
    obtain ⟨hia, hva⟩ := indices a ha
    obtain ⟨hib, hvb⟩ := indices b hb
    obtain ⟨hic, hvc⟩ := indices c hc
    refine ⟨member queue a (queue.idxOf a) (by omega) hva,
      member queue b (queue.idxOf b) (by omega) hvb,
      member queue c (queue.idxOf c) (by omega) hvc, ?_⟩
    exact triple queue length_eq a b c (queue.idxOf a) (queue.idxOf b) (queue.idxOf c)
      hia hib hic (orders a b ha hb firstAB) (orders b c hb hc firstBC) hva hvb hvc
  have hlf : ∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
      ¬ (w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b) ∧
      ¬ (w.idxOf b < w.idxOf a ∧ w.idxOf a < w.idxOf c) := by
    intro a b c ha hb hc hab hbc
    constructor
    · rintro ⟨firstFM, firstML⟩
      obtain ⟨hma, hmc, hmb, sublist⟩ :=
        firstTriple w p hp hwi hwr
          a c b ha hc hb firstFM firstML
      apply hlow.1
      exact (occursTriple p [1, 3, 2] (by decide) (by decide)).mpr
        ⟨a, b, c, hab, hbc, hma, hmb, hmc, by simpa using sublist⟩
    · rintro ⟨firstFM, firstML⟩
      obtain ⟨hmb, hma, hmc, sublist⟩ :=
        firstTriple w p hp hwi hwr
          b a c hb ha hc firstFM firstML
      apply hlow.2
      exact (occursTriple p [2, 1, 3] (by decide) (by decide)).mpr
        ⟨a, b, c, hab, hbc, hma, hmb, hmc, by simpa using sublist⟩
  have hfirstHigh : ∀ a b c : ℕ, a ∈ v → b ∈ v → c ∈ v → a < b → b < c →
      ¬ (v.idxOf a < v.idxOf b ∧ v.idxOf b < v.idxOf c) ∧
      ¬ (v.idxOf a < v.idxOf c ∧ v.idxOf c < v.idxOf b) := by
    intro a b c ha hb hc hab hbc
    constructor
    · rintro ⟨firstFM, firstML⟩
      obtain ⟨hma, hmb, hmc, sublist⟩ :=
        firstTriple v r hr hvi hvr
          a b c ha hb hc firstFM firstML
      apply hhigh.1
      exact (occursTriple r [1, 2, 3] (by decide) (by decide)).mpr
        ⟨a, b, c, hab, hbc, hma, hmb, hmc, by simpa using sublist⟩
    · rintro ⟨firstFM, firstML⟩
      obtain ⟨hma, hmc, hmb, sublist⟩ :=
        firstTriple v r hr hvi hvr
          a c b ha hc hb firstFM firstML
      apply hhigh.2
      exact (occursTriple r [1, 3, 2] (by decide) (by decide)).mpr
        ⟨a, b, c, hab, hbc, hma, hmb, hmc, by simpa using sublist⟩
  let F : ℕ → ℕ := fun i => w.idxOf p[i]!; let S : ℕ → ℕ := fun i => secondPos p[i]! w
  let VF : ℕ → ℕ := fun i => v.idxOf r[i]!; let VS : ℕ → ℕ := fun i => secondPos r[i]! v
  have hlowRank : (¬ Occurs [1, 1, 3, 2] w ∧ ¬ Occurs [2, 2, 1, 3] w) ↔
        ¬ ∃ i j k, i < j ∧ j < k ∧ k < n ∧ p[i]! < p[j]! ∧ S i < F k ∧ F k < S j := by
    rw [low_local_test w hw hnw hlf]
    constructor
    · intro htest hcross
      obtain ⟨i, j, k, hij, hjk, hkn, hpij, hsi, hfj⟩ := hcross; have hi : i < n := by omega
      have hj : j < n := (by omega); have hmI := hwm i hi; have hmJ := hwm j hj
      have hmK := hwm k hkn; have hfoI := hwo i j hij hj; have hfoJ := hwo j k hjk hkn
      have hneI : p[k]! ≠ p[i]! := (by intro he; rw [he] at hfoJ; omega)
      have hneJ : p[k]! ≠ p[j]! := (by intro he; rw [he] at hfoJ; omega)
      by_cases hbig : p[j]! < p[k]!
      · exact (htest p[i]! p[j]! p[k]! hmI hmJ hmK hpij hbig).1
          ⟨hfoI, hfoJ, hsi, hfj⟩
      · by_cases hsmall : p[k]! < p[i]!
        · exact (htest p[k]! p[i]! p[j]! hmK hmI hmJ hsmall hpij).2
            ⟨hfoI, hfoJ, hsi, hfj⟩
        · exact (hlf p[i]! p[k]! p[j]! hmI hmK hmJ (by omega) (by omega)).1
            ⟨hfoI, hfoJ⟩
    · intro hcross a b c ha hb hc hab hbc
      constructor
      · rintro ⟨hafb, hbfc, hsafc, hfcsb⟩
        obtain ⟨hia, hva⟩ := hwi a ha; obtain ⟨hib, hvb⟩ := hwi b hb
        obtain ⟨hic, hvc⟩ := hwi c hc
        apply hcross
        refine ⟨p.idxOf a, p.idxOf b, p.idxOf c,
          hwr a b ha hb hafb, hwr b c hb hc hbfc, hic, ?_, ?_, ?_⟩
        · simpa only [hva, hvb] using hab
        · simpa only [S, F, hva, hvc] using hsafc
        · simpa only [S, F, hvb, hvc] using hfcsb
      · rintro ⟨hbfc, hfca, hsbfa, hfasC⟩
        obtain ⟨hia, hva⟩ := hwi a ha; obtain ⟨hib, hvb⟩ := hwi b hb
        obtain ⟨hic, hvc⟩ := hwi c hc
        apply hcross
        refine ⟨p.idxOf b, p.idxOf c, p.idxOf a,
          hwr b c hb hc hbfc, hwr c a hc ha hfca, hia, ?_, ?_, ?_⟩
        · simpa only [hvb, hvc] using hbc
        · simpa only [S, F, hvb, hva] using hsbfa
        · simpa only [S, F, hvc, hva] using hfasC
  have hhighRank : (¬ Occurs [1, 2, 3, 3] v ∧ ¬ Occurs [1, 3, 2, 2] v) ↔
        ¬ ∃ i j k, i < j ∧ j < k ∧ k < n ∧ r[j]! < r[i]! ∧ r[j]! < r[k]! ∧
          VF j < VS i ∧ VS i < VF k := by
    rw [high_local_test v hv hnv hfirstHigh]
    constructor
    · intro htest hcross
      obtain ⟨i, j, k, hij, hjk, hkn, hpji, hpjk, hfj, hsk⟩ := hcross
      have hmI := hvm i (by omega); have hmJ := hvm j (by omega); have hmK := hvm k hkn
      have hfoI := hvo i j hij (by omega); have hfoJ := hvo j k hjk hkn
      have hne : r[i]! ≠ r[k]! := (by intro he; rw [he] at hfoI; omega)
      by_cases hik : r[i]! < r[k]!
      · exact (htest r[j]! r[i]! r[k]! hmJ hmI hmK hpji hik).1
          ⟨hfoI, hfoJ, hfj, hsk⟩
      · exact (htest r[j]! r[k]! r[i]! hmJ hmK hmI hpjk (by omega)).2
          ⟨hfoI, hfoJ, hfj, hsk⟩
    · intro hcross a b c ha hb hc hab hbc
      constructor
      · rintro ⟨hbfa, hafc, hfasb, hsbfc⟩
        obtain ⟨hia, hva⟩ := hvi a ha; obtain ⟨hib, hvb⟩ := hvi b hb
        obtain ⟨hic, hvc⟩ := hvi c hc
        apply hcross
        refine ⟨r.idxOf b, r.idxOf a, r.idxOf c,
          hvr b a hb ha hbfa, hvr a c ha hc hafc, hic, ?_, ?_, ?_, ?_⟩
        · simpa only [hva, hvb] using hab
        · simpa only [hva, hvc] using hab.trans hbc
        · simpa only [VF, VS, hva, hvb] using hfasb
        · simpa only [VF, VS, hvb, hvc] using hsbfc
      · rintro ⟨hcfa, hafb, hfasc, hscfb⟩
        obtain ⟨hia, hva⟩ := hvi a ha; obtain ⟨hib, hvb⟩ := hvi b hb
        obtain ⟨hic, hvc⟩ := hvi c hc
        apply hcross
        refine ⟨r.idxOf c, r.idxOf a, r.idxOf b,
          hvr c a hc ha hcfa, hvr a b ha hb hafb, hib, ?_, ?_, ?_, ?_⟩
        · simpa only [hva, hvc] using hab.trans hbc
        · simpa only [hva, hvb] using hab
        · simpa only [VF, VS, hva, hvc] using hfasc
        · simpa only [VF, VS, hvc, hvb] using hscfb
  have hS (i j : ℕ) (hij : i < j) (hj : j < n) : S i < S j :=
    (nonnesting_iff_equal_orders w hw).mp hnw p[i]! (hwm i (by omega))
      p[j]! (hwm j hj) (hwo i j hij hj)
  have hb := block_crossing_transfer n ks hpos hsum F S hS
  have hrev (i : ℕ) (hi : i < n) : r.reverse[i]! = r[n - 1 - i]! := by
    simp only [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa [hr] using hi : i < r.reverse.length),
      List.getElem_reverse, hr, Option.getD_some,
      List.getElem?_eq_getElem (by omega : n - 1 - i < r.length)]
  have href : (∃ i j k, i < j ∧ j < k ∧ k < n ∧ r.reverse[j]! < r.reverse[i]! ∧
        r.reverse[j]! < r.reverse[k]! ∧ S i < F k ∧ F k < S j) ↔
      (∃ i j k, i < j ∧ j < k ∧ k < n ∧ r[j]! < r[i]! ∧ r[j]! < r[k]! ∧
        VF j < VS i ∧ VS i < VF k) := by
    constructor
    · rintro ⟨i, j, k, hij, hjk, hkn, hqji, hqjk, hsi, hfj⟩
      rw [hrev j (by omega), hrev i (by omega)] at hqji; rw [hrev j (by omega), hrev k hkn] at hqjk
      have hFj := hfv j (by omega); have hFi := hfv i (by omega); have hSk := hsv k hkn
      change VF (n - 1 - j) + S j + 1 = w.length at hFj
      change VF (n - 1 - i) + S i + 1 = w.length at hFi
      change VS (n - 1 - k) + F k + 1 = w.length at hSk
      exact ⟨n - 1 - k, n - 1 - j, n - 1 - i, by omega, by omega,
        by omega, hqjk, hqji, by omega, by omega⟩
    · rintro ⟨i, j, k, hij, hjk, hkn, hpji, hpjk, hfj, hsk⟩
      have hi : i < n := (by omega); have hj : j < n := (by omega)
      have he (a : ℕ) (ha : a < n) : n - 1 - (n - 1 - a) = a := (by omega)
      have hFj := hfv (n - 1 - j) (by omega); have hFk := hfv (n - 1 - k) (by omega)
      have hSi := hsv (n - 1 - i) (by omega)
      rw [he j hj] at hFj; rw [he k hkn] at hFk; rw [he i hi] at hSi
      change VF j + S (n - 1 - j) + 1 = w.length at hFj
      change VF k + S (n - 1 - k) + 1 = w.length at hFk
      change VS i + F (n - 1 - i) + 1 = w.length at hSi
      refine ⟨n - 1 - k, n - 1 - j, n - 1 - i, by omega, by omega, by omega,
        ?_, ?_, by omega, by omega⟩
      · rw [hrev (n - 1 - j) (by omega), hrev (n - 1 - k) (by omega), he j hj, he k hkn];
          exact hpjk
      · rw [hrev (n - 1 - j) (by omega), hrev (n - 1 - i) (by omega), he j hj, he i hi];
          exact hpji
  exact (hlowRank.trans (not_congr (hb.trans href))).trans hhighRank.symm
end D5.S3.Combinatorics.Nonnesting.NonnestingRoyalAvoidanceTransfer
