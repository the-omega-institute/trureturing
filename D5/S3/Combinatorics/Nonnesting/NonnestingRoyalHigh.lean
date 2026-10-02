/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingRoyalHigh
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingRoyalHigh
   mirror-E: none(waiver:royal-high-block-reflection)
   anchors: []
   utility: none
   digest: Counts high Royal avoiders by the reflected increasing-block bijection. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBijection
import D5.S3.Combinatorics.Nonnesting.NonnestingRoyalAvoidanceTransfer
import D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLow
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncConverse
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHookBlocks
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalShape
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingRoyalHigh

open NonnestingRoyalAvoidanceTransfer

open scoped symmDiff
open DyckStep

open NonnestingBasicRoyalHookBlocks

open NonnestingBasicRoyalIncBlocks

open DyckStep NonnestingBasicRoyalEncoding NonnestingBasicRoyalShape

open DyckStep NonnestingBasicRoyalEncoding

open DyckStep NonnestingBasicOrders NonnestingBasicRoyalEncoding NonnestingBasicRoyalReverse

open DyckStep NonnestingBasicRoyalEncoding NonnestingBasicRoyalShape NonnestingBasicRoyalHookBlocks
  NonnestingBasicRoyalIncBlocks NonnestingBasicOrders  NonnestingDefs
  NonnestingBasicRoyalIncConverse  NonnestingBasicRoyalBijection
  NonnestingRoyalLowGap NonnestingBasicRoyalReverse
local notation "toggle" =>
  (fun (active : Finset ℕ) (letter : ℕ) => active ∆ Singleton.singleton letter)
set_option maxHeartbeats 2000000 in
theorem result : NonnestingDefs.claim1233 := by
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
  have high_local_test (w : List ℕ) (hcount : ∀ x ∈ w, w.count x = 2)
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
      (havoid : ¬ NonnestingDefs.Occurs [1, 2, 3, 3] w ∧
        ¬ NonnestingDefs.Occurs [1, 3, 2, 2] w) :
      ∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
        ¬ (w.idxOf a < w.idxOf b ∧ w.idxOf b < w.idxOf c) ∧
        ¬ (w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b) := by
    intro a b c ha hb hc hab hbc
    have horders := (nonnesting_iff_equal_orders w hcount).mp hnn
    constructor
    · intro order
      apply havoid.1
      apply (occursTriple w [1, 2, 3, 3] (by decide))
      refine ⟨a, b, c, hab, hbc, ha, hb, hc, ?_⟩
      have sublist := (quadruplePositions w a b c c)
        ⟨w.idxOf a, w.idxOf b, w.idxOf c, secondPos c w,
          order.1, order.2, by unfold secondPos; omega,
          List.getElem?_idxOf ha,
          List.getElem?_idxOf hb,
          List.getElem?_idxOf hc,
          secondOccurrence w c (hcount c hc)⟩
      simpa using sublist
    · intro order
      apply havoid.2
      apply (occursTriple w [1, 3, 2, 2] (by decide))
      refine ⟨a, b, c, hab, hbc, ha, hb, hc, ?_⟩
      have sublist := (quadruplePositions w a c b b)
        ⟨w.idxOf a, w.idxOf c, w.idxOf b, secondPos b w,
          order.1, order.2, by unfold secondPos; omega,
          List.getElem?_idxOf ha,
          List.getElem?_idxOf hc,
          List.getElem?_idxOf hb,
          secondOccurrence w b (hcount b hb)⟩
      simpa using sublist
  let exchange : DyckStep → DyckStep | U => D | D => U
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
  have hookBlocks_unique (n : ℕ) (ks ls : List ℕ)
      (hkpos : ∀ k ∈ ks, 0 < k) (hlpos : ∀ l ∈ ls, 0 < l)
      (hksum : ks.sum = n) (hlsum : ls.sum = n)
      (heq : hookBlocks n ks = hookBlocks n ls) : ks = ls := by
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
        have firstMax (j : ℕ) (js : List ℕ) (hj : 0 < j) (hjn : j ≤ n) :
            (hookBlocks n (j :: js)).idxOf n = j - 1 := by
          let pre := List.ofFn (fun i : Fin (j - 1) => n - i.val - 1)
          have hnot : n ∉ pre := by
            intro hnpre
            obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnpre
            have : i.val < j - 1 := i.isLt; omega
          simp [hookBlocks, List.idxOf_append, pre, hnot]
        have hksum' : ks.sum = n - k := by
          simp only [List.sum_cons] at hksum; omega
        have hlsum' : ls.sum = n - l := by
          simp only [List.sum_cons] at hlsum; omega
        have hkpos' : ∀ x ∈ ks, 0 < x := by
          intro x hx; exact hkpos x (by simp [hx])
        have hlpos' : ∀ x ∈ ls, 0 < x := by
          intro x hx; exact hlpos x (by simp [hx])
        have hkl : k = l := by
          have hidx := congrArg (List.idxOf n) heq
          rw [firstMax k ks hk hkn, firstMax l ls hl hln] at hidx; omega
        subst l
        have htail : hookBlocks (n - k) ks = hookBlocks (n - k) ls := by
          have h := heq; simp only [hookBlocks] at h; exact List.append_cancel_left h
        exact congrArg (k :: ·)
          (ih (n - k) ls hkpos' hlpos' hksum' (by simpa using hlsum') htail)
  have incBlocks_unique (n : ℕ) (ks ls : List ℕ) (hkpos : ∀ k ∈ ks, 0 < k) (hlpos : ∀ l ∈ ls, 0 < l)
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
  have weave_exists_of_counts (p q : List ℕ) (d : List DyckStep)
      (hp : p.length = d.count U) (hq : q.length = d.count D) : ∃ w, weave p q d = some w := by
    induction d generalizing p q with
    | nil =>
      have hp0 : p = [] := List.eq_nil_of_length_eq_zero (by simpa using hp)
      have hq0 : q = [] := List.eq_nil_of_length_eq_zero (by simpa using hq)
      subst p; subst q; exact ⟨[], rfl⟩
    | cons s d ih =>
      cases s with
      | U =>
        cases p with
        | nil => simp at hp
        | cons a p =>
          have hp' : p.length = d.count U := (by simpa using hp)
          have hq' : q.length = d.count D := (by simpa using hq)
          obtain ⟨w, hw⟩ := ih p q hp' hq'
          exact ⟨a :: w, by simp [weave, hw]⟩
      | D =>
        cases q with
        | nil => simp at hq
        | cons a q =>
          have hp' : p.length = d.count U := (by simpa using hp)
          have hq' : q.length = d.count D := (by simpa using hq)
          obtain ⟨w, hw⟩ := ih p q hp' hq'
          exact ⟨a :: w, by simp [weave, hw]⟩
  have weave_perm (p q : List ℕ) (d : List DyckStep) (w : List ℕ)
      (hw : weave p q d = some w) : w.Perm (p ++ q) := by
    induction d generalizing p q w with
    | nil =>
      cases p with
      | nil =>
        cases q with
        | nil => simpa [weave] using hw.symm
        | cons a q => simp [weave] at hw
      | cons a p => simp [weave] at hw
    | cons s d ih =>
      cases s with
      | U =>
        cases p with
        | nil => simp [weave] at hw
        | cons a p =>
          cases h : weave p q d with
          | none => simp [weave, h] at hw
          | some v =>
            have heq : w = a :: v := (by simpa [weave, h] using hw.symm); subst w
            simpa using (ih p q v h).cons a
      | D =>
        cases q with
        | nil => simp [weave] at hw
        | cons a q =>
          cases h : weave p q d with
          | none => simp [weave, h] at hw
          | some v =>
            have heq : w = a :: v := (by simpa [weave, h] using hw.symm)
            subst w; exact ((ih p q v h).cons a).trans (List.perm_middle.symm)
  have weave_reversal (p q : List ℕ) (steps : List DyckStep) (w : List ℕ)
      (hw : weave p q steps = some w) :
      weave q.reverse p.reverse (steps.reverse.map exchange) = some w.reverse := by
    have hsnoc : ∀ (steps : List DyckStep) (p q w : List ℕ) (a : ℕ), weave p q steps = some w →
        weave (p ++ [a]) q (steps ++ [U]) = some (w ++ [a]) ∧
        weave p (q ++ [a]) (steps ++ [D]) = some (w ++ [a]) := by
      intro steps
      induction steps with
      | nil =>
        intro p q w a h
        cases p with
        | nil =>
          cases q with
          | nil =>
            have hw : w = [] := (by simpa [weave] using h.symm); subst w; exact ⟨rfl, rfl⟩
          | cons b q => simp [weave] at h
        | cons b p => simp [weave] at h
      | cons step steps ih =>
        intro p q w a h
        cases step with
        | U =>
          cases p with
          | nil => simp [weave] at h
          | cons b p =>
            cases ht : weave p q steps with
            | none => simp [weave, ht] at h
            | some v =>
              have hw : w = b :: v := (by simpa [weave, ht] using h.symm); subst w
              obtain ⟨hu, hd⟩ := ih p q v a ht
              constructor <;> simp [weave, hu, hd]
        | D =>
          cases q with
          | nil => simp [weave] at h
          | cons b q =>
            cases ht : weave p q steps with
            | none => simp [weave, ht] at h
            | some v =>
              have hw : w = b :: v := (by simpa [weave, ht] using h.symm); subst w
              obtain ⟨hu, hd⟩ := ih p q v a ht
              constructor <;> simp [weave, hu, hd]
    induction steps generalizing p q w with
    | nil =>
      cases p with
      | nil =>
        cases q with
        | nil =>
          have hw : w = [] := (by simpa [weave] using hw.symm); subst w; rfl
        | cons a q => simp [weave] at hw
      | cons a p => simp [weave] at hw
    | cons step steps ih =>
      cases step with
      | U =>
        cases p with
        | nil => simp [weave] at hw
        | cons a p =>
          cases ht : weave p q steps with
          | none => simp [weave, ht] at hw
          | some v =>
            have hw : w = a :: v := (by simpa [weave, ht] using hw.symm)
            subst w; have hrev := ih p q v ht; simpa [List.reverse_cons, exchange] using
              (hsnoc (steps.reverse.map exchange) q.reverse p.reverse v.reverse a hrev).2
      | D =>
        cases q with
        | nil => simp [weave] at hw
        | cons a q =>
          cases ht : weave p q steps with
          | none => simp [weave, ht] at hw
          | some v =>
            have hw : w = a :: v := (by simpa [weave, ht] using hw.symm)
            subst w; have hrev := ih p q v ht; simpa [List.reverse_cons, exchange] using
              (hsnoc (steps.reverse.map exchange) q.reverse p.reverse v.reverse a hrev).1
  have reflected_encode_positions (p q : List ℕ) (d : DyckWord)
      (hp : p.Nodup) (hq : q.Nodup) (hlen : p.length = d.semilength)
      (helen : q.length = (reflection d).semilength) (hsize : p.length = q.length)
      (i : ℕ) (hi : i < p.length) : let w := (weave p p d.toList).getD []
      let v := (weave q q (reflection d).toList).getD []
      v.idxOf q[p.length - 1 - i]! + secondPos p[i]! w + 1 = w.length ∧
        secondPos q[p.length - 1 - i]! v + w.idxOf p[i]! + 1 = w.length := by
    let f : ℕ → ℕ := fun a => q[p.length - 1 - p.idxOf a]!
    have value (l : List ℕ) (j : ℕ) (hj : j < l.length) : l[j]! = l[j] := by
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hmap : p.reverse.map f = q := by
      apply List.ext_getElem
      · simp [hsize]
      · intro j hj hqj
        have hjp : j < p.length := (by simpa using hj)
        have hjr : p.length - 1 - j < p.length := (by omega)
        simp only [List.getElem_map, List.getElem_reverse, f]; rw [hp.idxOf_getElem _ hjr]
        have he : p.length - 1 - (p.length - 1 - j) = j := (by omega); rw [he, value q j hqj]
    have hinj : ∀ a ∈ p, ∀ b ∈ p, f a = f b → a = b := by
      intro a ha b hb he
      have hia := List.idxOf_lt_length_of_mem ha; have hib := List.idxOf_lt_length_of_mem hb
      have hqa : p.length - 1 - p.idxOf a < q.length := (by omega)
      have hqb : p.length - 1 - p.idxOf b < q.length := (by omega)
      simp only [f, value q _ hqa, value q _ hqb] at he
      have heidx := (hq.getElem_inj_iff (hi := hqa) (hj := hqb)).mp he
      have heab : p.idxOf a = p.idxOf b := (by omega); exact (List.idxOf_inj ha).mp heab
    have weaveMap : ∀ (steps : List DyckStep) (a b w : List ℕ), weave a b steps = some w →
          weave (a.map f) (b.map f) steps = some (w.map f) := by
      intro steps
      induction steps with
      | nil => intro a b w h; cases a <;> cases b <;> simp [weave] at h ⊢; simp [← h]
      | cons t steps ih =>
        intro a b w h
        cases t with
        | U =>
          cases a with
          | nil => simp [weave] at h
          | cons c a =>
            cases ht : weave a b steps with
            | none => simp [weave, ht] at h
            | some z =>
              have he : w = c :: z := (by simpa [weave, ht] using h.symm)
              subst w; simp [weave, ih a b z ht]
        | D =>
          cases b with
          | nil => simp [weave] at h
          | cons c b =>
            cases ht : weave a b steps with
            | none => simp [weave, ht] at h
            | some z =>
              have he : w = c :: z := (by simpa [weave, ht] using h.symm)
              subst w; simp [weave, ih a b z ht]
    let w := (weave p p d.toList).getD []; let v := (weave q q (reflection d).toList).getD []
    have hc : p.length = d.toList.count U := (by simpa [DyckWord.semilength] using hlen)
    obtain ⟨z, hz⟩ := weave_exists_of_counts p p d.toList hc
      (hc.trans d.count_U_eq_count_D)
    have hw : weave p p d.toList = some w := (by simp [w, hz])
    have hr := weave_reversal p p d.toList w hw; have hm := weaveMap _ _ _ _ hr; rw [hmap] at hm
    have hv : v = w.reverse.map f := by
      change (weave q q (reflection d).toList).getD [] = _
      change (weave q q (d.toList.reverse.map exchange)).getD [] = _; rw [hm]; rfl
    have hperm := weave_perm p p d.toList w hw
    have hsupport : ∀ a ∈ w, a ∈ p := by
      intro a ha; simpa using hperm.subset ha
    let a := p[i]!
    have hap : a ∈ p := (by change p[i]! ∈ p; rw [value p i hi]; exact List.getElem_mem hi)
    have hca : w.count a = 2 := by
      have he := hperm.count_eq a; have hcnt : p.count a = 1 := List.count_eq_one_of_mem hp hap
      simpa [List.count_append, hcnt] using he
    obtain ⟨u, b, z, hau, hab, haz, hwform⟩ := count_two_decomposition a w hca
    have hfirst : w.idxOf a = u.length := (by rw [hwform]; simp [List.idxOf_append, hau])
    have hsecond : secondPos a w = u.length + 1 + b.length := by
      rw [hwform]
      have hd : u.drop (u.length + 1) = [] := (by apply List.drop_eq_nil_iff.mpr; omega)
      simp [secondPos, List.idxOf_append, hau, hab, List.drop_append, hd]
    have hnot (t : List ℕ) (ht : t.Sublist w) (hat : a ∉ t) : f a ∉ t.map f := by
      intro he
      obtain ⟨c, hc, hfc⟩ := List.mem_map.mp he; have hcap : c ∈ p := hsupport c (ht.subset hc)
      have hce : c = a := hinj c hcap a hap hfc; exact hat (hce ▸ hc)
    have hu : u.Sublist w := by
      rw [hwform]
      exact ((List.sublist_append_left u [a]).trans (List.sublist_append_left _ b)).trans
          ((List.sublist_append_left _ [a]).trans (List.sublist_append_left _ z))
    have hb : b.Sublist w := by
      rw [hwform]; exact (List.sublist_append_right (u ++ [a]) b).trans
        ((List.sublist_append_left _ [a]).trans (List.sublist_append_left _ z))
    have hzsub : z.Sublist w := (by rw [hwform]; exact List.sublist_append_right _ _)
    have hun := hnot u hu hau; have hbn := hnot b hb hab; have hzn := hnot z hzsub haz
    have hvform : v = z.reverse.map f ++ [f a] ++ b.reverse.map f ++ [f a] ++ u.reverse.map f := by
      rw [hv, hwform]
      simp only [List.reverse_append, List.reverse_singleton, List.map_append,
        List.map_singleton, List.append_assoc]
    have hvfirst : v.idxOf (f a) = z.length := by
      rw [hvform]
      have hnr : f a ∉ z.reverse.map f := (by simpa [List.map_reverse] using hzn)
      simp only [List.idxOf_append, hnr, if_false, List.idxOf_cons_self,
        List.length_reverse, List.length_map, Nat.zero_add, List.mem_append,
        List.mem_singleton, or_true, true_or, if_true]
    have hvsecond : secondPos (f a) v = z.length + 1 + b.length := by
      unfold secondPos; rw [hvfirst]; rw [hvform]
      have hnr : f a ∉ z.reverse.map f := (by simpa [List.map_reverse] using hzn)
      have hbr : f a ∉ b.reverse.map f := (by simpa [List.map_reverse] using hbn)
      have hd : (z.reverse.map f).drop (z.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr; simp only [List.length_map, List.length_reverse]; omega
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.drop_append]
      simp only [hd, List.nil_append, List.length_map, List.length_reverse,
        Nat.add_sub_cancel_left, List.singleton_append, List.drop_succ_cons, List.drop_zero]
      rw [List.idxOf_append]
      simp only [hbr, if_false, List.idxOf_cons_self,
        List.length_reverse, List.length_map, Nat.zero_add]
    have hfai : f a = q[p.length - 1 - i]! := by
      change f p[i]! = _; rw [value p i hi]; simp only [f, hp.idxOf_getElem i hi]
    have hwlen : w.length = u.length + b.length + z.length + 2 := by
      rw [hwform]; simp only [List.length_append, List.length_singleton]; omega
    change v.idxOf _ + secondPos a w + 1 = w.length ∧ secondPos _ v + w.idxOf a + 1 = w.length
    rw [← hfai, hvfirst, hvsecond, hfirst, hsecond]
    constructor <;> omega
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
  have hookBlocks_perm (m : ℕ) (ks : List ℕ) (hp : ∀ k ∈ ks, 0 < k) (hs : ks.sum = m) :
      (hookBlocks m ks).Perm (List.range' 1 m) := by
    induction ks generalizing m with
    | nil =>
      have hm : m = 0 := (by simpa using hs.symm); simp [hookBlocks, hm]
    | cons k ks ih =>
      have hk : 0 < k := hp k (by simp)
      have hkm : k ≤ m := (by simp only [List.sum_cons] at hs; omega)
      have hs' : ks.sum = m - k := (by simp only [List.sum_cons] at hs; omega)
      have hp' : ∀ a ∈ ks, 0 < a := (by intro a ha; exact hp a (by simp [ha]))
      have htail := ih (m - k) hp' hs'
      have hpre : List.ofFn (fun i : Fin (k - 1) => m - i.val - 1) =
          (List.range' (m - k + 1) (k - 1)).reverse := by
        apply List.ext_getElem
        · simp
        · intro i hi hj
          simp only [List.getElem_ofFn, List.getElem_reverse, List.length_range',
            List.getElem_range']
          have hib : i < k - 1 := (by simpa using hi); omega
      have hblock : (List.ofFn (fun i : Fin (k - 1) => m - i.val - 1) ++ [m]).Perm
            (List.range' (m - k + 1) k) := by
        rw [hpre]
        have hsplit : List.range' (m - k + 1) k = List.range' (m - k + 1) (k - 1) ++ [m] := by
          have he := List.range'_append (s := m - k + 1)
            (m := k - 1) (n := 1) (step := 1)
          have hlast : m - k + 1 + (k - 1) = m := (by omega)
          simpa [hlast, Nat.sub_add_cancel hk] using he.symm
        rw [hsplit]; exact (List.reverse_perm _).append_right _
      have hrange : List.range' 1 m = List.range' 1 (m - k) ++ List.range' (m - k + 1) k := by
        have hm : m - k + k = m := (by omega); simpa [hm, Nat.add_comm] using
          (List.range'_append (s := 1) (m := m - k) (n := k) (step := 1)).symm
      change ((List.ofFn (fun i : Fin (k - 1) => m - i.val - 1) ++ [m]) ++
        hookBlocks (m - k) ks).Perm _
      rw [hrange]; exact (hblock.append htail).trans List.perm_append_comm
  have incBlocks_perm (n : ℕ) (ks : List ℕ) (hpos : ∀ k ∈ ks, 0 < k) (hsum : ks.sum = n) :
      (incBlocks n ks).Perm (List.range' 1 n) := by
    induction ks generalizing n with
    | nil =>
      have hn : n = 0 := (by simpa using hsum.symm); simp [incBlocks, hn]
    | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have hpos' : ∀ x ∈ ks, 0 < x := (by intro x hx; exact hpos x (by simp [hx]))
      have hsum' : ks.sum = n - k := (by simp only [List.sum_cons] at hsum; omega)
      have hkn : k ≤ n := (by simp only [List.sum_cons] at hsum; omega)
      have htail := ih (n - k) hpos' hsum'
      have hrange : List.range' 1 n = List.range' 1 (n - k) ++ List.range' (n - k + 1) k := by
        have hn : n - k + k = n := (by omega); simpa [hn, Nat.add_comm] using
          (List.range'_append (s := 1) (m := n - k) (n := k) (step := 1)).symm
      change (List.range' (n - k + 1) k ++ incBlocks (n - k) ks).Perm
        (List.range' 1 n)
      refine (htail.append_left _).trans ?_
      rw [hrange]; exact List.perm_append_comm
  have toggle_eq (active : Finset ℕ) (letter : ℕ) : toggle active letter =
        if letter ∈ active then active.erase letter else insert letter active := by
    ext value
    by_cases present : letter ∈ active <;>
      by_cases same : value = letter <;>
      simp [Finset.mem_symmDiff, present, same]
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
  have encode_data (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n))
      (d : DyckWord) (hlen : p.length = d.semilength) : let w := (weave p p d.toList).getD []
      ∃ hw : w.Perm ((List.range' 1 n).flatMap fun a => [a, a]),
        (¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧ ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) ∧
        shape (List.range' 1 n) w hw = d ∧ select U (scan ∅ w) w = p := by
    let parameter : royalPairs n := ⟨(p, d), hp, hlen⟩; let word := royalEncoding n parameter
    have inverse := (royalEncoding n).symm_apply_apply parameter
    have path := congrArg (fun pair : royalPairs n => pair.1.2) inverse
    have queue := congrArg (fun pair : royalPairs n => pair.1.1) inverse
    change shape (List.range' 1 n) ((weave p p d.toList).getD []) word.2.1 = d at path
    change select U (scan ∅ ((weave p p d.toList).getD []))
      ((weave p p d.toList).getD []) = p at queue
    exact ⟨word.2.1, ⟨word.2.2.1, word.2.2.2.1⟩, path, queue⟩
  have low_first_order_avoids (d : DyckWord) (w p : List ℕ) (hscan : scan ∅ w = d.toList)
      (hcount : ∀ a ∈ w, w.count a = 2)
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧ ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
      (havoid : ¬ NonnestingDefs.Occurs [1, 1, 3, 2] w ∧ ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w)
      (hU : select U d.toList w = p) : ¬ NonnestingDefs.Occurs [1, 3, 2] p ∧
      ¬ NonnestingDefs.Occurs [2, 1, 3] p := by
    have htest := low_local_test w hcount hnn havoid
    have hpair := queue_pairwise_position U w hcount; rw [hscan, hU] at hpair
    have hfirst_sublist (a b c : ℕ) (hsub : List.Sublist [a, b, c] p) :
        w.idxOf a < w.idxOf b ∧ w.idxOf b < w.idxOf c := by
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
      have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
      have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
      have hvi : p[i] = a := (by simpa [i] using (hf (0 : Fin 3)).symm)
      have hvj : p[j] = b := (by simpa [j] using (hf (1 : Fin 3)).symm)
      have hvk : p[k] = c := (by simpa [k] using (hf (2 : Fin 3)).symm)
      have hab := (List.pairwise_iff_getElem.mp hpair) i j
        (f 0).isLt (f 1).isLt hij
      have hbc := (List.pairwise_iff_getElem.mp hpair) j k
        (f 1).isLt (f 2).isLt hjk
      constructor
      · simpa [hvi, hvj] using hab
      · simpa [hvj, hvk] using hbc
    have hmem_sublist (a b c : ℕ) (hsub : List.Sublist [a, b, c] p) : a ∈ w ∧ b ∈ w ∧ c ∈ w := by
      have hsubw : List.Sublist [a, b, c] w :=
        hsub.trans (by rw [← hU]; exact select_sublist U d.toList w)
      exact ⟨hsubw.subset (by simp), hsubw.subset (by simp), hsubw.subset (by simp)⟩
    have h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p := by
      rintro ⟨x, hxlt, _, hsub, _⟩
      change List.Sublist [x 1, x 3, x 2] p at hsub; have hm := hmem_sublist (x 1) (x 3) (x 2) hsub
      have horder := hfirst_sublist (x 1) (x 3) (x 2) hsub
      have h12 : x 1 < x 2 := hxlt 1 (by omega) (by decide)
      have h23 : x 2 < x 3 := hxlt 2 (by omega) (by decide)
      exact (htest (x 1) (x 2) (x 3) hm.1 hm.2.2 hm.2.1 h12 h23).1 ⟨horder.1, horder.2⟩
    have h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p := by
      rintro ⟨x, hxlt, _, hsub, _⟩
      change List.Sublist [x 2, x 1, x 3] p at hsub; have hm := hmem_sublist (x 2) (x 1) (x 3) hsub
      have horder := hfirst_sublist (x 2) (x 1) (x 3) hsub
      have h12 : x 1 < x 2 := hxlt 1 (by omega) (by decide)
      have h23 : x 2 < x 3 := hxlt 2 (by omega) (by decide)
      exact (htest (x 1) (x 2) (x 3) hm.2.1 hm.1 hm.2.2 h12 h23).2 ⟨horder.1, horder.2⟩
    exact ⟨h132, h213⟩
  have counts (n : ℕ) : (avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]).ncard =
        (avoiders n [[1, 2, 3, 3], [1, 3, 2, 2]]).ncard := by
    let C := {ks : List ℕ // (∀ k ∈ ks, 0 < k) ∧ ks.sum = n}
    let D := {d : DyckWord // d.semilength = n}; let E := C × D
    let B := {w : List ℕ // w ∈ avoiders n []}
    let L := {w : List ℕ // w ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]}
    let H := {w : List ℕ // w ∈ avoiders n [[1, 2, 3, 3], [1, 3, 2, 2]]}
    have hreflect (d : DyckWord) : (reflection d).semilength = d.semilength := by
      have hl : (reflection d).toList.length = d.toList.length := by
        change (d.toList.reverse.map exchange).length = d.toList.length; simp
      have h1 := (reflection d).two_mul_semilength_eq_length
      have h2 := d.two_mul_semilength_eq_length; omega
    let lp (cd : E) : royalPairs n := by
      have hp := incBlocks_perm n cd.1.1 cd.1.2.1 cd.1.2.2
      exact ⟨(incBlocks n cd.1.1, cd.2.1), hp, by
        simpa [cd.2.2] using hp.length_eq⟩
    let rp (cd : E) : royalPairs n := by
      have hp := hookBlocks_perm n cd.1.1.reverse
        (by intro k hk; exact cd.1.2.1 k (by simpa using hk))
        (by simpa using cd.1.2.2)
      exact ⟨(hookBlocks n cd.1.1.reverse, reflection cd.2.1), hp, by
        rw [hreflect, cd.2.2]
        simpa using hp.length_eq⟩
    let lw (cd : E) : B := royalEncoding n (lp cd); let rw (cd : E) : B := royalEncoding n (rp cd)
    have hcount (x : B) : ∀ a ∈ x.1, x.1.count a = 2 := by
      intro a ha
      have hsupport : a ∈ List.range' 1 n := by
        have hb := x.2.1.subset ha; simpa using hb
      exact doubled_count n a x.1 x.2.1 hsupport
    have hbaseLow (x : L) : x.1 ∈ avoiders n [] := ⟨x.2.1, x.2.2.1, x.2.2.2.1, by simp⟩
    have hbaseHigh (x : H) : x.1 ∈ avoiders n [] := ⟨x.2.1, x.2.2.1, x.2.2.2.1, by simp⟩
    have hlwinj : Function.Injective lw := by
      intro a b he; have hpair := (royalEncoding n).injective he
      have hfirst : incBlocks n a.1.1 = incBlocks n b.1.1 :=
        congrArg (fun x : royalPairs n => x.1.1) hpair
      have hd : a.2.1 = b.2.1 := congrArg (fun x : royalPairs n => x.1.2) hpair; apply Prod.ext
      · apply Subtype.ext
        exact incBlocks_unique n a.1.1 b.1.1 a.1.2.1 b.1.2.1
          a.1.2.2 b.1.2.2 hfirst
      · exact Subtype.ext hd
    have hrwinj : Function.Injective rw := by
      intro a b he; have hpair := (royalEncoding n).injective he
      have hfirst : hookBlocks n a.1.1.reverse = hookBlocks n b.1.1.reverse :=
        congrArg (fun x : royalPairs n => x.1.1) hpair
      have hd : reflection a.2.1 = reflection b.2.1 :=
        congrArg (fun x : royalPairs n => x.1.2) hpair
      have hrks : a.1.1.reverse = b.1.1.reverse := hookBlocks_unique n _ _
        (by intro k hk; exact a.1.2.1 k (by simpa using hk))
        (by intro k hk; exact b.1.2.1 k (by simpa using hk))
        (by simpa using a.1.2.2) (by simpa using b.1.2.2) hfirst
      apply Prod.ext
      · apply Subtype.ext
        simpa using congrArg List.reverse hrks
      · exact Subtype.ext (reflection.injective hd)
    have htransfer (cd : E) : (lw cd).1 ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]] ↔
          (rw cd).1 ∈ avoiders n [[1, 2, 3, 3], [1, 3, 2, 2]] := by
      let p := (lp cd).1.1; let q := (rp cd).1.1; let d := cd.2.1
      have hpperm : p.Perm (List.range' 1 n) := (lp cd).2.1
      have hqperm : q.Perm (List.range' 1 n) := (rp cd).2.1
      have hpn : p.length = n := (by simpa using hpperm.length_eq)
      have hqn : q.length = n := (by simpa using hqperm.length_eq)
      have hpd : p.length = d.semilength := (lp cd).2.2
      have hqd : q.length = (reflection d).semilength := (rp cd).2.2
      have hpnd : p.Nodup := hpperm.nodup_iff.mpr List.nodup_range'
      have hqnd : q.Nodup := hqperm.nodup_iff.mpr List.nodup_range'
      obtain ⟨_, _, _, hqw⟩ := encode_data n p hpperm d hpd
      obtain ⟨_, _, _, hqv⟩ := encode_data n q hqperm (reflection d) hqd
      have ht := avoidance_transfer n cd.1.1 cd.1.2.1 cd.1.2.2
        (lw cd).1 (rw cd).1 (hcount (lw cd)) (hcount (rw cd))
        ⟨(lw cd).2.2.1, (lw cd).2.2.2.1⟩
        ⟨(rw cd).2.2.1, (rw cd).2.2.2.1⟩ hqw hqv
        (by
          intro i hi; have h := reflected_encode_positions p q d hpnd hqnd hpd hqd
            (by omega) i (by omega)
          have he := h.1
          change ((weave q q (reflection d).toList).getD []).idxOf q[p.length - 1 - i]! +
            secondPos p[i]! ((weave p p d.toList).getD []) + 1 =
            ((weave p p d.toList).getD []).length at he
          rw [hpn] at he
          exact he)
        (by
          intro i hi; have h := reflected_encode_positions p q d hpnd hqnd hpd hqd
            (by omega) i (by omega)
          have he := h.2
          change secondPos q[p.length - 1 - i]! ((weave q q (reflection d).toList).getD []) +
            ((weave p p d.toList).getD []).idxOf p[i]! + 1 =
            ((weave p p d.toList).getD []).length at he
          rw [hpn] at he
          exact he)
      constructor
      · intro h
        have hav : ¬ Occurs [1, 1, 3, 2] (lw cd).1 ∧ ¬ Occurs [2, 2, 1, 3] (lw cd).1 := by
          constructor <;> apply h.2.2.2 <;> simp
        have hnew := ht.mp hav
        exact ⟨(rw cd).2.1, (rw cd).2.2.1, (rw cd).2.2.2.1, by simpa using hnew⟩
      · intro h
        have hav : ¬ Occurs [1, 2, 3, 3] (rw cd).1 ∧ ¬ Occurs [1, 3, 2, 2] (rw cd).1 := by
          constructor <;> apply h.2.2.2 <;> simp
        have hnew := ht.mpr hav
        exact ⟨(lw cd).2.1, (lw cd).2.2.1, (lw cd).2.2.2.1, by simpa using hnew⟩
    have hlsurj (x : L) : ∃ cd : E, lw cd = (⟨x.1, hbaseLow x⟩ : B) := by
      let b : B := ⟨x.1, hbaseLow x⟩; let pd := (royalEncoding n).symm b
      have hlen : pd.1.1.length = n := (by simpa using pd.2.1.length_eq)
      have hd : pd.1.2.semilength = n := pd.2.2.symm.trans hlen
      have hscan : scan ∅ b.1 = pd.1.2.toList := rfl
      have hqw : select U pd.1.2.toList b.1 = pd.1.1 := rfl
      have havoid : ¬ Occurs [1, 1, 3, 2] b.1 ∧ ¬ Occurs [2, 2, 1, 3] b.1 := by
        constructor <;> apply x.2.2.2.2 <;> simp
      have hfirst := low_first_order_avoids pd.1.2 b.1 pd.1.1 hscan (hcount b)
        ⟨b.2.2.1, b.2.2.2.1⟩ havoid hqw
      obtain ⟨ks, hp, hs, he⟩ := avoids_has_inc_blocks n pd.1.1 pd.2.1 hfirst.1 hfirst.2
      let cd : E := (⟨ks, hp, hs⟩, ⟨pd.1.2, hd⟩)
      refine ⟨cd, ?_⟩
      have hpair : lp cd = pd := by
        apply Subtype.ext; apply Prod.ext
        · exact he.symm
        · rfl
      change royalEncoding n (lp cd) = b; rw [hpair]; exact (royalEncoding n).apply_symm_apply b
    have hrsurj (x : H) : ∃ cd : E, rw cd = (⟨x.1, hbaseHigh x⟩ : B) := by
      let b : B := ⟨x.1, hbaseHigh x⟩; let pd := (royalEncoding n).symm b; let p := pd.1.1
      have hlen : p.length = n := (by simpa [p] using pd.2.1.length_eq)
      have hd : pd.1.2.semilength = n := pd.2.2.symm.trans hlen
      have hqw : select U (scan ∅ b.1) b.1 = p := rfl
      have hpair := queue_pairwise_position U b.1 (hcount b); rw [hqw] at hpair
      have havoid : ¬ Occurs [1, 2, 3, 3] b.1 ∧ ¬ Occurs [1, 3, 2, 2] b.1 := by
        constructor <;> apply x.2.2.2.2 <;> simp
      have htest := high_local_test b.1 (hcount b) ⟨b.2.2.1, b.2.2.2.1⟩ havoid
      have hfirst : ¬ Occurs [1, 2, 3] p ∧ ¬ Occurs [1, 3, 2] p := by
        have triple (a c e : ℕ) (hsub : [a, c, e].Sublist p) :
            b.1.idxOf a < b.1.idxOf c ∧ b.1.idxOf c < b.1.idxOf e := by
          have hab0 : [a, c].Sublist [a, c, e] :=
            List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.nil_sublist _))
          have hab : [a, c].Sublist p := hab0.trans hsub
          have hbc : [c, e].Sublist p := (List.sublist_cons_self _ _).trans hsub
          exact ⟨by simpa only [ite_true] using hpair.forall_sublist hab,
            by simpa only [ite_true] using hpair.forall_sublist hbc⟩
        have mem (a : ℕ) (ha : a ∈ p) : a ∈ b.1 :=
          (select_sublist U (scan ∅ b.1) b.1).subset (by rw [hqw]; exact ha)
        constructor
        · rintro ⟨f, hmono, hmem, hsub, _⟩
          have hsub' : [f 1, f 2, f 3].Sublist p := (by simpa using hsub)
          have hpos := triple _ _ _ hsub'
          exact (htest (f 1) (f 2) (f 3) (mem _ (hmem 1 (by omega) (by simp [letters])))
            (mem _ (hmem 2 (by omega) (by simp [letters])))
            (mem _ (hmem 3 (by omega) (by simp [letters])))
            (hmono 1 (by omega) (by simp [letters]))
            (hmono 2 (by omega) (by simp [letters]))).1 hpos
        · rintro ⟨f, hmono, hmem, hsub, _⟩
          have hsub' : [f 1, f 3, f 2].Sublist p := (by simpa using hsub)
          have hpos := triple _ _ _ hsub'
          exact (htest (f 1) (f 2) (f 3) (mem _ (hmem 1 (by omega) (by simp [letters])))
            (mem _ (hmem 2 (by omega) (by simp [letters])))
            (mem _ (hmem 3 (by omega) (by simp [letters])))
            (hmono 1 (by omega) (by simp [letters]))
            (hmono 2 (by omega) (by simp [letters]))).2 hpos
      obtain ⟨ks, hp, hs, he⟩ := avoids_has_hook_blocks n p pd.2.1 hfirst.1 hfirst.2
      let cd : E := (⟨ks.reverse, by
        constructor
        · intro k hk; exact hp k (by simpa using hk)
        · simpa using hs⟩, ⟨reflection pd.1.2, by rw [hreflect, hd]⟩)
      refine ⟨cd, ?_⟩
      have hpd : rp cd = pd := by
        apply Subtype.ext; apply Prod.ext
        · change hookBlocks n ks.reverse.reverse = p
          rw [List.reverse_reverse]; exact he.symm
        · change reflection (reflection pd.1.2) = pd.1.2
          exact reflection.left_inv _
      change royalEncoding n (rp cd) = b; rw [hpd]; exact (royalEncoding n).apply_symm_apply b
    let P := {cd : E // (lw cd).1 ∈ avoiders n [[1, 1, 3, 2], [2, 2, 1, 3]]}
    let lmap (x : P) : L := ⟨(lw x.1).1, x.2⟩
    let rmap (x : P) : H := ⟨(rw x.1).1, (htransfer x.1).mp x.2⟩
    have hlbij : Function.Bijective lmap := by
      constructor
      · intro a b he
        apply Subtype.ext; apply hlwinj; apply Subtype.ext; exact congrArg (fun x : L => x.1) he
      · intro x
        obtain ⟨cd, he⟩ := hlsurj x; have hv : (lw cd).1 = x.1 := congrArg Subtype.val he
        refine ⟨⟨cd, by rw [hv]; exact x.2⟩, ?_⟩
        exact Subtype.ext hv
    have hrbij : Function.Bijective rmap := by
      constructor
      · intro a b he
        apply Subtype.ext; apply hrwinj; apply Subtype.ext; exact congrArg (fun x : H => x.1) he
      · intro x
        obtain ⟨cd, he⟩ := hrsurj x; have hv : (rw cd).1 = x.1 := congrArg Subtype.val he
        have hprop : (rw cd).1 ∈ avoiders n [[1, 2, 3, 3], [1, 3, 2, 2]] := (by rw [hv]; exact x.2)
        refine ⟨⟨cd, (htransfer cd).mpr hprop⟩, ?_⟩
        exact Subtype.ext hv
    have hcard := Nat.card_congr
      ((Equiv.ofBijective lmap hlbij).symm.trans (Equiv.ofBijective rmap hrbij))
    exact hcard
  have hseries : gf [[1, 1, 3, 2], [2, 2, 1, 3]] = gf [[1, 2, 3, 3], [1, 3, 2, 2]] := by
    apply PowerSeries.ext; intro n; simp only [gf, PowerSeries.coeff_mk, counts n]
  change IsRoyalRoot _; rw [← hseries]; exact NonnestingRoyalLow.result
end D5.S3.Combinatorics.Nonnesting.NonnestingRoyalHigh

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingRoyalHigh.result
