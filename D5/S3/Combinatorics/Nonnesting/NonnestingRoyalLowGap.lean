/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingRoyalLowGap
   mirror-E: none(waiver:royal-low-ascent-gap-obstruction)
   anchors: []
   utility: none
   digest: Shows that a low-row adjacent ascent forces a good Dyck downstep gap. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBijection
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalShape
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowGap

open NonnestingBasicRoyalBlocks

open scoped symmDiff
open DyckStep

open NonnestingBasicRoyalEncoding

open DyckStep NonnestingBasicRoyalEncoding NonnestingBasicRoyalShape NonnestingBasicOrders

open DyckStep NonnestingBasicRoyalEncoding NonnestingBasicRoyalShape

local notation "toggle" =>
  (fun (active : Finset ℕ) (letter : ℕ) => active ∆ Singleton.singleton letter)
theorem ascent_forces_good_gap (d : DyckWord) (w p : List ℕ)
    (hscan : scan ∅ w = d.toList)
    (hcount : ∀ a ∈ w, w.count a = 2)
    (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧ ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
    (havoid : ¬ NonnestingDefs.Occurs [1, 1, 3, 2] w ∧ ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w)
    (hU : select U d.toList w = p) (hD : select D d.toList w = p)
    (hp : p.Nodup)
    (u v z : List DyckStep)
    (hsplit : d.toList = u ++ [D] ++ v ++ [D] ++ z)
    (hnoD : v.count D = 0)
    (ht : u.count D + 1 < p.length)
    (hasc : p[u.count D] < p[u.count D + 1]) : v = [] ∨ (v = [U] ∧ u.count U = u.count D + 1) := by
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
      (¬ NonnestingDefs.Occurs [1, 1, 3, 2] w ∧ ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w) ↔
      ∀ a b c : ℕ, a ∈ w → b ∈ w → c ∈ w → a < b → b < c →
        ¬ (w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b) ∧
        ¬ (w.idxOf b < w.idxOf a ∧ w.idxOf a < w.idxOf c) ∧
        ¬ (w.idxOf a < w.idxOf b ∧ w.idxOf b < w.idxOf c ∧
          secondPos a w < w.idxOf c ∧ w.idxOf c < secondPos b w) ∧
        ¬ (w.idxOf b < w.idxOf c ∧ w.idxOf c < w.idxOf a ∧
          secondPos b w < w.idxOf a ∧ w.idxOf a < secondPos c w) := by
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
    have low_first_order_132_forbidden (w : List ℕ) (a b c : ℕ) (hcount : ∀ x ∈ w, w.count x = 2)
        (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧ ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
        (havoid : ¬ NonnestingDefs.Occurs [1, 1, 3, 2] w)
        (ha : a ∈ w) (hb : b ∈ w) (hc : c ∈ w)
        (hab : a < b) (hbc : b < c)
        (hfirst : w.idxOf a < w.idxOf c ∧ w.idxOf c < w.idxOf b) : False := by
      have secondAt (x : ℕ) (hx : w.count x = 2) : w[secondPos x w]? = some x := by
        exact secondOccurrence w x hx
      have horders := (nonnesting_iff_equal_orders w hcount).mp hnn
      have hac : secondPos a w < secondPos c w := horders a ha c hc hfirst.1
      have hcb : secondPos c w < secondPos b w := horders c hc b hb hfirst.2
      have hpc := secondAt c (hcount c hc); have hpb := secondAt b (hcount b hb)
      apply havoid; exact (occurs1132_iff w hcount).mpr
          ⟨a, b, c, hab, hbc, ha, secondPos c w, secondPos b w, by omega, by omega, hpc, hpb⟩
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
    have low_first_order_213_forbidden (w : List ℕ) (a b c : ℕ) (hcount : ∀ x ∈ w, w.count x = 2)
        (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧ ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
        (havoid : ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w)
        (ha : a ∈ w) (hb : b ∈ w) (hc : c ∈ w)
        (hab : a < b) (hbc : b < c)
        (hfirst : w.idxOf b < w.idxOf a ∧ w.idxOf a < w.idxOf c) : False := by
      have secondAt (x : ℕ) (hx : w.count x = 2) : w[secondPos x w]? = some x := by
        exact secondOccurrence w x hx
      have horders := (nonnesting_iff_equal_orders w hcount).mp hnn
      have hba : secondPos b w < secondPos a w := horders b hb a ha hfirst.1
      have hac : secondPos a w < secondPos c w := horders a ha c hc hfirst.2
      have hpa := secondAt a (hcount a ha); have hpc := secondAt c (hcount c hc)
      apply havoid; exact (occurs2213_iff w hcount).mpr
        ⟨a, b, c, hab, hbc, hb, secondPos a w, secondPos c w, by omega, by omega, hpa, hpc⟩
    have horders := (nonnesting_iff_equal_orders w hcount).mp hnn
    have secondAt (x : ℕ) (hx : w.count x = 2) : w[secondPos x w]? = some x := by
      exact secondOccurrence w x hx
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
    constructor
    · intro havoid a b c ha hb hc hab hbc
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact low_first_order_132_forbidden w a b c hcount hnn havoid.1
          ha hb hc hab hbc
      · exact low_first_order_213_forbidden w a b c hcount hnn havoid.2
          ha hb hc hab hbc
      · rintro ⟨hfab, hfbc, hsa, hcsb⟩
        apply havoid.1; exact (occurs1132_iff w hcount).mpr
          ⟨a, b, c, hab, hbc, ha, w.idxOf c, secondPos b w,
            hsa, hcsb, List.getElem?_idxOf hc, secondAt b (hcount b hb)⟩
      · rintro ⟨hfbc, hfca, hsb, hac⟩
        apply havoid.2; exact (occurs2213_iff w hcount).mpr
          ⟨a, b, c, hab, hbc, hb, w.idxOf a, secondPos c w,
            hsb, hac, List.getElem?_idxOf ha, secondAt c (hcount c hc)⟩
    · intro htest
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
  have avoids_iff_skew_cuts (p : List ℕ) (hp : p.Nodup) : (¬ NonnestingDefs.Occurs [1, 3, 2] p ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] p) ↔ ∀ t i k (ht : t + 1 < p.length) (hi : i ≤ t)
        (_hk : t < k) (hklen : k < p.length), p[t + 1] < p[t] → p[k] < p[i] := by
    constructor
    · rintro ⟨h132, h213⟩ t i k ht hi hk hklen hdesc
      exact descent_separates p hp h132 h213 t i k ht hdesc hi hk hklen
    · intro hcut
      have descent_between (a b : ℕ) (ha : a < p.length)
          (hb : b < p.length) (hab : a < b) (hval : p[b] < p[a]) : ∃ t, ∃ ht : t + 1 < p.length,
            a ≤ t ∧ t + 1 ≤ b ∧ p[t + 1] < p[t] := by
        by_contra hnone
        have hsteps : ∀ t (ht : t + 1 < p.length) (hat : a ≤ t) (htb : t < b), p[t] ≤ p[t + 1] := by
          intro t ht hat htb
          by_contra hstep
          have hdesc : p[t + 1] < p[t] := (by omega); exact hnone ⟨t, ht, hat, by omega, hdesc⟩
        have hfinal : p[a] ≤ p[b] := by
          let value (index : ℕ) : ℕ := p[min index b]!; have steps (index : ℕ) (lower : a ≤ index) :
              value index ≤ value (index + 1) := by
            by_cases upper : index < b
            · have step := hsteps index (by omega) lower upper
              simpa [value, Nat.min_eq_left (by omega : index ≤ b),
                Nat.min_eq_left (by omega : index + 1 ≤ b), List.getElem!_eq_getElem?_getD,
                List.getElem?_eq_getElem (by omega : index < p.length),
                List.getElem?_eq_getElem (by omega : index + 1 < p.length)] using step
            · simp [value, Nat.min_eq_right (by omega : b ≤ index),
                Nat.min_eq_right (by omega : b ≤ index + 1)]
          have bound := Nat.rel_of_forall_rel_succ_of_le_of_lt
            (· ≤ ·) steps (b := a) (c := b) (by rfl) hab
          simpa [value, Nat.min_eq_left (by omega : a ≤ b), List.getElem!_eq_getElem?_getD,
            List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] using bound
        omega
      constructor
      · intro hocc
        obtain ⟨x, hxlt, _, hsub, _⟩ := hocc
        change List.Sublist [x 1, x 3, x 2] p at hsub
        obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
        have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
        have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
        have hi : i < p.length := (f 0).isLt; have hj : j < p.length := (f 1).isLt
        have hk : k < p.length := (f 2).isLt
        have hv0 : p[i] = x 1 := (by simpa [i] using (hf (0 : Fin 3)).symm)
        have hv1 : p[j] = x 3 := (by simpa [j] using (hf (1 : Fin 3)).symm)
        have hv2 : p[k] = x 2 := (by simpa [k] using (hf (2 : Fin 3)).symm)
        have hik : p[i] < p[k] := by
          rw [hv0, hv2]; exact hxlt 1 (by omega) (by decide)
        have hkj : p[k] < p[j] := by
          rw [hv2, hv1]; exact hxlt 2 (by omega) (by decide)
        obtain ⟨t, htt, hjt, htk, hdesc⟩ := descent_between j k hj hk hjk hkj
        have hsep := hcut t i k htt (by omega) (by omega) hk hdesc; omega
      · intro hocc
        obtain ⟨x, hxlt, _, hsub, _⟩ := hocc
        change List.Sublist [x 2, x 1, x 3] p at hsub
        obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
        have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
        have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
        have hi : i < p.length := (f 0).isLt; have hj : j < p.length := (f 1).isLt
        have hk : k < p.length := (f 2).isLt
        have hv0 : p[i] = x 2 := (by simpa [i] using (hf (0 : Fin 3)).symm)
        have hv1 : p[j] = x 1 := (by simpa [j] using (hf (1 : Fin 3)).symm)
        have hv2 : p[k] = x 3 := (by simpa [k] using (hf (2 : Fin 3)).symm)
        have hji : p[j] < p[i] := by
          rw [hv1, hv0]; exact hxlt 1 (by omega) (by decide)
        have hik : p[i] < p[k] := by
          rw [hv0, hv2]; exact hxlt 2 (by omega) (by decide)
        obtain ⟨t, htt, hit, htj, hdesc⟩ := descent_between i j hi hj hij hji
        have hsep := hcut t i k htt hit (by omega) hk hdesc; omega
  have adjacent_ascent_no_intermediate (p : List ℕ) (hp : p.Nodup)
      (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
      (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p)
      (t : ℕ) (ht : t + 1 < p.length)
      (z : ℕ) (hz : z ∈ p) (hl : p[t] < z) (hr : z < p[t + 1]) : False := by
    have hcut := (avoids_iff_skew_cuts p hp).mp ⟨h132, h213⟩
    have descent_between (a b : ℕ) (ha : a < p.length)
        (hb : b < p.length) (hab : a < b) (hval : p[b] < p[a]) : ∃ s, ∃ hs : s + 1 < p.length,
          a ≤ s ∧ s + 1 ≤ b ∧ p[s + 1] < p[s] := by
      by_contra hnone
      have hsteps : ∀ s (hs : s + 1 < p.length) (has : a ≤ s) (hsb : s < b), p[s] ≤ p[s + 1] := by
        intro s hs has hsb
        by_contra hstep
        exact hnone ⟨s, hs, has, by omega, by omega⟩
      have hfinal : p[a] ≤ p[b] := by
        let value (index : ℕ) : ℕ := p[min index b]!; have steps (index : ℕ) (lower : a ≤ index) :
            value index ≤ value (index + 1) := by
          by_cases upper : index < b
          · have step := hsteps index (by omega) lower upper
            simpa [value, Nat.min_eq_left (by omega : index ≤ b),
              Nat.min_eq_left (by omega : index + 1 ≤ b), List.getElem!_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega : index < p.length),
              List.getElem?_eq_getElem (by omega : index + 1 < p.length)] using step
          · simp [value, Nat.min_eq_right (by omega : b ≤ index),
              Nat.min_eq_right (by omega : b ≤ index + 1)]
        have bound := Nat.rel_of_forall_rel_succ_of_le_of_lt
          (· ≤ ·) steps (b := a) (c := b) (by rfl) hab
        simpa [value, Nat.min_eq_left (by omega : a ≤ b), List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] using bound
      omega
    let i := p.idxOf z; have hi : i < p.length := List.idxOf_lt_length_of_mem hz
    have hzi : p[i] = z := by
      exact (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hz)).2
    have ht0 : t < p.length := (by omega)
    by_cases hit : i < t
    · obtain ⟨s, hs, his, hst, hdesc⟩ := descent_between i t hi ht0 hit (by rw [hzi]; omega)
      have hsep := hcut s i (t + 1) hs his (by omega) ht hdesc; rw [hzi] at hsep; omega
    · have hti : t + 1 < i := by
        have hit' : i ≠ t := by
          intro heq
          have hz' : p[t] = z := (by simpa [heq] using hzi); omega
        have hsi : i ≠ t + 1 := by
          intro heq
          have hz' : p[t + 1] = z := (by simpa [heq] using hzi); omega
        omega
      obtain ⟨s, hs, hts, hsi, hdesc⟩ := descent_between (t + 1) i ht hi hti (by rw [hzi]; omega)
      have hsep := hcut s t i hs (by omega) (by omega) hi hdesc; rw [hzi] at hsep; omega
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
  have later_upstep_crosses (d : List DyckStep) (w p : List ℕ)
      (hscan : scan ∅ w = d) (hcount : ∀ a ∈ w, w.count a = 2)
      (hU : select U d w = p) (hD : select D d w = p)
      (u v z : List DyckStep) (hsplit : d = u ++ [D] ++ v ++ [D] ++ z)
      (hnoD : v.count D = 0) (ht : u.count D + 1 < p.length)
      (q : ℕ) (hq : q < v.length) (hup : v[q] = U)
      (hlater : u.count D + 1 < u.count U + (v.take q).count U) :
      ∃ k, ∃ hk' : k < p.length, u.count D + 1 < k ∧
        secondPos (p[u.count D]'(by omega)) w < w.idxOf (p[k]'hk') ∧
        w.idxOf (p[k]'hk') < secondPos (p[u.count D + 1]'ht) w := by
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
    let k := u.count U + (v.take q).count U; let i := u.length; let j := u.length + 1 + q
    let l := u.length + 1 + v.length
    have hlen : d.length = w.length := (by rw [← hscan]; exact scan_length ∅ w)
    have hdi : d[i]? = some D := (by simp [hsplit, i])
    have hdl : d[l]? = some D := by
      have hsplit' : d = (u ++ [D] ++ v) ++ [D] ++ z := by
        simpa [List.append_assoc] using hsplit
      rw [hsplit']
      have hl : l = (u ++ [D] ++ v).length := (by simp [l]; omega); rw [hl]; simp
    have hdj : d[j]? = some U := by
      have hsplit' : d = u ++ (D :: v ++ [D] ++ z) := by
        simpa [List.append_assoc] using hsplit
      rw [hsplit', List.getElem?_append_right (by dsimp [j]; omega)]
      have heq : j - u.length = q + 1 := (by dsimp [j]; omega); rw [heq]
      have hqopt : v[q]? = some U := by
        rw [List.getElem?_eq_getElem hq]; exact congrArg some hup
      simpa [List.getElem?_append_left hq] using hqopt
    have hri : (d.take i).count D = u.count D := (by simp [hsplit, i])
    have hrl : (d.take l).count D = u.count D + 1 + v.count D := by
      have hsplit' : d = (u ++ [D] ++ v) ++ [D] ++ z := by
        simpa [List.append_assoc] using hsplit
      rw [hsplit']
      have hl : l = (u ++ [D] ++ v).length := (by simp [l]; omega)
      have htake : ((u ++ [D] ++ v) ++ [D] ++ z).take l = u ++ [D] ++ v := by
        rw [hl]; simpa [List.append_assoc] using
          (List.take_left : ((u ++ [D] ++ v) ++ ([D] ++ z)).take
            (u ++ [D] ++ v).length = u ++ [D] ++ v)
      rw [htake]; simp; omega
    have hrj : (d.take j).count U = k := by
      have hsplit' : d = (u ++ [D]) ++ (v ++ [D] ++ z) := by
        simpa [List.append_assoc] using hsplit
      have hj : j = (u ++ [D]).length + q := (by simp [j])
      have htake : d.take j = (u ++ [D]) ++ v.take q := by
        rw [hsplit', hj, List.take_append]; rw [Nat.add_sub_cancel_left]
        have hv : (v ++ [D] ++ z).take q = v.take q := by
          simpa [List.append_assoc] using
            (List.take_append_of_le_length (by omega : q ≤ v.length) :
              (v ++ ([D] ++ z)).take q = v.take q)
        rw [hv]; have hprefix : (u ++ [D]).take ((u ++ [D]).length + q) = u ++ [D] :=
          List.take_of_length_le (by omega)
        rw [hprefix]
      rw [htake]; simp [k]
    have hk : k < p.length := by
      have hs := select_position U d w j hdj; rw [hU, hrj] at hs
      have hjlen : j < w.length := by
        have hjd : j < d.length := (List.getElem?_eq_some_iff.mp hdj).1; omega
      by_contra hn
      have hnone : p[k]? = none := List.getElem?_eq_none_iff.mpr (by omega); rw [hnone] at hs
      have hwSome : w[j]? ≠ none := (by simp [hjlen]); exact hwSome hs.symm
    have hpos (t : DyckStep) (m r : ℕ) (htag : d[m]? = some t) (hrank : (d.take m).count t = r)
        (hqueue : select t d w = p) (hr : r < p.length) :
        m = if t = U then w.idxOf p[r] else secondPos p[r] w := by
      have hs := select_position t d w m htag; rw [hqueue, hrank] at hs
      have hw : w[m]? = some p[r] := by
        rw [← hs]; exact List.getElem?_eq_getElem hr
      have hc : w.count p[r] = 2 := hcount p[r] (List.mem_of_getElem? hw)
      have htag' : (scan ∅ w)[m]? = some t := (by simpa [hscan] using htag)
      exact scan_tag_position t w p[r] m hc hw htag'
    have hwi := hpos D i (u.count D) hdi hri hD (by omega)
    have hwl := hpos D l (u.count D + 1) hdl (by omega) hD ht; have hwj := hpos U j k hdj hrj hU hk
    have hwi' : i = secondPos p[u.count D] w := (by simpa using hwi)
    have hwl' : l = secondPos p[u.count D + 1] w := (by simpa using hwl)
    have hwj' : j = w.idxOf p[k] := (by simpa using hwj)
    refine ⟨k, hk, hlater, ?_, ?_⟩
    · rw [← hwi', ← hwj']
      dsimp [i, j]; omega
    · rw [← hwj', ← hwl']
      dsimp [j, l]; omega
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
  have low_first_order_avoids (d : DyckWord) (w p : List ℕ) (hscan : scan ∅ w = d.toList)
      (hcount : ∀ a ∈ w, w.count a = 2)
      (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧ ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w)
      (havoid : ¬ NonnestingDefs.Occurs [1, 1, 3, 2] w ∧ ¬ NonnestingDefs.Occurs [2, 2, 1, 3] w)
      (hU : select U d.toList w = p) : ¬ NonnestingDefs.Occurs [1, 3, 2] p ∧
      ¬ NonnestingDefs.Occurs [2, 1, 3] p := by
    have htest := (low_local_test w hcount hnn).mp havoid
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
      exact (htest (x 1) (x 2) (x 3) hm.2.1 hm.1 hm.2.2 h12 h23).2.1 ⟨horder.1, horder.2⟩
    exact ⟨h132, h213⟩
  obtain ⟨h132, h213⟩ := low_first_order_avoids d w p
    hscan hcount hnn havoid hU
  have htest := (low_local_test w hcount hnn).mp havoid
  have hpair := queue_pairwise_position U w hcount; rw [hscan, hU] at hpair
  have hgood : (∀ q, q < v.length → u.count U + q ≤ u.count D + 1) →
      v = [] ∨ (v = [U] ∧ u.count U = u.count D + 1) := by
    have htake : d.toList.take (u.length + 1) = u ++ [D] := by
      rw [hsplit]
      have heq : u.length + 1 = (u ++ [D]).length := (by simp); rw [heq]
      simpa only [List.append_assoc] using
        (show ((u ++ [D]) ++ (v ++ [D] ++ z)).take (u ++ [D]).length = u ++ [D] from List.take_left)
    have hbalance : u.count D + 1 ≤ u.count U := by
      have h := d.count_D_le_count_U (u.length + 1); rw [htake] at h; simpa using h
    intro hall
    by_cases hv : v = []
    · exact Or.inl hv
    · have hlenpos : 0 < v.length := by
        cases v with
        | nil => contradiction
        | cons _ _ => simp
      have h0 := hall 0 hlenpos; have hground : u.count U = u.count D + 1 := (by omega)
      have hlenle : v.length ≤ 1 := by
        by_contra hnot
        have h1 := hall 1 (by omega); omega
      have hlen : v.length = 1 := (by omega)
      cases v with
      | nil => contradiction
      | cons a v =>
        cases v with
        | nil =>
          cases a with
          | U => exact Or.inr ⟨rfl, hground⟩
          | D => simp at hnoD
        | cons b v => simp at hlen
  apply hgood; intro q hq; have hallU (x : List DyckStep) (hx : x.count D = 0) :
      x = List.replicate x.length U := by
    induction x with
    | nil => rfl
    | cons a xs ih =>
      cases a with
      | U =>
        have hxs : xs.count D = 0 := (by simpa using hx)
        simpa [List.replicate_succ] using congrArg (U :: ·) (ih hxs)
      | D => simp at hx
  have hqcount : (v.take q).count U = q := by
    rw [hallU v hnoD]; simp [List.take_replicate, Nat.min_eq_left (by omega : q ≤ v.length)]
  by_contra hbad
  have hlater : u.count D + 1 < u.count U + (v.take q).count U := by
    rw [hqcount]; omega
  have hup : v[q] = U := by
    cases hstep : v[q] with
    | U => rfl
    | D =>
      have hnot : D ∉ v := List.count_eq_zero.mp hnoD
      exact False.elim (hnot (by rw [← hstep]; exact List.getElem_mem hq))
  obtain ⟨k, hk, htk, hcross⟩ := later_upstep_crosses d.toList w p hscan hcount hU hD
      u v z hsplit hnoD ht q hq hup hlater
  let t := u.count D; have ht0 : t < p.length := (by dsimp [t]; omega)
  have ht1 : t + 1 < p.length := (by simpa [t] using ht)
  have hp0 : p[t] ∈ w := (select_sublist U d.toList w).subset
    (by rw [hU]; exact List.getElem_mem ht0)
  have hp1 : p[t + 1] ∈ w := (select_sublist U d.toList w).subset
    (by rw [hU]; exact List.getElem_mem ht1)
  have hpk : p[k] ∈ w := (select_sublist U d.toList w).subset
    (by rw [hU]; exact List.getElem_mem hk)
  have hfirst01 : w.idxOf p[t] < w.idxOf p[t + 1] := by
    have h := (List.pairwise_iff_getElem.mp hpair) t (t + 1) ht0 ht1
      (by omega)
    simpa using h
  have hfirst1k : w.idxOf p[t + 1] < w.idxOf p[k] := by
    have h := (List.pairwise_iff_getElem.mp hpair) (t + 1) k ht1 hk
      (by simpa [t] using htk)
    simpa using h
  have hnotmid : ¬ (p[t] < p[k] ∧ p[k] < p[t + 1]) := by
    rintro ⟨hl, hr⟩
    exact adjacent_ascent_no_intermediate p hp h132 h213 t ht1 p[k]
      (List.getElem_mem hk) hl hr
  have hne0 : p[k] ≠ p[t] := by
    intro heq; have := (hp.getElem_inj_iff (hi := hk) (hj := ht0)).mp heq; omega
  have hne1 : p[k] ≠ p[t + 1] := by
    intro heq; have := (hp.getElem_inj_iff (hi := hk) (hj := ht1)).mp heq; omega
  have hasc' : p[t] < p[t + 1] := (by simpa [t] using hasc)
  by_cases hlarge : p[t + 1] < p[k]
  · exact (htest p[t] p[t + 1] p[k] hp0 hp1 hpk hasc' hlarge).2.2.1
      ⟨hfirst01, hfirst1k, by simpa [t] using hcross.1, by simpa [t] using hcross.2⟩
  · have hsmall : p[k] < p[t] := by omega
    exact (htest p[k] p[t] p[t + 1] hpk hp0 hp1 hsmall hasc').2.2.2
      ⟨hfirst01, hfirst1k, by simpa [t] using hcross.1, by simpa [t] using hcross.2⟩
#print axioms ascent_forces_good_gap

end D5.S3.Combinatorics.Nonnesting.NonnestingRoyalLowGap
