/- GID: D5/S3/Combinatorics/ShankarWords/OddWordConstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ShankarWords/OddWordConstruction
   mirror-E: none(waiver:open-structural-word-classification)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn, mathlib/module/Mathlib.Data.List.Count]
   utility: none
   digest: Injective odd lattice-word candidates at the proposed descent level. -/

import D5.S3.Combinatorics.ShankarWords.ActualWordExtremal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

open D5.S3.Combinatorics.ShankarWords.ActualWordExtremal

namespace D5.S3.Combinatorics.ShankarWords.OddWordConstruction

set_option maxHeartbeats 3000000 in
/-- Every odd candidate is an actual word at the proposed level, with distinct indices. -/
theorem odd_word_construction (t : ℕ) (ht : 1 ≤ t) :
    Function.Injective (oddWord t) ∧
      ∀ i : OddIndex t, oddWord t i ∈ actualWords (2 * t + 1) ∧
        descents (oddWord t i) = extremalValue (2 * t + 1) := by
  classical
  have pair_zero (a b : ℕ) : pairBlocks a b 0 = [] := by simp [pairBlocks]
  have pair_succ (a b n : ℕ) :
      pairBlocks a b (n + 1) = a :: b :: pairBlocks a b n := by
    simp [pairBlocks, List.replicate_succ]
  have pair_len (a b n : ℕ) : (pairBlocks a b n).length = 2 * n := by
    simp [pairBlocks, Nat.mul_comm]
  have pair_mem (a b n c : ℕ) (hc : c ∈ pairBlocks a b n) : c = a ∨ c = b := by
    exact (by simpa [pairBlocks] using hc : n ≠ 0 ∧ (c = a ∨ c = b)).2
  have pair_count (a b c n : ℕ) :
      (pairBlocks a b n).count c = n * (([a, b] : List ℕ).count c) := by
    simp [pairBlocks, List.count_flatten]
  have pair_add (a b n m : ℕ) :
      pairBlocks a b (n + m) = pairBlocks a b n ++ pairBlocks a b m := by
    simp only [pairBlocks, List.replicate_add, List.flatten_append]
  have pair_take (a b n q : ℕ) (hq : q ≤ n) :
      (pairBlocks a b n).take (2 * q) = pairBlocks a b q := by
    rw [show n = q + (n - q) by omega, pair_add]
    simp [← pair_len a b q]
  have pair_drop (a b n q : ℕ) (hq : q ≤ n) :
      (pairBlocks a b n).drop (2 * q) = pairBlocks a b (n - q) := by
    rw [show n = q + (n - q) by omega, pair_add]
    simp only [← pair_len a b q, List.drop_left]
    congr 1; omega
  have pair_prefix (a b n m : ℕ) (hab : a ≠ b) :
      ((pairBlocks a b n).take m).count a = min n ((m + 1) / 2) ∧
      ((pairBlocks a b n).take m).count b = min n (m / 2) := by
    induction n generalizing m with
    | zero => simp [pair_zero]
    | succ n ih =>
      cases m with
      | zero => simp
      | succ m =>
        cases m with
        | zero => simp [pair_succ, hab]
        | succ m =>
          obtain ⟨ha, hb⟩ := ih m
          simp only [pair_succ, List.take_succ_cons, List.count_cons_self,
            List.count_cons_of_ne hab, List.count_cons_of_ne (Ne.symm hab)]
          constructor <;> omega
  have prefix_absent (a b c n m : ℕ) (hca : c ≠ a) (hcb : c ≠ b) :
      ((pairBlocks a b n).take m).count c = 0 := by
    apply List.count_eq_zero.mpr
    intro hc
    rcases pair_mem a b n c (List.mem_of_mem_take hc) with h | h <;> contradiction
  have pair_get (a b n p : ℕ) (hp : p < (pairBlocks a b n).length) :
      (pairBlocks a b n)[p] = if p % 2 = 0 then a else b := by
    induction n generalizing p with
    | zero => simp [pair_zero] at hp
    | succ n ih =>
      cases p with
      | zero => simp [pair_succ]
      | succ p =>
        cases p with
        | zero => simp [pair_succ]
        | succ p =>
          have h : p < (pairBlocks a b n).length := by simp [pair_len] at hp ⊢; omega
          simpa only [pair_succ, List.getElem_cons_succ,
            show (p + 1 + 1) % 2 = p % 2 by omega] using ih p h
  have hdesc_cons (a b : ℕ) (v : List ℕ) :
      descents (a :: b :: v) = (if b < a then 1 else 0) + descents (b :: v) := by
    simp [descents, List.zip_cons_cons, List.filter_cons]
    split <;> simp_all <;> omega
  have hdesc_pairs (a b c n : ℕ) (v : List ℕ) (hab : b < a) (hca : b ≤ a)
      (hbc : b ≤ c) :
      descents (pairBlocks a b n ++ c :: v) = n + descents (c :: v) := by
    induction n with
    | zero => simp [pair_zero]
    | succ n ih =>
      rw [pair_succ]
      simp only [List.cons_append]
      rw [hdesc_cons]
      simp only [if_pos hab]
      cases n with
      | zero => simp [pair_zero, hdesc_cons, Nat.not_lt.mpr hbc]
      | succ n =>
        rw [pair_succ]
        simp only [List.cons_append]
        rw [hdesc_cons]
        simp only [if_neg (Nat.not_lt.mpr hca), zero_add]
        rw [← List.cons_append, ← List.cons_append, ← pair_succ, ih]
        omega
  have hcarrier (k : ℕ) (w : List ℕ) (hw : IsAdmissible k w) :
      w ∈ actualWords k := by
    obtain ⟨hlen, halphabet, hrest⟩ := hw
    have hraw : w ∈ rawWords k := by
      let f : Fin (3 * k) → Fin 3 := fun i =>
        ⟨w[i.val]'(by rw [hlen]; exact i.isLt) - 1, by
          have h := halphabet _ (List.getElem_mem (by rw [hlen]; exact i.isLt))
          omega⟩
      apply Finset.mem_image.mpr
      refine ⟨f, Finset.mem_univ _, ?_⟩
      rw [← List.ofFn_get w, List.ofFn_congr hlen]
      apply congrArg List.ofFn
      funext i
      dsimp [f]
      have h := halphabet _ (List.getElem_mem (by rw [hlen]; exact i.isLt))
      omega
    simpa only [actualWords, Finset.mem_filter] using
      (show w ∈ rawWords k ∧ IsAdmissible k w from ⟨hraw, hlen, halphabet, hrest⟩)
  have havoid_sep (u v z : List ℕ)
      (hu : ∀ a ∈ u, a ≠ 3) (hv : ∀ a ∈ v, a ≠ 2)
      (hz : ∀ a ∈ z, a ≠ 1) : Avoids321 (u ++ v ++ z) := by
    intro i j k hij hjk hbad
    obtain ⟨hi, hj, hk⟩ := hbad
    change (u ++ v ++ z)[i.val] = 3 at hi
    change (u ++ v ++ z)[j.val] = 2 at hj
    change (u ++ v ++ z)[k.val] = 1 at hk
    have hi0 : u.length ≤ i.val := by
      by_contra h
      have hil : i.val < u.length := by omega
      have he : (u ++ v ++ z)[i.val] = u[i.val] := by
        simp only [List.append_assoc]
        rw [List.getElem_append_left hil]
      exact hu _ (List.getElem_mem hil) (he.symm.trans hi)
    have hj0 : u.length + v.length ≤ j.val := by
      by_contra h
      have hj1 : u.length ≤ j.val := by change i.val < j.val at hij; omega
      have hjl : j.val - u.length < v.length := by omega
      have he : (u ++ v ++ z)[j.val] = v[j.val - u.length] := by
        simp only [List.append_assoc]
        rw [List.getElem_append_right hj1, List.getElem_append_left hjl]
      exact hv _ (List.getElem_mem hjl) (he.symm.trans hj)
    have hkl : k.val - (u.length + v.length) < z.length := by
      have hh := k.isLt
      simp only [List.length_append] at hh
      change j.val < k.val at hjk
      omega
    have he : (u ++ v ++ z)[k.val] = z[k.val - (u.length + v.length)] := by
      rw [List.getElem_append_right (by
        simp only [List.length_append]; change j.val < k.val at hjk; omega)]
      simp only [List.length_append]
    exact hz _ (List.getElem_mem hkl) (he.symm.trans hk)
  have c211 (n m : ℕ) : ((pairBlocks 2 1 n).take m).count 1 = min n (m / 2) :=
    (pair_prefix 2 1 n m (by decide)).2
  have c212 (n m : ℕ) : ((pairBlocks 2 1 n).take m).count 2 = min n ((m + 1) / 2) :=
    (pair_prefix 2 1 n m (by decide)).1
  have c213 (n m : ℕ) : ((pairBlocks 2 1 n).take m).count 3 = 0 :=
    prefix_absent 2 1 3 n m (by decide) (by decide)
  have c311 (n m : ℕ) : ((pairBlocks 3 1 n).take m).count 1 = min n (m / 2) :=
    (pair_prefix 3 1 n m (by decide)).2
  have c312 (n m : ℕ) : ((pairBlocks 3 1 n).take m).count 2 = 0 :=
    prefix_absent 3 1 2 n m (by decide) (by decide)
  have c313 (n m : ℕ) : ((pairBlocks 3 1 n).take m).count 3 = min n ((m + 1) / 2) :=
    (pair_prefix 3 1 n m (by decide)).1
  have c321 (n m : ℕ) : ((pairBlocks 3 2 n).take m).count 1 = 0 :=
    prefix_absent 3 2 1 n m (by decide) (by decide)
  have c322 (n m : ℕ) : ((pairBlocks 3 2 n).take m).count 2 = min n (m / 2) :=
    (pair_prefix 3 2 n m (by decide)).2
  have c323 (n m : ℕ) : ((pairBlocks 3 2 n).take m).count 3 = min n ((m + 1) / 2) :=
    (pair_prefix 3 2 n m (by decide)).1
  have csingle (a c m : ℕ) : (([a] : List ℕ).take m).count c =
      if m = 0 then 0 else if a = c then 1 else 0 := by
    cases m <;> simp [List.count_cons]
  let oneForm (a b c d : ℕ) : List ℕ :=
    [1] ++ pairBlocks 2 1 a ++ pairBlocks 3 1 b ++ [1] ++
      pairBlocks 2 1 c ++ pairBlocks 3 1 d ++ pairBlocks 3 2 (t + 1) ++ [3]
  have one_valid (a b c d : ℕ) (hac : a + c = t) (hbd : b + d = t - 1)
      (horder : b = 0 ∨ c = 0) : IsAdmissible (2 * t + 1) (oneForm a b c d) := by
    have hlen : (oneForm a b c d).length = 3 * (2 * t + 1) := by
      simp only [oneForm, List.length_append, List.length_singleton, pair_len]; omega
    have halphabet : ∀ x ∈ oneForm a b c d, 1 ≤ x ∧ x ≤ 3 := by
      intro x hx
      simp only [oneForm, List.mem_append, List.mem_singleton] at hx
      rcases hx with ((((((rfl | hx) | hx) | rfl) | hx) | hx) | hx) | rfl
      all_goals try omega
      all_goals rcases pair_mem _ _ _ x hx with rfl | rfl <;> omega
    have hcounts : (oneForm a b c d).count 1 = 2 * t + 1 ∧
        (oneForm a b c d).count 2 = 2 * t + 1 ∧
        (oneForm a b c d).count 3 = 2 * t + 1 := by
      simp [oneForm, pair_count]; omega
    have hlattice : IsLattice (oneForm a b c d) := by
      intro i
      generalize hm : i.val = m
      simp only [oneForm, List.take_append, List.length_append,
        List.length_singleton, pair_len, List.count_append,
        c211, c212, c213, c311, c312, c313, c321, c322, c323, csingle]
      simp only [show ¬ (1 : ℕ) = 2 by decide, show ¬ (1 : ℕ) = 3 by decide,
        show ¬ (3 : ℕ) = 1 by decide, show ¬ (3 : ℕ) = 2 by decide,
        ite_true, ite_false, Nat.zero_add, Nat.add_zero]
      rcases horder with hb | hc
      · subst b
        simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.zero_min]
        split_ifs <;> constructor <;> omega
      · subst c
        simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.zero_min]
        split_ifs <;> constructor <;> omega
    have havoid : Avoids321 (oneForm a b c d) := by
      rcases horder with hb | hc
      · subst b
        have he : oneForm a 0 c d =
            ([1] ++ pairBlocks 2 1 a ++ [1] ++ pairBlocks 2 1 c) ++
              pairBlocks 3 1 d ++ (pairBlocks 3 2 (t + 1) ++ [3]) := by
          simp only [oneForm, pair_zero, List.append_nil, List.nil_append, List.append_assoc]
        rw [he]
        apply havoid_sep
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with ((rfl | hx) | rfl) | hx
          all_goals try omega
          all_goals rcases pair_mem 2 1 _ x hx with rfl | rfl <;> omega
        · intro x hx
          rcases pair_mem 3 1 _ x hx with rfl | rfl <;> omega
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · rcases pair_mem 3 2 _ x hx with rfl | rfl <;> omega
          · omega
      · subst c
        have he : oneForm a b 0 d =
            ([1] ++ pairBlocks 2 1 a) ++
              (pairBlocks 3 1 b ++ [1] ++ pairBlocks 3 1 d) ++
                (pairBlocks 3 2 (t + 1) ++ [3]) := by
          simp only [oneForm, pair_zero, List.append_nil, List.nil_append, List.append_assoc]
        rw [he]
        apply havoid_sep
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with rfl | hx
          · omega
          · rcases pair_mem 2 1 _ x hx with rfl | rfl <;> omega
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with (hx | rfl) | hx
          all_goals try omega
          all_goals rcases pair_mem 3 1 _ x hx with rfl | rfl <;> omega
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · rcases pair_mem 3 2 _ x hx with rfl | rfl <;> omega
          · omega
    exact ⟨hlen, halphabet, hcounts.1, hcounts.2.1, hcounts.2.2, hlattice, havoid⟩
  have one_early (q : Fin (2 * t)) (hq : q.val ≤ t) :
      oddOneWord t q = oneForm q.val 0 (t - q.val) (t - 1) := by
    have he : oddOneBase t = pairBlocks 2 1 t ++
        (pairBlocks 3 1 (t - 1) ++ pairBlocks 3 2 (t + 1)) := by
      simp [oddOneBase, List.append_assoc]
    simp only [oddOneWord, he]
    rw [List.take_append_of_le_length (by rw [pair_len]; omega), pair_take 2 1 t q.val hq,
      List.drop_append_of_le_length (by rw [pair_len]; omega), pair_drop 2 1 t q.val hq]
    simp only [oneForm, pair_zero, List.append_nil, List.nil_append, List.append_assoc]
  have one_late (q : Fin (2 * t)) (hq : t < q.val) :
      oddOneWord t q = oneForm t (q.val - t) 0 (2 * t - 1 - q.val) := by
    have hq' : q.val - t ≤ t - 1 := by have hh := q.isLt; omega
    simp only [oddOneWord, oddOneBase, List.append_assoc]
    rw [List.take_append, pair_len, List.take_of_length_le (by rw [pair_len]; omega)]
    rw [show 2 * q.val - 2 * t = 2 * (q.val - t) by omega]
    rw [List.take_append_of_le_length (by rw [pair_len]; omega), pair_take 3 1 (t - 1) _ hq']
    rw [List.drop_append, List.drop_eq_nil_of_le (by rw [pair_len]; omega)]
    simp only [pair_len, List.nil_append]
    rw [show 2 * q.val - 2 * t = 2 * (q.val - t) by omega]
    rw [List.drop_append_of_le_length (by rw [pair_len]; omega), pair_drop 3 1 (t - 1) _ hq']
    simp only [oneForm, pair_zero, List.append_nil, List.nil_append, List.append_assoc]
    rw [show t - 1 - (q.val - t) = 2 * t - 1 - q.val by omega]
  have one_adm (q : Fin (2 * t)) : IsAdmissible (2 * t + 1) (oddOneWord t q) := by
    by_cases hq : q.val ≤ t
    · rw [one_early q hq]
      exact one_valid _ _ _ _ (by omega) (by omega) (Or.inl rfl)
    · rw [one_late q (by omega)]
      exact one_valid _ _ _ _ (by omega) (by have hh := q.isLt; omega) (Or.inr rfl)
  have two_adm (late : Bool) : IsAdmissible (2 * t + 1) (oddTwoWord t late) := by
    have hlen : (oddTwoWord t late).length = 3 * (2 * t + 1) := by
      cases late <;> simp [oddTwoWord, pair_len] <;> omega
    have halphabet : ∀ x ∈ oddTwoWord t late, 1 ≤ x ∧ x ≤ 3 := by
      intro x hx
      cases late
      · simp only [oddTwoWord, Bool.false_eq_true, if_false, List.mem_append,
          List.mem_singleton] at hx
        rcases hx with (((rfl | h21) | (rfl | h31)) | h32) | rfl
        all_goals try omega
        · rcases pair_mem 2 1 _ x h21 with rfl | rfl <;> omega
        · rcases pair_mem 3 1 _ x h31 with rfl | rfl <;> omega
        · rcases pair_mem 3 2 _ x h32 with rfl | rfl <;> omega
      · simp only [oddTwoWord, if_true, List.mem_append, List.mem_singleton] at hx
        rcases hx with (((rfl | h21) | (h31 | rfl)) | h32) | rfl
        all_goals try omega
        · rcases pair_mem 2 1 _ x h21 with rfl | rfl <;> omega
        · rcases pair_mem 3 1 _ x h31 with rfl | rfl <;> omega
        · rcases pair_mem 3 2 _ x h32 with rfl | rfl <;> omega
    have hcounts : (oddTwoWord t late).count 1 = 2 * t + 1 ∧
        (oddTwoWord t late).count 2 = 2 * t + 1 ∧
        (oddTwoWord t late).count 3 = 2 * t + 1 := by
      cases late <;> simp [oddTwoWord, pair_count] <;> omega
    have hlattice : IsLattice (oddTwoWord t late) := by
      intro i
      generalize hm : i.val = m
      cases late <;>
        simp only [oddTwoWord, Bool.false_eq_true, if_false, if_true,
          List.take_append, List.length_append, List.length_singleton, pair_len,
          List.count_append, c211, c212, c213, c311, c312, c313,
          c321, c322, c323, csingle]
      all_goals simp only [show ¬ (1 : ℕ) = 2 by decide, show ¬ (1 : ℕ) = 3 by decide,
        show ¬ (2 : ℕ) = 1 by decide, show ¬ (2 : ℕ) = 3 by decide,
        show ¬ (3 : ℕ) = 1 by decide, show ¬ (3 : ℕ) = 2 by decide,
        ite_true, ite_false, Nat.zero_add, Nat.add_zero]
      all_goals split_ifs <;> constructor <;> omega
    have havoid : Avoids321 (oddTwoWord t late) := by
      cases late
      · have he : oddTwoWord t false =
            ([1] ++ pairBlocks 2 1 t ++ [2]) ++ pairBlocks 3 1 t ++
              (pairBlocks 3 2 t ++ [3]) := by simp [oddTwoWord, List.append_assoc]
        rw [he]
        apply havoid_sep
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with (rfl | hx) | rfl
          all_goals try omega
          rcases pair_mem 2 1 _ x hx with rfl | rfl <;> omega
        · intro x hx
          rcases pair_mem 3 1 _ x hx with rfl | rfl <;> omega
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · rcases pair_mem 3 2 _ x hx with rfl | rfl <;> omega
          · omega
      · have he : oddTwoWord t true =
            ([1] ++ pairBlocks 2 1 t) ++ pairBlocks 3 1 t ++
              ([2] ++ pairBlocks 3 2 t ++ [3]) := by simp [oddTwoWord, List.append_assoc]
        rw [he]
        apply havoid_sep
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with rfl | hx
          · omega
          · rcases pair_mem 2 1 _ x hx with rfl | rfl <;> omega
        · intro x hx
          rcases pair_mem 3 1 _ x hx with rfl | rfl <;> omega
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with (rfl | hx) | rfl
          all_goals try omega
          rcases pair_mem 3 2 _ x hx with rfl | rfl <;> omega
    exact ⟨hlen, halphabet, hcounts.1, hcounts.2.1, hcounts.2.2, hlattice, havoid⟩
  have hdesc_phase (a b n : ℕ) (v : List ℕ) (hab : b < a) :
      descents (b :: (pairBlocks a b n ++ v)) = n + descents (b :: v) := by
    induction n with
    | zero => simp [pair_zero]
    | succ n ih =>
      rw [pair_succ]
      simp only [List.cons_append]
      rw [hdesc_cons, hdesc_cons]
      simp only [if_neg (by omega : ¬ a < b), if_pos hab, zero_add, ih]
      omega
  have hdesc_terminal (d n : ℕ) (hd : d ≤ 3) :
      descents (d :: (pairBlocks 3 2 n ++ [3])) = n := by
    cases n with
    | zero => simp [pair_zero, descents, Nat.not_lt.mpr hd]
    | succ n =>
      rw [pair_succ]
      simp only [List.cons_append]
      rw [hdesc_cons, hdesc_cons]
      simp only [if_neg (Nat.not_lt.mpr hd), if_pos (by decide : (2 : ℕ) < 3), zero_add]
      rw [hdesc_phase 3 2 n _ (by decide)]
      simp [descents]; omega
  have one_desc (q : Fin (2 * t)) : descents (oddOneWord t q) = 3 * t := by
    by_cases hq : q.val ≤ t
    · rw [one_early q hq]
      simp only [oneForm, pair_zero, List.append_nil, List.nil_append, List.append_assoc,
        List.singleton_append, List.cons_append, List.nil_append]
      rw [hdesc_phase 2 1 q.val _ (by decide), hdesc_cons]
      simp only [if_neg (by decide : ¬ (1 : ℕ) < 1), zero_add]
      rw [hdesc_phase 2 1 (t - q.val) _ (by decide),
        hdesc_phase 3 1 (t - 1) _ (by decide), hdesc_terminal 1 (t + 1) (by decide)]
      omega
    · rw [one_late q (by omega)]
      simp only [oneForm, pair_zero, List.append_nil, List.nil_append, List.append_assoc,
        List.singleton_append, List.cons_append, List.nil_append]
      rw [hdesc_phase 2 1 t _ (by decide), hdesc_phase 3 1 (q.val - t) _ (by decide),
        hdesc_cons]
      simp only [if_neg (by decide : ¬ (1 : ℕ) < 1), zero_add]
      rw [hdesc_phase 3 1 (2 * t - 1 - q.val) _ (by decide),
        hdesc_terminal 1 (t + 1) (by decide)]
      have hh := q.isLt
      omega
  have two_desc (late : Bool) : descents (oddTwoWord t late) = 3 * t := by
    cases late
    · simp only [oddTwoWord, Bool.false_eq_true, if_false, List.append_assoc,
        List.singleton_append, List.cons_append, List.nil_append]
      rw [hdesc_phase 2 1 t _ (by decide), hdesc_cons]
      simp only [if_neg (by decide : ¬ (2 : ℕ) < 1), zero_add]
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      rw [hn, pair_succ 3 1]
      simp only [List.cons_append]
      rw [hdesc_cons, hdesc_cons]
      simp only [if_neg (by decide : ¬ (3 : ℕ) < 2), if_pos (by decide : (1 : ℕ) < 3), zero_add]
      rw [hdesc_phase 3 1 n _ (by decide), hdesc_terminal 1 (n + 1) (by decide)]
      omega
    · simp only [oddTwoWord, if_true, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
      rw [hdesc_phase 2 1 t _ (by decide), hdesc_phase 3 1 t _ (by decide), hdesc_cons]
      simp only [if_neg (by decide : ¬ (2 : ℕ) < 1), zero_add]
      rw [hdesc_terminal 2 t (by decide)]
      omega
  have rc_len (w : List ℕ) : (reverseComplement w).length = w.length := by
    simp [reverseComplement]
  have rc_get (w : List ℕ) (p : ℕ) (hp : p < (reverseComplement w).length) :
      (reverseComplement w)[p] = 4 - w[w.length - 1 - p]'(by rw [rc_len] at hp; omega) := by
    simp only [reverseComplement, List.getElem_map, List.getElem_reverse]
  have rc_count (w : List ℕ) (hw : ∀ x ∈ w, 1 ≤ x ∧ x ≤ 3)
      (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 3) :
      (reverseComplement w).count a = w.count (4 - a) := by
    simp only [reverseComplement, List.count_eq_countP, List.countP_map, List.countP_reverse]
    apply List.countP_congr
    intro x hx
    simp only [Function.comp_apply, beq_iff_eq]
    have h := hw x hx
    omega
  have rc_involution (w : List ℕ) (hw : ∀ x ∈ w, 1 ≤ x ∧ x ≤ 3) :
      reverseComplement (reverseComplement w) = w := by
    simp only [reverseComplement, List.map_reverse, List.reverse_reverse, List.map_map]
    conv_rhs => rw [← List.map_id w]
    apply List.map_congr_left
    intro x hx
    have h := hw x hx
    simp only [Function.comp_apply, id_eq]
    omega
  have rc_prefix (w : List ℕ) (hw : ∀ x ∈ w, 1 ≤ x ∧ x ≤ 3)
      (a m : ℕ) (ha : 1 ≤ a ∧ a ≤ 3) :
      ((reverseComplement w).take m).count a =
        w.count (4 - a) - (w.take (w.length - m)).count (4 - a) := by
    simp only [reverseComplement, ← List.map_take, List.take_reverse]
    rw [show (w.drop (w.length - m)).reverse.map (fun x => 4 - x) =
      reverseComplement (w.drop (w.length - m)) from rfl]
    rw [rc_count _ (fun x hx => hw x (List.mem_of_mem_drop hx)) a ha]
    have he := congrArg (fun v : List ℕ => v.count (4 - a))
      (List.take_append_drop (w.length - m) w)
    simp only [List.count_append] at he
    omega
  have rc_adm (k : ℕ) (w : List ℕ) (hw : IsAdmissible k w) :
      IsAdmissible k (reverseComplement w) := by
    obtain ⟨hlen, halpha, hc1, hc2, hc3, hlat, hav⟩ := hw
    refine ⟨by rw [rc_len, hlen], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [reverseComplement, List.mem_map, List.mem_reverse] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have h := halpha a ha
      omega
    · rw [rc_count w halpha 1 (by decide)]; exact hc3
    · rw [rc_count w halpha 2 (by decide)]; exact hc2
    · rw [rc_count w halpha 3 (by decide)]; exact hc1
    · intro i
      have h := hlat ⟨w.length - i.val, by omega⟩
      simp only [rc_prefix w halpha 1 i.val (by decide),
        rc_prefix w halpha 2 i.val (by decide), rc_prefix w halpha 3 i.val (by decide)]
      simp only [show 4 - 1 = (3 : ℕ) by decide, show 4 - 2 = (2 : ℕ) by decide,
        show 4 - 3 = (1 : ℕ) by decide, hc1, hc2, hc3]
      dsimp at h
      constructor <;> omega
    · intro i j l hij hjl hbad
      obtain ⟨hi, hj, hl⟩ := hbad
      change (reverseComplement w)[i.val] = 3 at hi
      change (reverseComplement w)[j.val] = 2 at hj
      change (reverseComplement w)[l.val] = 1 at hl
      rw [rc_get] at hi hj hl
      have hib : w.length - 1 - i.val < w.length := by
        have h : i.val < w.length := by simpa only [rc_len] using i.isLt
        omega
      have hjb : w.length - 1 - j.val < w.length := by
        have h : j.val < w.length := by simpa only [rc_len] using j.isLt
        omega
      have hlb : w.length - 1 - l.val < w.length := by
        have h : l.val < w.length := by simpa only [rc_len] using l.isLt
        omega
      have hi' := halpha _ (List.getElem_mem hib)
      have hj' := halpha _ (List.getElem_mem hjb)
      have hl' := halpha _ (List.getElem_mem hlb)
      apply hav ⟨w.length - 1 - l.val, hlb⟩
        ⟨w.length - 1 - j.val, hjb⟩ ⟨w.length - 1 - i.val, hib⟩
      · change w.length - 1 - l.val < w.length - 1 - j.val
        change j.val < l.val at hjl
        have h : l.val < w.length := by simpa only [rc_len] using l.isLt
        omega
      · change w.length - 1 - j.val < w.length - 1 - i.val
        change i.val < j.val at hij
        have h : j.val < w.length := by simpa only [rc_len] using j.isLt
        omega
      · change w[w.length - 1 - l.val] = 3 ∧ w[w.length - 1 - j.val] = 2 ∧
          w[w.length - 1 - i.val] = 1
        constructor
        · omega
        · constructor <;> omega
  have hdesc_snoc (v : List ℕ) (a b : ℕ) :
      descents (v ++ [a, b]) = descents (v ++ [a]) + if b < a then 1 else 0 := by
    induction v with
    | nil => rw [List.nil_append, List.nil_append, hdesc_cons]; simp only [descents, List.tail_cons, List.zip_nil_right, List.filter_nil, List.length_nil]; omega
    | cons c v ih =>
      cases v with
      | nil =>
        simp only [List.cons_append, List.nil_append]
        rw [hdesc_cons, hdesc_cons, hdesc_cons]
        simp only [descents, List.tail_cons, List.zip_nil_right, List.filter_nil, List.length_nil]
        omega
      | cons d v =>
        simp only [List.cons_append] at ih ⊢
        rw [hdesc_cons, hdesc_cons, ih]
        omega
  have rc_desc (w : List ℕ) (hw : ∀ x ∈ w, 1 ≤ x ∧ x ≤ 3) :
      descents (reverseComplement w) = descents w := by
    induction w with
    | nil => simp [reverseComplement, descents]
    | cons a v ih =>
      cases v with
      | nil => simp [reverseComplement, descents]
      | cons b v =>
        have ha := hw a (by simp)
        have hb := hw b (by simp)
        have hi := ih (fun x hx => hw x (List.mem_cons_of_mem a hx))
        have he : reverseComplement (a :: b :: v) = reverseComplement v ++ [4 - b, 4 - a] := by
          simp [reverseComplement]
        have he' : reverseComplement (b :: v) = reverseComplement v ++ [4 - b] := by
          simp [reverseComplement]
        rw [he, hdesc_snoc, ← he', hi, hdesc_cons]
        have hh : 4 - a < 4 - b ↔ b < a := by omega
        simp only [hh]
        omega
  have base_len : (oddOneBase t).length = 6 * t := by
    simp only [oddOneBase, List.length_append, pair_len]; omega
  have base_get (p : ℕ) (hp : p < (oddOneBase t).length) :
      (oddOneBase t)[p] =
        if p < 2 * t then (if p % 2 = 0 then 2 else 1)
        else if p < 4 * t - 2 then (if p % 2 = 0 then 3 else 1)
        else (if p % 2 = 0 then 3 else 2) := by
    simp only [oddOneBase, List.append_assoc]
    by_cases h1 : p < 2 * t
    · rw [List.getElem_append_left (by rw [pair_len]; exact h1), pair_get]
      simp only [if_pos h1]
    · rw [List.getElem_append_right (by rw [pair_len]; omega)]
      simp only [pair_len]
      by_cases h2 : p < 4 * t - 2
      · rw [List.getElem_append_left (by rw [pair_len]; omega), pair_get]
        rw [show (p - 2 * t) % 2 = p % 2 by omega]
        simp only [if_neg h1, if_pos h2]
      · rw [List.getElem_append_right (by rw [pair_len]; omega)]
        simp only [pair_len]
        rw [pair_get, show (p - 2 * t - 2 * (t - 1)) % 2 = p % 2 by omega]
        simp only [if_neg h1, if_neg h2]
  have one_len (q : Fin (2 * t)) : (oddOneWord t q).length = 6 * t + 3 := by
    have h := (one_adm q).1
    omega
  have one_get (q : Fin (2 * t)) (p : ℕ) (hp : p < (oddOneWord t q).length) :
      (oddOneWord t q)[p] =
        if p = 0 then 1 else if p ≤ 2 * q.val then
          (if p - 1 < 2 * t then (if (p - 1) % 2 = 0 then 2 else 1)
           else if p - 1 < 4 * t - 2 then (if (p - 1) % 2 = 0 then 3 else 1)
           else (if (p - 1) % 2 = 0 then 3 else 2))
        else if p = 2 * q.val + 1 then 1 else if p < 6 * t + 2 then
          (if p - 2 < 2 * t then (if (p - 2) % 2 = 0 then 2 else 1)
           else if p - 2 < 4 * t - 2 then (if (p - 2) % 2 = 0 then 3 else 1)
           else (if (p - 2) % 2 = 0 then 3 else 2))
        else 3 := by
    have hql : 2 * q.val ≤ (oddOneBase t).length := by rw [base_len]; have h := q.isLt; omega
    have htake : ((oddOneBase t).take (2 * q.val)).length = 2 * q.val := by
      simp only [List.length_take, Nat.min_eq_left hql]
    have hdrop : ((oddOneBase t).drop (2 * q.val)).length = 6 * t - 2 * q.val := by
      simp only [List.length_drop, base_len]
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hp]
    cases p with
    | zero => simp [oddOneWord]
    | succ p =>
      simp only [oddOneWord, List.append_assoc, List.singleton_append, List.cons_append,
        List.getElem?_cons_succ, List.nil_append]
      by_cases h1 : p < 2 * q.val
      · rw [List.getElem?_append_left (by rw [htake]; exact h1), List.getElem?_take_of_lt h1, List.getElem?_eq_getElem (by rw [base_len]; have h := q.isLt; omega), base_get]
        simp only [Nat.add_sub_cancel, show ¬ p + 1 = 0 by omega,
          show p + 1 ≤ 2 * q.val by omega, if_false, if_true]
      · rw [List.getElem?_append_right (by rw [htake]; omega)]
        simp only [htake]
        by_cases h2 : p = 2 * q.val
        · subst p
          simp only [Nat.sub_self, List.getElem?_cons_zero,
            show ¬ 2 * q.val + 1 = 0 by omega, show ¬ 2 * q.val + 1 ≤ 2 * q.val by omega,
            if_false, if_true]
        · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p - 2 * q.val ≠ 0)
          rw [hr, List.getElem?_cons_succ]
          have hr' : r = p - (2 * q.val + 1) := by omega
          by_cases h3 : p + 1 < 6 * t + 2
          · rw [List.getElem?_append_left (by rw [hdrop]; have h := q.isLt; omega), List.getElem?_drop]
            rw [show 2 * q.val + r = p - 1 by omega, List.getElem?_eq_getElem (by rw [base_len]; omega), base_get]
            simp only [show ¬ p + 1 = 0 by omega, show ¬ p + 1 ≤ 2 * q.val by omega,
              show ¬ p + 1 = 2 * q.val + 1 by omega, if_false, if_pos h3]
            congr 2 <;> omega
          · rw [List.getElem?_append_right (by rw [hdrop]; omega)]
            have hp' : p + 1 < 6 * t + 3 := by rw [one_len] at hp; exact hp
            rw [show r - ((oddOneBase t).drop (2 * q.val)).length = 0 by rw [hdrop]; omega]
            simp only [List.getElem?_cons_zero, show ¬ p + 1 = 0 by omega,
              show ¬ p + 1 ≤ 2 * q.val by omega, show ¬ p + 1 = 2 * q.val + 1 by omega,
              if_false, if_neg h3]
  have one_is1 (q : Fin (2 * t)) (p : ℕ) (hp : p < (oddOneWord t q).length) :
      (oddOneWord t q)[p] = 1 ↔ p = 0 ∨ p = 2 * q.val + 1 ∨
        (p ≤ 2 * q.val ∧ p % 2 = 0) ∨
        (2 * q.val + 1 < p ∧ p < 4 * t ∧ p % 2 = 1) := by
    rw [one_get q p hp]
    have hq := q.isLt
    rw [one_len] at hp
    split_ifs <;> omega
  have one_is3 (q : Fin (2 * t)) (p : ℕ) (hp : p < (oddOneWord t q).length) :
      (oddOneWord t q)[p] = 3 ↔
        (p ≤ 2 * q.val ∧ 2 * t < p ∧ p % 2 = 1) ∨
        (2 * q.val + 1 < p ∧ 2 * t + 1 < p ∧ p % 2 = 0) := by
    rw [one_get q p hp]
    have hq := q.isLt
    rw [one_len] at hp
    split_ifs <;> omega
  have one_marker (q : Fin (2 * t)) (p : ℕ) (hp : p + 1 < (oddOneWord t q).length) :
      ((oddOneWord t q)[p] = 1 ∧ (oddOneWord t q)[p + 1] = 1) ↔ p = 2 * q.val := by
    rw [one_is1 q p (by omega), one_is1 q (p + 1) hp]
    have hq := q.isLt
    rw [one_len] at hp
    omega
  have one_no33 (q : Fin (2 * t)) (p : ℕ) (hp : p + 1 < (oddOneWord t q).length) :
      ¬ ((oddOneWord t q)[p] = 3 ∧ (oddOneWord t q)[p + 1] = 3) := by
    rw [one_is3 q p (by omega), one_is3 q (p + 1) hp]
    have hq := q.isLt
    rw [one_len] at hp
    omega
  have pair_get_opt (a b n p : ℕ) :
      (pairBlocks a b n)[p]? = if p < 2 * n then some (if p % 2 = 0 then a else b) else none := by
    by_cases h : p < 2 * n
    · rw [List.getElem?_eq_getElem (by rw [pair_len]; exact h), pair_get]
      simp only [if_pos h]
    · rw [List.getElem?_eq_none (by rw [pair_len]; omega)]
      simp only [if_neg h]
  have two_len (late : Bool) : (oddTwoWord t late).length = 6 * t + 3 := by
    have h := (two_adm late).1
    omega
  have two_get (late : Bool) (p : ℕ) (hp : p < (oddTwoWord t late).length) :
      (oddTwoWord t late)[p] =
        if p = 0 then 1 else if p ≤ 2 * t then (if (p - 1) % 2 = 0 then 2 else 1)
        else if late then
          (if p ≤ 4 * t then (if (p - 1) % 2 = 0 then 3 else 1)
           else if p = 4 * t + 1 then 2
           else if p < 6 * t + 2 then (if p % 2 = 0 then 3 else 2) else 3)
        else
          (if p = 2 * t + 1 then 2
           else if p < 4 * t + 2 then (if p % 2 = 0 then 3 else 1)
           else if p < 6 * t + 2 then (if p % 2 = 0 then 3 else 2) else 3) := by
    have hp' : p < 6 * t + 3 := by rw [two_len] at hp; exact hp
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hp]
    cases late <;> simp only [oddTwoWord, Bool.false_eq_true, if_false, if_true,
      List.getElem?_append, List.length_append, List.length_singleton, pair_len,
      List.getElem?_cons, List.getElem?_nil, pair_get_opt]
    all_goals split_ifs <;> first | rfl | (congr 1 <;> omega) | omega
  have two_is1 (late : Bool) (p : ℕ) (hp : p < (oddTwoWord t late).length) :
      (oddTwoWord t late)[p] = 1 ↔
        if late then (p ≤ 4 * t ∧ p % 2 = 0)
        else (p ≤ 2 * t ∧ p % 2 = 0) ∨
          (2 * t + 1 < p ∧ p < 4 * t + 2 ∧ p % 2 = 1) := by
    rw [two_get late p hp]
    rw [two_len] at hp
    cases late <;> simp only [Bool.false_eq_true, if_false, if_true]
    all_goals split_ifs <;> omega
  have two_is3 (late : Bool) (p : ℕ) (hp : p < (oddTwoWord t late).length) :
      (oddTwoWord t late)[p] = 3 ↔
        if late then (2 * t < p ∧ p ≤ 4 * t ∧ p % 2 = 1) ∨
          (4 * t + 1 < p ∧ p % 2 = 0)
        else (2 * t + 1 < p ∧ p % 2 = 0) := by
    rw [two_get late p hp]
    rw [two_len] at hp
    cases late <;> simp only [Bool.false_eq_true, if_false, if_true]
    all_goals split_ifs <;> omega
  have two_nomarkers (late : Bool) (p : ℕ) (hp : p + 1 < (oddTwoWord t late).length) :
      ¬ ((oddTwoWord t late)[p] = 1 ∧ (oddTwoWord t late)[p + 1] = 1) ∧
      ¬ ((oddTwoWord t late)[p] = 3 ∧ (oddTwoWord t late)[p + 1] = 3) := by
    rw [two_is1 late p (by omega), two_is1 late (p + 1) hp,
      two_is3 late p (by omega), two_is3 late (p + 1) hp]
    rw [two_len] at hp
    cases late <;> simp only [Bool.false_eq_true, if_false, if_true]
    all_goals constructor <;> omega
  have one_inj : Function.Injective (oddOneWord t) := by
    intro q r he
    apply Fin.ext
    have hp : 2 * q.val + 1 < (oddOneWord t q).length := by rw [one_len]; have h := q.isLt; omega
    have hm := (one_marker q (2 * q.val) hp).mpr rfl
    have hp' : 2 * q.val + 1 < (oddOneWord t r).length := by rw [← he]; exact hp
    have hm' : (oddOneWord t r)[2 * q.val] = 1 ∧ (oddOneWord t r)[2 * q.val + 1] = 1 := by
      simpa only [he] using hm
    have hh := (one_marker r (2 * q.val) hp').mp hm'
    omega
  have rc_inj : Function.Injective (fun q : Fin (2 * t) => reverseComplement (oddOneWord t q)) := by
    intro q r h
    apply one_inj
    have h' := congrArg reverseComplement h
    rw [rc_involution _ (one_adm q).2.1, rc_involution _ (one_adm r).2.1] at h'
    exact h'
  have two_inj : Function.Injective (oddTwoWord t) := by
    intro a b he
    cases a <;> cases b
    all_goals try rfl
    all_goals
      have hpa : 2 * t + 1 < (oddTwoWord t false).length := by rw [two_len]; omega
      have hpb : 2 * t + 1 < (oddTwoWord t true).length := by rw [two_len]; omega
      have hfa := two_get false (2 * t + 1) hpa
      have htr := two_get true (2 * t + 1) hpb
      simp only [Bool.false_eq_true, if_false, if_true,
        show ¬ 2 * t + 1 = 0 by omega, show ¬ 2 * t + 1 ≤ 2 * t by omega,
        show 2 * t + 1 ≤ 4 * t by omega,
        show (2 * t + 1 - 1) % 2 = 0 by omega] at hfa htr
      have he' : oddTwoWord t false = oddTwoWord t true := by
        first | exact he | exact he.symm
      have hv := congrArg (fun w : List ℕ => w[2 * t + 1]?) he'
      rw [List.getElem?_eq_getElem hpa, List.getElem?_eq_getElem hpb, hfa, htr] at hv
      simp at hv
  have rc_no11 (q : Fin (2 * t)) (p : ℕ)
      (hp : p + 1 < (reverseComplement (oddOneWord t q)).length) :
      ¬ ((reverseComplement (oddOneWord t q))[p] = 1 ∧
        (reverseComplement (oddOneWord t q))[p + 1] = 1) := by
    intro h
    rw [rc_get _ p (by omega), rc_get _ (p + 1) hp] at h
    have hp' : p + 1 < (oddOneWord t q).length := by rw [rc_len] at hp; exact hp
    let n := (oddOneWord t q).length - 2 - p
    have hn : n + 1 < (oddOneWord t q).length := by dsimp [n]; omega
    have he1 : (oddOneWord t q).length - 1 - p = n + 1 := by dsimp [n]; omega
    have he2 : (oddOneWord t q).length - 1 - (p + 1) = n := by dsimp [n]; omega
    simp only [he1, he2] at h
    have ha := (one_adm q).2.1 _ (List.getElem_mem (by omega : n < (oddOneWord t q).length))
    have hb := (one_adm q).2.1 _ (List.getElem_mem hn)
    apply one_no33 q n hn
    constructor <;> omega
  have rc_has33 (q : Fin (2 * t)) :
      ∃ p, ∃ hp : p + 1 < (reverseComplement (oddOneWord t q)).length,
        (reverseComplement (oddOneWord t q))[p] = 3 ∧
          (reverseComplement (oddOneWord t q))[p + 1] = 3 := by
    let p := 6 * t + 1 - 2 * q.val
    have hp : p + 1 < (reverseComplement (oddOneWord t q)).length := by
      rw [rc_len, one_len]; dsimp [p]; have hq := q.isLt; omega
    refine ⟨p, hp, ?_⟩
    have hq := q.isLt
    have hmark := (one_marker q (2 * q.val) (by rw [one_len]; omega)).mpr rfl
    rw [rc_get _ p (by omega), rc_get _ (p + 1) hp]
    have he1 : (oddOneWord t q).length - 1 - p = 2 * q.val + 1 := by
      rw [one_len]; dsimp [p]; omega
    have he2 : (oddOneWord t q).length - 1 - (p + 1) = 2 * q.val := by
      rw [one_len]; dsimp [p]; omega
    simp only [he1, he2, hmark.1, hmark.2]
    decide
  have one_rc_ne (q r : Fin (2 * t)) :
      oddOneWord t q ≠ reverseComplement (oddOneWord t r) := by
    intro he
    have hp : 2 * q.val + 1 < (oddOneWord t q).length := by rw [one_len]; have h := q.isLt; omega
    have hm := (one_marker q (2 * q.val) hp).mpr rfl
    have hp' : 2 * q.val + 1 < (reverseComplement (oddOneWord t r)).length := by rw [← he]; exact hp
    apply rc_no11 r (2 * q.val) hp'
    simpa only [he] using hm
  have one_two_ne (q : Fin (2 * t)) (b : Bool) : oddOneWord t q ≠ oddTwoWord t b := by
    intro he
    have hp : 2 * q.val + 1 < (oddOneWord t q).length := by rw [one_len]; have h := q.isLt; omega
    have hm := (one_marker q (2 * q.val) hp).mpr rfl
    have hp' : 2 * q.val + 1 < (oddTwoWord t b).length := by rw [← he]; exact hp
    apply (two_nomarkers b (2 * q.val) hp').1
    simpa only [he] using hm
  have rc_two_ne (q : Fin (2 * t)) (b : Bool) :
      reverseComplement (oddOneWord t q) ≠ oddTwoWord t b := by
    intro he
    obtain ⟨p, hp, hm⟩ := rc_has33 q
    have hp' : p + 1 < (oddTwoWord t b).length := by rw [← he]; exact hp
    apply (two_nomarkers b p hp').2
    simpa only [he] using hm
  constructor
  · intro i j he
    cases i with
    | inl i =>
      cases i with
      | inl q =>
        cases j with
        | inl j =>
          cases j with
          | inl r => exact congrArg (fun x => Sum.inl (Sum.inl x)) (one_inj he)
          | inr r => exact False.elim (one_rc_ne q r he)
        | inr b => exact False.elim (one_two_ne q b he)
      | inr q =>
        cases j with
        | inl j =>
          cases j with
          | inl r => exact False.elim (one_rc_ne r q he.symm)
          | inr r => exact congrArg (fun x => Sum.inl (Sum.inr x)) (rc_inj he)
        | inr b => exact False.elim (rc_two_ne q b he)
    | inr a =>
      cases j with
      | inl j =>
        cases j with
        | inl q => exact False.elim (one_two_ne q a he.symm)
        | inr q => exact False.elim (rc_two_ne q a he.symm)
      | inr b => exact congrArg Sum.inr (two_inj he)
  · intro i
    have hv : extremalValue (2 * t + 1) = 3 * t := by unfold extremalValue; omega
    cases i with
    | inl i =>
      cases i with
      | inl q => exact ⟨hcarrier _ _ (one_adm q), (one_desc q).trans hv.symm⟩
      | inr q => exact ⟨hcarrier _ _ (rc_adm _ _ (one_adm q)),
          ((rc_desc _ (one_adm q).2.1).trans (one_desc q)).trans hv.symm⟩
    | inr b => exact ⟨hcarrier _ _ (two_adm b), (two_desc b).trans hv.symm⟩

#print axioms odd_word_construction

end D5.S3.Combinatorics.ShankarWords.OddWordConstruction
