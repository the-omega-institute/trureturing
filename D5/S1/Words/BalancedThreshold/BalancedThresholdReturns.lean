/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdReturns
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdReturns
   mirror-E: none(waiver:mechanical-unimodular-return-classification)
   anchors: []
   utility: none
   digest: Length induction classifies bispecial returns and their unimodular Parikh vectors. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- Descent and complementation construct two unimodular candidates for every adjacent
return, with the exact factor-count identity. Both candidates need not be realized. -/
theorem mechanical_bispecial_returns {alpha : ℝ} (h0 : 0 < alpha) (h1 : alpha < 1)
    (hirr : Irrational alpha) {n : ℕ} (w : Fin n → Bool)
    (hw : BispecialFactor (lowerMechanicalWord alpha alpha) w) :
    ∃ r s : List Bool,
      0 < r.length ∧ 0 < s.length ∧
      (r.count true * s.count false + 1 = s.count true * r.count false ∨
        s.count true * r.count false + 1 = r.count true * s.count false) ∧
      (∀ b, r.count b + s.count b = (List.ofFn w).count b + 1) ∧
      ∀ i j, AdjacentOccurrences (lowerMechanicalWord alpha alpha) w i j →
        List.ofFn (wordFactor (lowerMechanicalWord alpha alpha) (j - i) i) = r ∨
        List.ofFn (wordFactor (lowerMechanicalWord alpha alpha) (j - i) i) = s := by
  classical
  induction n using Nat.strong_induction_on generalizing alpha with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨[false], [true], by simp, by simp, Or.inl (by simp), ?_, ?_⟩
      · intro b
        cases b <;> simp
      · intro i j hj
        have hij := hj.1
        have he : j = i + 1 := by
          by_contra hne
          have hk : i + 1 < j := by omega
          exact hj.2.2.2 (i + 1) (by omega) hk (Subsingleton.elim _ _)
        rw [he, Nat.add_sub_cancel_left]
        simp only [List.ofFn_succ, List.ofFn_zero, wordFactor]
        cases lowerMechanicalWord alpha alpha i <;> simp
    have hnpos : 0 < n := by omega
    have small : ∀ {beta : ℝ}, 0 < beta → beta < 1 / 2 → Irrational beta →
        ∀ (v : Fin n → Bool), BispecialFactor (lowerMechanicalWord beta beta) v →
        ∃ r s : List Bool,
          0 < r.length ∧ 0 < s.length ∧
          (r.count true * s.count false + 1 = s.count true * r.count false ∨
            s.count true * r.count false + 1 = r.count true * s.count false) ∧
          (∀ b, r.count b + s.count b = (List.ofFn v).count b + 1) ∧
          ∀ i j, AdjacentOccurrences (lowerMechanicalWord beta beta) v i j →
            List.ofFn (wordFactor (lowerMechanicalWord beta beta) (j - i) i) = r ∨
            List.ofFn (wordFactor (lowerMechanicalWord beta beta) (j - i) i) = s := by
      intro beta hb0 hbhalf hbi v hv
      let theta := beta / (1 - beta)
      let u := lowerMechanicalWord beta beta
      let u' := lowerMechanicalWord theta theta
      let pos := Nat.nth (fun i => u i = false)
      let block := fun b : Bool => if b then [false, true] else [false]
      let enc := fun l : List Bool => l.flatMap block
      have ht0 : 0 < theta := div_pos hb0 (by linarith)
      have ht1 : theta < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      have hti : Irrational theta := by
        have he : theta = 1 / (1 / beta - 1) := by
          dsimp [theta]
          field_simp
        rw [he]
        simpa [one_div] using (hbi.inv.sub_ratCast 1).inv
      obtain ⟨m, z, hmn, hz, hcode, hocc, _⟩ :=
        mechanical_bispecial_descent hb0 hbhalf hnpos v hv
      obtain ⟨r, s, hr, hs, hdet, hcounts, hreturns⟩ := ih m hmn ht0 ht1 hti z hz
      have counts : ∀ l : List Bool,
          (enc l).count true = l.count true ∧
          (enc l).count false = l.count true + l.count false ∧
          l.length ≤ (enc l).length := by
        intro l
        induction l with
        | nil => simp [enc]
        | cons b l hl =>
          cases b <;> simp [enc, block] at * <;> omega
      have position := mechanical_majority_desubstitution hb0 hbhalf
      have infinite : (Set.ofPred (fun i => u i = false)).Infinite := by
        intro hf
        have he := Nat.nth_of_card_le hf (n := hf.toFinset.card + 1) (by omega)
        change pos (hf.toFinset.card + 1) = 0 at he
        have hp : pos (hf.toFinset.card + 1) =
            hf.toFinset.card + 1 +
              (⌊((hf.toFinset.card + 2 : ℕ) : ℝ) * theta⌋).toNat :=
          (position _).1
        omega
      have mono : StrictMono pos := Nat.nth_strictMono infinite
      have split : ∀ (x : ℕ → Bool) a b i,
          List.ofFn (wordFactor x (a + b) i) =
            List.ofFn (wordFactor x a i) ++ List.ofFn (wordFactor x b (i + a)) := by
        intro x a b i
        rw [List.ofFn_add]
        congr 1
        apply congrArg List.ofFn
        funext k
        simp [wordFactor, Nat.add_assoc]
      have interval : ∀ k l,
          List.ofFn (wordFactor u (pos l - pos k) (pos k)) =
            enc (List.ofFn (wordFactor u' (l - k) k)) := by
        intro k l
        by_cases hkl : k ≤ l
        · have hp : pos k ≤ pos l := mono.monotone hkl
          have he := (position l).2
          change List.ofFn (wordFactor u (pos l) 0) =
            (List.range l).flatMap (fun i => block (u' i)) at he
          have hk := (position k).2
          change List.ofFn (wordFactor u (pos k) 0) =
            (List.range k).flatMap (fun i => block (u' i)) at hk
          rw [← Nat.add_sub_of_le hp, split, hk] at he
          have hprefix : ∀ a,
              (List.range a).flatMap (fun i => block (u' i)) =
                enc (List.ofFn (wordFactor u' a 0)) := by
            intro a
            simp only [enc, List.ofFn_eq_map, wordFactor, Nat.zero_add,
              ← List.map_coe_finRange_eq_range, List.flatMap_map]
          rw [hprefix, hprefix, ← Nat.add_sub_of_le hkl, split] at he
          simp only [enc, List.flatMap_append, Nat.zero_add, Nat.add_sub_of_le hkl] at he
          exact List.append_cancel_left he
        · have hp : pos l ≤ pos k := mono.monotone (by omega)
          simp [Nat.sub_eq_zero_of_le hp, Nat.sub_eq_zero_of_le (by omega : l ≤ k),
            enc]
      refine ⟨enc r, enc s, lt_of_lt_of_le hr (counts r).2.2,
        lt_of_lt_of_le hs (counts s).2.2, ?_, ?_, ?_⟩
      · rw [(counts r).1, (counts s).1, (counts r).2.1, (counts s).2.1]
        rcases hdet with hd | hd
        · left
          nlinarith only [hd]
        · right
          nlinarith only [hd]
      · intro b
        change List.ofFn v = enc (List.ofFn z) ++ [false] at hcode
        rw [hcode]
        cases b with
        | false =>
          simp only [List.count_append, List.count_singleton, beq_self_eq_true,
            ↓reduceIte, (counts r).2.1, (counts s).2.1, (counts (List.ofFn z)).2.1]
          have ht := hcounts true
          have hf := hcounts false
          omega
        | true =>
          simp only [List.count_append, List.count_singleton, (counts r).1, (counts s).1,
            (counts (List.ofFn z)).1]
          exact hcounts true
      · intro i j hij
        obtain ⟨ki, hki, hzi⟩ := (hocc i).mp hij.2.1
        obtain ⟨kj, hkj, hzj⟩ := (hocc j).mp hij.2.2.1
        change pos ki = i at hki
        change pos kj = j at hkj
        have hlt : ki < kj := (mono.lt_iff_lt).mp (by simpa [hki, hkj] using hij.1)
        have hadj : AdjacentOccurrences u' z ki kj := by
          refine ⟨hlt, hzi, hzj, ?_⟩
          intro k hik hkj' hk
          exact hij.2.2.2 (pos k) (by simpa [hki] using mono hik)
            (by simpa [hkj] using mono hkj') ((hocc _).mpr ⟨k, rfl, hk⟩)
        have he := interval ki kj
        rw [hki, hkj] at he
        change List.ofFn (wordFactor u (j - i) i) = enc r ∨
          List.ofFn (wordFactor u (j - i) i) = enc s
        rw [he]
        exact (hreturns ki kj hadj).imp (congrArg enc) (congrArg enc)
    by_cases hhalf : alpha < 1 / 2
    · exact small h0 hhalf hirr w hw
    let beta := 1 - alpha
    have hb0 : 0 < beta := by dsimp [beta]; linarith
    have hbhalf : beta < 1 / 2 := by
      have hne := hirr.ne_rat (1 / 2)
      norm_num at hne
      dsimp [beta]
      rcases lt_or_eq_of_le (le_of_not_gt hhalf) with hlt | heq
      · linarith
      · exact (hne heq.symm).elim
    have hbi : Irrational beta := by simpa [beta] using hirr.ratCast_sub 1
    have complement : ∀ i, lowerMechanicalWord beta beta i =
        !(lowerMechanicalWord alpha alpha i) := by
      intro i
      have floor : ∀ k : ℕ, 0 < k →
          ⌊(k : ℝ) * beta⌋ = k - ⌊(k : ℝ) * alpha⌋ - 1 := by
        intro k hk
        have hi := hirr.natCast_mul (by omega : k ≠ 0)
        have hc := (Int.ceil_eq_floor_add_one_iff_notMem ((k : ℝ) * alpha)).mpr ?_
        · rw [show (k : ℝ) * beta = (k : ℝ) + -((k : ℝ) * alpha) by
            dsimp [beta]; ring, Int.floor_natCast_add, Int.floor_neg, hc]
          omega
        · rintro ⟨z, hz⟩
          exact hi.ne_int z hz.symm
      have he : lowerMechanicalLetter beta beta i =
          1 - lowerMechanicalLetter alpha alpha i := by
        unfold lowerMechanicalLetter
        rw [show beta + ((i + 1 : ℕ) : ℝ) * beta = ((i + 2 : ℕ) : ℝ) * beta by
            push_cast; ring,
          show beta + (i : ℝ) * beta = ((i + 1 : ℕ) : ℝ) * beta by
            push_cast; ring, floor _ (by omega), floor _ (by omega)]
        rw [show alpha + ((i + 1 : ℕ) : ℝ) * alpha =
            ((i + 2 : ℕ) : ℝ) * alpha by push_cast; ring,
          show alpha + (i : ℝ) * alpha = ((i + 1 : ℕ) : ℝ) * alpha by
            push_cast; ring]
        push_cast
        ring
      have hbit := lowerMechanicalLetter_eq_zero_or_one (rho := alpha) h0.le h1 i
      rcases hbit with hz | ho
      · simp [lowerMechanicalWord, he, hz]
      · simp [lowerMechanicalWord, he, ho]
    let v : Fin n → Bool := fun k => !(w k)
    have factors : ∀ a i, List.ofFn (wordFactor (lowerMechanicalWord beta beta) a i) =
        (List.ofFn (wordFactor (lowerMechanicalWord alpha alpha) a i)).map Bool.not := by
      intro a i
      rw [← List.ofFn_comp']
      congr 1
      funext k
      exact complement (i + k)
    have occ : ∀ i, wordFactor (lowerMechanicalWord beta beta) n i = v ↔
        wordFactor (lowerMechanicalWord alpha alpha) n i = w := by
      intro i
      constructor <;> intro he <;> funext k
      · have hh := congrFun he k
        simpa [wordFactor, complement, v] using congrArg Bool.not hh
      · simpa [wordFactor, complement, v] using congrArg Bool.not (congrFun he k)
    have hv : BispecialFactor (lowerMechanicalWord beta beta) v := by
      constructor
      · obtain ⟨i, j, hi, hj, hwi, hwj, hne⟩ := hw.1
        refine ⟨i, j, hi, hj, (occ i).mpr hwi, (occ j).mpr hwj, ?_⟩
        intro he
        apply hne
        simpa [complement] using congrArg Bool.not he
      · obtain ⟨i, j, hwi, hwj, hne⟩ := hw.2
        refine ⟨i, j, (occ i).mpr hwi, (occ j).mpr hwj, ?_⟩
        intro he
        apply hne
        simpa [complement] using congrArg Bool.not he
    obtain ⟨r, s, hr, hs, hd, hc, ht⟩ := small hb0 hbhalf hbi v hv
    have counts : ∀ l : List Bool, ∀ b, (l.map Bool.not).count b = l.count (!b) := by
      intro l b
      have he := List.count_map_of_injective l Bool.not
        (by intro a b he; simpa using congrArg Bool.not he) (!b)
      simpa using he
    have hvlist : List.ofFn v = (List.ofFn w).map Bool.not := by
      rw [← List.ofFn_comp']
    refine ⟨r.map Bool.not, s.map Bool.not, by simpa using hr, by simpa using hs,
      ?_, ?_, ?_⟩
    · simp only [counts, Bool.not_true, Bool.not_false]
      rcases hd with hd | hd
      · exact Or.inr (by simpa [Nat.mul_comm] using hd)
      · exact Or.inl (by simpa [Nat.mul_comm] using hd)
    · intro b
      rw [counts, counts]
      have he := hc (!b)
      rw [hvlist, counts, Bool.not_not] at he
      exact he
    · intro i j hij
      have ha : AdjacentOccurrences (lowerMechanicalWord beta beta) v i j := by
        refine ⟨hij.1, (occ i).mpr hij.2.1, (occ j).mpr hij.2.2.1, ?_⟩
        intro k hik hkj hk
        exact hij.2.2.2 k hik hkj ((occ k).mp hk)
      have he := factors (j - i) i
      have hmap := (ht i j ha).imp
        (congrArg (List.map Bool.not)) (congrArg (List.map Bool.not))
      rw [he, List.map_map] at hmap
      simpa [Function.comp_def] using hmap

end D5.S1.Words.BalancedThreshold
