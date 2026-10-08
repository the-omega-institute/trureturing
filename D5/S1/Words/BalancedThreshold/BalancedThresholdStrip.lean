/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdStrip
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdStrip
   mirror-E: none(waiver:strict-bispecial-displacement-strip)
   anchors: []
   utility: none
   digest: Bispecial descent bounds every displacement by two distinct return discrepancies. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdDescent
import D5.S1.Words.Mechanical.MechanicalDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- The strict strip is measured by actual physical returns. Descent scales all three
errors by the same positive factor; complementation preserves their absolute values. -/
theorem mechanical_bispecial_strip {alpha : ℝ} (h0 : 0 < alpha) (h1 : alpha < 1)
    (hirr : Irrational alpha) {n : ℕ} (w : Fin n → Bool)
    (hw : BispecialFactor (lowerMechanicalWord alpha alpha) w) :
    let u := lowerMechanicalWord alpha alpha
    ∀ i j a b c d : ℕ, i < j → wordFactor u n i = w → wordFactor u n j = w →
      AdjacentOccurrences u w a b → AdjacentOccurrences u w c d →
      List.ofFn (wordFactor u (b - a) a) ≠ List.ofFn (wordFactor u (d - c) c) →
      |(lowerMechanicalWindowTrueCount alpha alpha i (j - i) : ℝ) -
        alpha * (j - i : ℕ)| <
      |(lowerMechanicalWindowTrueCount alpha alpha a (b - a) : ℝ) -
        alpha * (b - a : ℕ)| +
      |(lowerMechanicalWindowTrueCount alpha alpha c (d - c) : ℝ) -
        alpha * (d - c : ℕ)| := by
  classical
  have window : ∀ (gamma : ℝ) (i m : ℕ),
      (List.ofFn (wordFactor (lowerMechanicalWord gamma gamma) m i)).count true =
        lowerMechanicalWindowTrueCount gamma gamma i m := by
    intro gamma i m
    induction m with
    | zero => simp [lowerMechanicalWindowTrueCount]
    | succ m hm =>
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append, List.count_append, List.count_singleton,
        wordFactor, Fin.val_last]
      rw [show (fun k : Fin m => lowerMechanicalWord gamma gamma (i + k.castSucc)) =
        wordFactor (lowerMechanicalWord gamma gamma) m i from rfl, hm]
      simp only [lowerMechanicalWindowTrueCount, Finset.range_add_one,
        Finset.filter_insert]
      by_cases hu : lowerMechanicalWord gamma gamma (i + m) = true
      · simp [hu, Finset.mem_filter, Finset.mem_range]
      · simp [hu]
  induction n using Nat.strong_induction_on generalizing alpha with
  | h n ih =>
    dsimp only
    by_cases hn : n = 0
    · subst n
      intro i j a b c d hij hi hj hab hcd hne
      have step : ∀ a b, AdjacentOccurrences (lowerMechanicalWord alpha alpha) w a b →
          b - a = 1 := by
        intro a b h
        by_contra he
        have hlt := h.1
        exact h.2.2.2 (a + 1) (by omega) (by omega) (Subsingleton.elim _ _)
      have hab1 := step a b hab
      have hcd1 := step c d hcd
      rw [hab1, hcd1] at hne ⊢
      have distinct : lowerMechanicalWord alpha alpha a ≠
          lowerMechanicalWord alpha alpha c := by
        simpa [List.ofFn_succ, wordFactor] using hne
      have sum :
          |(lowerMechanicalWindowTrueCount alpha alpha a 1 : ℝ) - alpha| +
          |(lowerMechanicalWindowTrueCount alpha alpha c 1 : ℝ) - alpha| = 1 := by
        rw [← window alpha a 1, ← window alpha c 1]
        simp only [List.ofFn_succ, List.ofFn_zero, wordFactor]
        cases ha : lowerMechanicalWord alpha alpha a <;>
          cases hc : lowerMechanicalWord alpha alpha c <;>
          simp [ha, hc] at distinct
        all_goals
          simp only [List.count_cons, List.count_nil]
          norm_num
          rw [abs_of_pos h0, abs_of_pos (by linarith : 0 < 1 - alpha)]
          ring
      simpa only [sum, Nat.cast_one, mul_one, mul_comm] using
        lower_mechanical_window_true_discrepancy (rho := alpha) h0.le h1 i (j - i)
    have small : ∀ {gamma : ℝ}, 0 < gamma → gamma < 1 / 2 → Irrational gamma →
        ∀ (v : Fin n → Bool), BispecialFactor (lowerMechanicalWord gamma gamma) v →
        ∀ i j a b c d : ℕ, i < j →
          wordFactor (lowerMechanicalWord gamma gamma) n i = v →
          wordFactor (lowerMechanicalWord gamma gamma) n j = v →
          AdjacentOccurrences (lowerMechanicalWord gamma gamma) v a b →
          AdjacentOccurrences (lowerMechanicalWord gamma gamma) v c d →
          List.ofFn (wordFactor (lowerMechanicalWord gamma gamma) (b - a) a) ≠
            List.ofFn (wordFactor (lowerMechanicalWord gamma gamma) (d - c) c) →
          |(lowerMechanicalWindowTrueCount gamma gamma i (j - i) : ℝ) -
            gamma * (j - i : ℕ)| <
          |(lowerMechanicalWindowTrueCount gamma gamma a (b - a) : ℝ) -
            gamma * (b - a : ℕ)| +
          |(lowerMechanicalWindowTrueCount gamma gamma c (d - c) : ℝ) -
            gamma * (d - c : ℕ)| := by
      intro gamma hg0 hghalf hgi v hv i j a b c d hij hi hj hab hcd hne
      let theta := gamma / (1 - gamma)
      let u := lowerMechanicalWord gamma gamma
      let u' := lowerMechanicalWord theta theta
      let pos := Nat.nth (fun k => u k = false)
      let enc := fun l : List Bool => l.flatMap
        (fun z => if z then [false, true] else [false])
      have ht0 : 0 < theta := div_pos hg0 (by linarith)
      have ht1 : theta < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      have hti : Irrational theta := by
        have he : theta = 1 / (1 / gamma - 1) := by dsimp [theta]; field_simp
        rw [he]
        simpa [one_div] using (hgi.inv.sub_ratCast 1).inv
      obtain ⟨m, z, hmn, hz, _, hocc, _⟩ :=
        mechanical_bispecial_descent hg0 hghalf (by omega) v hv
      have source := mechanical_majority_desubstitution hg0 hghalf
      have infinite : (Set.ofPred (fun k => u k = false)).Infinite := by
        intro hf
        have he := Nat.nth_of_card_le hf (n := hf.toFinset.card + 1) (by omega)
        change pos (hf.toFinset.card + 1) = 0 at he
        have hp := (source (hf.toFinset.card + 1)).1
        change pos (hf.toFinset.card + 1) = _ at hp
        omega
      have mono : StrictMono pos := Nat.nth_strictMono infinite
      have hprefix : ∀ k,
          List.ofFn (wordFactor u (pos k) 0) = enc (List.ofFn (wordFactor u' k 0)) := by
        intro k
        rw [(source k).2]
        have he : List.ofFn (wordFactor u' k 0) = (List.range k).map u' := by
          rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
          congr 1
          funext r
          simp [wordFactor]
        rw [he]
        simp only [enc, List.flatMap_map]
        rfl
      have split : ∀ (x : ℕ → Bool) a b i,
          List.ofFn (wordFactor x (a + b) i) =
            List.ofFn (wordFactor x a i) ++ List.ofFn (wordFactor x b (i + a)) := by
        intro x a b i
        rw [List.ofFn_add]
        congr 1
        apply congrArg List.ofFn
        funext k
        simp [wordFactor, Nat.add_assoc]
      have interval : ∀ k l, k ≤ l →
          List.ofFn (wordFactor u (pos l - pos k) (pos k)) =
            enc (List.ofFn (wordFactor u' (l - k) k)) := by
        intro k l hkl
        have hp := mono.monotone hkl
        have he := hprefix l
        rw [← Nat.add_sub_of_le hp, split, hprefix k] at he
        conv_rhs at he => rw [← Nat.add_sub_of_le hkl, split]
        simp only [enc, List.flatMap_append, zero_add] at he
        exact List.append_cancel_left he
      have counts : ∀ l : List Bool,
          (enc l).count true = l.count true ∧ (enc l).length = l.length + l.count true := by
        intro l
        induction l with
        | nil => simp [enc]
        | cons x l hl => cases x <;> simp [enc] at * <;> omega
      have error : ∀ k l, k ≤ l →
          (lowerMechanicalWindowTrueCount gamma gamma (pos k) (pos l - pos k) : ℝ) -
              gamma * (pos l - pos k : ℕ) =
            (1 - gamma) *
              ((lowerMechanicalWindowTrueCount theta theta k (l - k) : ℝ) -
                theta * (l - k : ℕ)) := by
        intro k l hkl
        have he := interval k l hkl
        have hc := congrArg (List.count true) he
        rw [(counts _).1, window, window] at hc
        have hl := congrArg List.length he
        rw [(counts _).2, List.length_ofFn, List.length_ofFn, window] at hl
        have hlR := congrArg (fun a : ℕ => (a : ℝ)) hl
        push_cast at hlR
        rw [hc, hlR]
        dsimp [theta]
        field_simp [ne_of_gt (by linarith : 0 < 1 - gamma)]
        ring
      obtain ⟨ki, hki, hzi⟩ := (hocc i).mp hi
      obtain ⟨kj, hkj, hzj⟩ := (hocc j).mp hj
      obtain ⟨ka, hka, hza⟩ := (hocc a).mp hab.2.1
      obtain ⟨kb, hkb, hzb⟩ := (hocc b).mp hab.2.2.1
      obtain ⟨kc, hkc, hzc⟩ := (hocc c).mp hcd.2.1
      obtain ⟨kd, hkd, hzd⟩ := (hocc d).mp hcd.2.2.1
      change pos ki = i at hki
      change pos kj = j at hkj
      change pos ka = a at hka
      change pos kb = b at hkb
      change pos kc = c at hkc
      change pos kd = d at hkd
      have adj : ∀ a b ka kb, pos ka = a → pos kb = b →
          wordFactor u' m ka = z → wordFactor u' m kb = z →
          AdjacentOccurrences u v a b → AdjacentOccurrences u' z ka kb := by
        intro a b ka kb ha hb hza hzb hab
        refine ⟨(mono.lt_iff_lt).mp (by simpa [ha, hb] using hab.1), hza, hzb, ?_⟩
        intro k hak hkb hk
        exact hab.2.2.2 (pos k) (by simpa [ha] using mono hak)
          (by simpa [hb] using mono hkb) ((hocc _).mpr ⟨k, rfl, hk⟩)
      have hab' := adj a b ka kb hka hkb hza hzb hab
      have hcd' := adj c d kc kd hkc hkd hzc hzd hcd
      have hij' : ki < kj := (mono.lt_iff_lt).mp (by simpa [hki, hkj] using hij)
      have hne' : List.ofFn (wordFactor u' (kb - ka) ka) ≠
          List.ofFn (wordFactor u' (kd - kc) kc) := by
        intro he
        apply hne
        rw [← hka, ← hkb, ← hkc, ← hkd, interval _ _ hab'.1.le,
          interval _ _ hcd'.1.le, he]
      have bound := ih m hmn ht0 ht1 hti z hz ki kj ka kb kc kd
        hij' hzi hzj hab' hcd' hne'
      rw [← hki, ← hkj, ← hka, ← hkb, ← hkc, ← hkd,
        error _ _ hij'.le, error _ _ hab'.1.le, error _ _ hcd'.1.le]
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 - gamma)]
      exact (mul_lt_mul_of_pos_left bound (by linarith)).trans_eq (by ring)
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
      rcases lowerMechanicalLetter_eq_zero_or_one (rho := alpha) h0.le h1 i with hz | ho
      · simp [lowerMechanicalWord, he, hz]
      · simp [lowerMechanicalWord, he, ho]
    let v : Fin n → Bool := fun k => !(w k)
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
    have factors : ∀ a i, List.ofFn (wordFactor (lowerMechanicalWord beta beta) a i) =
        (List.ofFn (wordFactor (lowerMechanicalWord alpha alpha) a i)).map Bool.not := by
      intro a i
      rw [← List.ofFn_comp']
      congr 1
      funext k
      exact complement (i + k)
    have error : ∀ i m,
        |(lowerMechanicalWindowTrueCount beta beta i m : ℝ) - beta * (m : ℝ)| =
          |(lowerMechanicalWindowTrueCount alpha alpha i m : ℝ) - alpha * (m : ℝ)| := by
      intro i m
      have hc := factors m i
      have hl : ∀ l : List Bool, (l.map Bool.not).count true + l.count true = l.length := by
        intro l
        induction l with
        | nil => simp
        | cons x l hl => cases x <;> simp at * <;> omega
      have he := hl (List.ofFn (wordFactor (lowerMechanicalWord alpha alpha) m i))
      rw [← hc, window, window, List.length_ofFn] at he
      have heR := congrArg (fun k : ℕ => (k : ℝ)) he
      push_cast at heR
      have he' : (lowerMechanicalWindowTrueCount beta beta i m : ℝ) - beta * m =
          -((lowerMechanicalWindowTrueCount alpha alpha i m : ℝ) - alpha * m) := by
        dsimp [beta]
        linarith
      rw [he', abs_neg]
    intro i j a b c d hij hi hj hab hcd hne
    have adj : ∀ a b, AdjacentOccurrences (lowerMechanicalWord alpha alpha) w a b →
        AdjacentOccurrences (lowerMechanicalWord beta beta) v a b := by
      intro a b h
      refine ⟨h.1, (occ a).mpr h.2.1, (occ b).mpr h.2.2.1, ?_⟩
      intro k hak hkb hk
      exact h.2.2.2 k hak hkb ((occ k).mp hk)
    have hne' : List.ofFn (wordFactor (lowerMechanicalWord beta beta) (b - a) a) ≠
        List.ofFn (wordFactor (lowerMechanicalWord beta beta) (d - c) c) := by
      intro he
      apply hne
      rw [factors, factors] at he
      have he' := congrArg (List.map Bool.not) he
      simpa [List.map_map, Function.comp_def] using he'
    have bound := small hb0 hbhalf hbi v hv i j a b c d hij
      ((occ i).mpr hi) ((occ j).mpr hj) (adj a b hab) (adj c d hcd) hne'
    simpa only [error] using bound

end D5.S1.Words.BalancedThreshold
