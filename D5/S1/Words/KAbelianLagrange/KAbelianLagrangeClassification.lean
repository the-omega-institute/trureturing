/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeClassification
   generality: I
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeClassification
   mirror-E: none(waiver:sturmian-extension-reconstruction)
   anchors: []
   utility: none
   digest: A unique right-special factor reconstructs all counts from letters and boundaries. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeExtensionMass
import D5.S1.Words.Mechanical.MechanicalRightSpecial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open KAbelianLagrangeDefs D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalRightSpecial

/-- Letter counts and the two boundaries suffice for actual irrational mechanical factors. -/
theorem mechanical_kabelian_of_boundaries {alpha rho : ℝ}
    (h0 : 0 ≤ alpha) (h1 : alpha < 1) (hirr : Irrational alpha)
    (k m i j : ℕ)
    (hab : KAbelianEq 1 (lowerMechanicalFactor alpha rho m i)
      (lowerMechanicalFactor alpha rho m j))
    (hpre : (lowerMechanicalFactor alpha rho m i).take (k - 1) =
      (lowerMechanicalFactor alpha rho m j).take (k - 1))
    (hsuf : (lowerMechanicalFactor alpha rho m i).drop (m - (k - 1)) =
      (lowerMechanicalFactor alpha rho m j).drop (m - (k - 1))) :
    KAbelianEq k (lowerMechanicalFactor alpha rho m i)
      (lowerMechanicalFactor alpha rho m j) := by
  classical
  let u := lowerMechanicalFactor alpha rho m i
  let v := lowerMechanicalFactor alpha rho m j
  have hu : u.length = m := by simp [u, lowerMechanicalFactor]
  have hv : v.length = m := by simp [v, lowerMechanicalFactor]
  by_cases hmk : m ≤ k - 1
  · have heq : u = v := by
      change u.take (k - 1) = v.take (k - 1) at hpre
      simpa only [List.take_of_length_le (hu.le.trans hmk),
        List.take_of_length_le (hv.le.trans hmk)] using hpre
    intro z _ _
    rw [show lowerMechanicalFactor alpha rho m i =
      lowerMechanicalFactor alpha rho m j from heq]
  have hkm : k - 1 < m := Nat.lt_of_not_ge hmk
  have hslice (s t r : ℕ) (hr : t + r ≤ m) :
      ((lowerMechanicalFactor alpha rho m s).drop t).take r =
        lowerMechanicalFactor alpha rho r (s + t) := by
    apply List.ext_getElem
    · simp [lowerMechanicalFactor, Nat.min_eq_left (show r ≤ m - t by omega)]
    · intro a ha hb
      simp only [List.getElem_take, List.getElem_drop, lowerMechanicalFactor,
        List.getElem_ofFn]
      congr 1
      omega
  have hcard (w z : List Bool) : occurrences w z =
      ∑ t ∈ Finset.range (w.length + 1),
        if t + z.length ≤ w.length ∧ (w.drop t).take z.length = z then 1 else 0 := by
    unfold occurrences
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    simp only [List.toFinset_filter, List.toFinset_range, decide_eq_true_eq]
    rw [Finset.card_filter]
  have hsupport (s : ℕ) (z : List Bool)
      (hp : 0 < occurrences (lowerMechanicalFactor alpha rho m s) z) :
      z ∈ lowerMechanicalFactorSet alpha rho z.length := by
    unfold occurrences at hp
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp hp)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at ht
    have hm : (lowerMechanicalFactor alpha rho m s).length = m := by
      simp [lowerMechanicalFactor]
    have hh := hslice s t z.length (by simpa only [hm] using ht.2.1)
    rw [ht.2.2] at hh
    exact mem_lowerMechanicalFactorSet.mpr ⟨s + t, hh⟩
  have hflow (w z : List Bool) (hn : z.length ≤ w.length) :
      occurrences w z = occurrences w (z ++ [false]) + occurrences w (z ++ [true]) +
        if w.drop (w.length - z.length) = z then 1 else 0 := by
    let n := z.length
    have hpoint (t : ℕ) :
        (if t + n ≤ w.length ∧ (w.drop t).take n = z then 1 else 0) =
        (if t + (n + 1) ≤ w.length ∧ (w.drop t).take (n + 1) = z ++ [false]
          then 1 else 0) +
        (if t + (n + 1) ≤ w.length ∧ (w.drop t).take (n + 1) = z ++ [true]
          then 1 else 0) +
        (if t + n = w.length ∧ (w.drop t).take n = z then 1 else 0) := by
      by_cases ht : t + n < w.length
      · have ht' : n < (w.drop t).length := by simp only [List.length_drop]; omega
        have htake := List.take_succ_eq_append_getElem ht'
        have hzlen : z.length = n := rfl
        have hwlen : ((w.drop t).take n).length = n := by
          simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt ht')]
        have hsplit (b : Bool) : (w.drop t).take (n + 1) = z ++ [b] ↔
            (w.drop t).take n = z ∧ (w.drop t)[n] = b := by
          rw [htake]
          constructor
          · intro heq
            refine ⟨List.append_inj_left heq (hwlen.trans hzlen.symm), ?_⟩
            simpa only [List.singleton_inj] using
              List.append_inj_right heq (hwlen.trans hzlen.symm)
          · rintro ⟨heq, hb⟩
            rw [heq, hb]
        simp only [hsplit, show t + n ≤ w.length by omega,
          show t + (n + 1) ≤ w.length by omega, show t + n ≠ w.length by omega,
          true_and, false_and, if_false]
        cases hb : (w.drop t)[n] <;>
          by_cases hz : (w.drop t).take n = z <;> simp [hz]
      · by_cases heq : t + n = w.length
        · simp only [show ¬t + (n + 1) ≤ w.length by omega,
            show t + n = w.length from heq, le_refl,
            false_and, if_false, true_and, zero_add]
        · simp only [show ¬t + n ≤ w.length by omega,
            show ¬t + (n + 1) ≤ w.length by omega,
            show ¬(t + n = w.length ∧ (w.drop t).take n = z) from fun h => heq h.1,
            false_and, if_false,
            Nat.add_zero]
    have hterminal : (∑ t ∈ Finset.range (w.length + 1),
        if t + n = w.length ∧ (w.drop t).take n = z then 1 else 0) =
        if w.drop (w.length - n) = z then 1 else 0 := by
      rw [Finset.sum_eq_single (w.length - n)]
      · have hd : (w.drop (w.length - n)).length = n := by
          simp only [List.length_drop]; dsimp [n]; omega
        have ht : (w.drop (w.length - n)).take n = w.drop (w.length - n) :=
          List.take_of_length_le hd.le
        simp only [show w.length - n + n = w.length by dsimp [n]; omega,
          true_and, ht]
      · intro t ht hne
        have hne' : t + n ≠ w.length := by dsimp [n] at *; omega
        simp only [hne', false_and, if_false]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    rw [hcard, hcard, hcard]
    simp only [List.length_append, List.length_singleton]
    change _ = _ + _ + if w.drop (w.length - n) = z then 1 else 0
    rw [← hterminal, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => hpoint t)
  have hset0 : lowerMechanicalFactorSet alpha rho 0 = {[]} := by
    ext z
    rw [mem_lowerMechanicalFactorSet, Finset.mem_singleton]
    constructor
    · rintro ⟨s, rfl⟩
      simp [lowerMechanicalFactor]
    · intro hz
      subst z
      exact ⟨0, by simp [lowerMechanicalFactor]⟩
  have hletters (b : Bool) : u.count b = v.count b := by
    have hi := mechanical_extension_mass alpha rho m i 0 b
    have hj := mechanical_extension_mass alpha rho m j 0 b
    simp only [hset0, Finset.sum_singleton, List.nil_append, List.drop_zero] at hi hj
    exact hi.symm.trans ((hab [b] (by simp) (by simp)).trans hj)
  have hboundaries (n : ℕ) (hn : n ≤ k - 1) :
      u.take n = v.take n ∧ u.drop (m - n) = v.drop (m - n) := by
    have hp := congrArg (List.take n) hpre
    have hs := congrArg (List.drop (k - 1 - n)) hsuf
    refine ⟨?_, ?_⟩
    · simpa only [List.take_take, Nat.min_eq_left hn] using hp
    · have heq : m - (k - 1) + (k - 1 - n) = m - n := by omega
      simpa only [List.drop_drop, heq] using hs
  have hcounts : ∀ n, 1 ≤ n → n ≤ k → KAbelianEq n u v := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn hnk
      by_cases hn0 : n = 0
      · subst n
        exact hab
      have hn1 : 1 ≤ n := by omega
      have hprev := ih hn1 (by omega)
      have hnm : n ≤ m := by omega
      obtain ⟨p, hp, huniq⟩ :=
        exists_unique_lower_mechanical_right_special (rho := rho) h0 h1 hirr n
      have hplen : p.length = n := by
        obtain ⟨s, hs⟩ := mem_lowerMechanicalFactorSet.mp hp.1
        simp [hs, lowerMechanicalFactor]
      have hmissing (s : ℕ) (z : List Bool)
          (hz : z ∉ lowerMechanicalFactorSet alpha rho z.length) :
          occurrences (lowerMechanicalFactor alpha rho m s) z = 0 := by
        by_contra hne
        exact hz (hsupport s z (Nat.pos_of_ne_zero hne))
      have hordinary (z : List Bool) (hz : z ∈ lowerMechanicalFactorSet alpha rho n)
          (hzp : z ≠ p) (b : Bool) : occurrences u (z ++ [b]) =
          occurrences v (z ++ [b]) := by
        have hzlen : z.length = n := by
          obtain ⟨s, rfl⟩ := mem_lowerMechanicalFactorSet.mp hz
          simp [lowerMechanicalFactor]
        have hbase := hprev z (by omega) (by omega)
        have hf := hflow u z (by omega)
        have hg := hflow v z (by omega)
        have hs := (hboundaries n (by omega)).2
        simp only [hu, hv, hzlen, hs] at hf hg
        have hnot : ¬ (z ++ [false] ∈ lowerMechanicalFactorSet alpha rho (n + 1) ∧
            z ++ [true] ∈ lowerMechanicalFactorSet alpha rho (n + 1)) := by
          intro hh
          exact hzp (huniq z ⟨hz, hh.1, hh.2⟩)
        rcases not_and_or.mp hnot with hfalse | htrue
        · have hf0 := hmissing i (z ++ [false]) (by simpa [hzlen] using hfalse)
          have hg0 := hmissing j (z ++ [false]) (by simpa [hzlen] using hfalse)
          cases b <;> change occurrences u _ = occurrences v _ <;> dsimp [u, v] at *
          · omega
          · omega
        · have hf0 := hmissing i (z ++ [true]) (by simpa [hzlen] using htrue)
          have hg0 := hmissing j (z ++ [true]) (by simpa [hzlen] using htrue)
          cases b <;> change occurrences u _ = occurrences v _ <;> dsimp [u, v] at *
          · omega
          · omega
      have hspecial (b : Bool) : occurrences u (p ++ [b]) =
          occurrences v (p ++ [b]) := by
        have hmassu := mechanical_extension_mass alpha rho m i n b
        have hmassv := mechanical_extension_mass alpha rho m j n b
        have hprefix := congrArg (List.count b) (hboundaries n (by omega)).1
        have hcu : (u.take n).count b + (u.drop n).count b = u.count b := by
          rw [← List.count_append, List.take_append_drop]
        have hcv : (v.take n).count b + (v.drop n).count b = v.count b := by
          rw [← List.count_append, List.take_append_drop]
        have hdrop : (u.drop n).count b = (v.drop n).count b := by
          have := hletters b
          omega
        have hsumeq : (∑ z ∈ lowerMechanicalFactorSet alpha rho n,
            occurrences u (z ++ [b])) =
            ∑ z ∈ lowerMechanicalFactorSet alpha rho n, occurrences v (z ++ [b]) :=
          hmassu.trans (hdrop.trans hmassv.symm)
        rw [← Finset.sum_erase_add _ _ hp.1, ← Finset.sum_erase_add _ _ hp.1] at hsumeq
        have herase : (∑ z ∈ (lowerMechanicalFactorSet alpha rho n).erase p,
            occurrences u (z ++ [b])) =
            ∑ z ∈ (lowerMechanicalFactorSet alpha rho n).erase p,
              occurrences v (z ++ [b]) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hordinary z (Finset.mem_erase.mp hz).2 (Finset.mem_erase.mp hz).1 b
        omega
      intro z hz hzn
      by_cases hzl : z.length ≤ n
      · exact hprev z hz hzl
      have hzlen : z.length = n + 1 := by omega
      by_cases hmem : z ∈ lowerMechanicalFactorSet alpha rho (n + 1)
      · obtain ⟨s, hs⟩ := mem_lowerMechanicalFactorSet.mp hmem
        let q := z.take n
        let b := z[n]'(by omega)
        have hzq : z = q ++ [b] := by
          simpa only [List.take_of_length_le (by omega : z.length ≤ n + 1)] using
            List.take_succ_eq_append_getElem (show n < z.length by omega)
        have hq : q ∈ lowerMechanicalFactorSet alpha rho n := by
          have hh : q = lowerMechanicalFactor alpha rho n s := by
            dsimp [q]
            rw [hs]
            apply List.ext_getElem
            · simp [lowerMechanicalFactor]
            · intro a ha hb
              simp only [List.getElem_take, lowerMechanicalFactor, List.getElem_ofFn]
          exact mem_lowerMechanicalFactorSet.mpr ⟨s, hh⟩
        rw [hzq]
        by_cases hqp : q = p
        · rw [hqp]
          exact hspecial b
        · exact hordinary q hq hqp b
      · have hi := hmissing i z (by simpa only [hzlen] using hmem)
        have hj := hmissing j z (by simpa only [hzlen] using hmem)
        exact hi.trans hj.symm
  by_cases hk : k = 0
  · intro z hz hzk
    omega
  · exact hcounts k (by omega) le_rfl

end D5.S1.Words.KAbelianLagrange
