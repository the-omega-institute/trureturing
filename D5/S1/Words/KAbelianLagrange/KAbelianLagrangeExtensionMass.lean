/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeExtensionMass
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeExtensionMass
   mirror-E: none(waiver:extension-occurrence-mass)
   anchors: []
   utility: none
   digest: Summing right-extension occurrences counts the letters beyond the initial boundary. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open KAbelianLagrangeDefs D5.S1.Words.Mechanical

/-- The total occurrence mass of right extensions in the actual mechanical language. -/
theorem mechanical_extension_mass (alpha rho : ℝ) (m start n : ℕ) (b : Bool) :
    ∑ z ∈ lowerMechanicalFactorSet alpha rho n,
      occurrences (lowerMechanicalFactor alpha rho m start) (z ++ [b]) =
        ((lowerMechanicalFactor alpha rho m start).drop n).count b := by
  classical
  have hcons (a : Bool) (w z : List Bool) :
      occurrences (a :: w) z =
        (if (a :: w).take z.length = z then 1 else 0) + occurrences w z := by
    have hbound (heq : (a :: w).take z.length = z) :
        z.length ≤ (a :: w).length := by
      have hh := congrArg List.length heq
      simp only [List.length_take] at hh
      omega
    unfold occurrences
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.filter_cons, List.filter_map, Function.comp_def,
      Nat.zero_add, List.drop_zero, List.drop_succ_cons, Nat.succ_eq_add_one]
    have hpred : (fun i : ℕ => decide
        (i + 1 + z.length ≤ w.length + 1 ∧ (w.drop i).take z.length = z)) =
        (fun i : ℕ => decide
          (i + z.length ≤ w.length ∧ (w.drop i).take z.length = z)) := by
      funext i
      simp only [Nat.add_right_comm i 1 z.length, Nat.add_le_add_iff_right]
    simp only [hpred]
    by_cases heq : (a :: w).take z.length = z
    · have hb : z.length ≤ w.length + 1 := hbound heq
      simp [heq, hb, Nat.add_comm]
    · simp [heq]
  have hmass (L : Finset (List Bool))
      (hlen : ∀ z ∈ L, z.length = n) (w : List Bool)
      (hcover : ∀ i, i + n ≤ w.length → (w.drop i).take n ∈ L) :
      ∑ z ∈ L, occurrences w (z ++ [b]) = (w.drop n).count b := by
    induction w with
    | nil =>
      simp only [List.drop_nil, List.count_nil]
      apply Finset.sum_eq_zero
      intro z hz
      simp [occurrences]
    | cons a w ih =>
      have hc : ∀ i, i + n ≤ w.length → (w.drop i).take n ∈ L := by
        intro i hi
        simpa using hcover (i + 1) (by simp only [List.length_cons]; omega)
      have hs : (∑ z ∈ L, occurrences (a :: w) (z ++ [b])) =
          (∑ z ∈ L, if (a :: w).take (n + 1) = z ++ [b] then 1 else 0) +
            (w.drop n).count b := by
        rw [← ih hc, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z hz
        simpa only [List.length_append, List.length_singleton, hlen z hz]
          using hcons a w (z ++ [b])
      rw [hs]
      by_cases hn : n < (a :: w).length
      · let p := (a :: w).take n
        have hp : p ∈ L := by simpa [p] using hcover 0 (by omega)
        have ht := List.take_succ_eq_append_getElem hn
        have hind (z : List Bool) (hz : z ∈ L) :
            (a :: w).take (n + 1) = z ++ [b] ↔ p = z ∧ (a :: w)[n] = b := by
          rw [ht]
          have hpLen : p.length = n := by
            simp only [p, List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]
          change p ++ [(a :: w)[n]] = z ++ [b] ↔ _
          constructor
          · intro heq
            refine ⟨List.append_inj_left heq (hpLen.trans (hlen z hz).symm), ?_⟩
            simpa only [List.singleton_inj] using
              List.append_inj_right heq (hpLen.trans (hlen z hz).symm)
          · rintro ⟨rfl, hb⟩
            simp only [hb]
        have hsum : (∑ z ∈ L,
            if (a :: w).take (n + 1) = z ++ [b] then 1 else 0) =
            if (a :: w)[n] = b then 1 else 0 := by
          calc
            _ = ∑ z ∈ L, if p = z ∧ (a :: w)[n] = b then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro z hz
              simp only [hind z hz]
            _ = if (a :: w)[n] = b then 1 else 0 := by
              by_cases hb : (a :: w)[n] = b <;> simp [hb, hp, eq_comm]
        rw [hsum]
        cases n with
        | zero => simp [List.count_cons, Nat.add_comm]
        | succ n =>
          have hn' : n < w.length := by simp only [List.length_cons] at hn; omega
          rw [List.drop_succ_cons, List.drop_eq_getElem_cons hn', List.count_cons]
          simp [Nat.add_comm]
      · have hzero : (∑ z ∈ L,
            if (a :: w).take (n + 1) = z ++ [b] then 1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro z hz
          have hne : (a :: w).take (n + 1) ≠ z ++ [b] := by
            intro heq
            have hh := congrArg List.length heq
            simp only [List.length_take, List.length_append,
              List.length_singleton, hlen z hz] at hh
            omega
          exact if_neg hne
        rw [hzero]
        have hw : w.length ≤ n := by simp only [List.length_cons] at hn; omega
        simp [List.drop_eq_nil_iff.mpr hw,
          List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt hn)]
  apply hmass
  · intro z hz
    obtain ⟨i, rfl⟩ := mem_lowerMechanicalFactorSet.mp hz
    simp [lowerMechanicalFactor]
  · intro i hi
    have hslice : ((lowerMechanicalFactor alpha rho m start).drop i).take n =
        lowerMechanicalFactor alpha rho n (start + i) := by
      have hm : (lowerMechanicalFactor alpha rho m start).length = m := by
        simp [lowerMechanicalFactor]
      apply List.ext_getElem
      · simp [lowerMechanicalFactor, Nat.min_eq_left (show n ≤ m - i by omega)]
      · intro j hj hk
        simp only [List.getElem_take, List.getElem_drop, lowerMechanicalFactor,
          List.getElem_ofFn]
        congr 1
        omega
    rw [hslice]
    exact mem_lowerMechanicalFactorSet.mpr ⟨start + i, rfl⟩

end D5.S1.Words.KAbelianLagrange
