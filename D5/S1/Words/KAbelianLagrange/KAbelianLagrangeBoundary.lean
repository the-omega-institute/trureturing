/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeBoundary
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeBoundary
   mirror-E: none(waiver:occurrence-boundary-recovery)
   anchors: []
   utility: none
   digest: Extension-count conservation recovers both boundaries of k-abelian equivalent words. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open KAbelianLagrangeDefs

/-- Occurrence counts recover every boundary shorter than the equivalence order. -/
theorem kabelian_boundary_recovery {k n : ℕ} {u v : List Bool}
    (hnk : n < k) (hnu : n ≤ u.length)
    (huv : KAbelianEq k u v) :
    u.take n = v.take n ∧ u.drop (u.length - n) = v.drop (v.length - n) := by
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
  have hflow (w z : List Bool) (hz : 0 < z.length) :
      occurrences w z = occurrences w (false :: z) + occurrences w (true :: z) +
        if w.take z.length = z then 1 else 0 := by
    induction w with
    | nil =>
        have hne : z ≠ [] := List.ne_nil_of_length_pos hz
        simp [occurrences, Nat.ne_of_gt hz, hne]
    | cons a w ih =>
      rw [hcons a w z, hcons a w (false :: z), hcons a w (true :: z), ih]
      simp only [List.length_cons, List.take_succ_cons, List.cons.injEq]
      cases a <;> by_cases h : w.take z.length = z <;> simp [h] <;> omega
  have hprefix (a b : List Bool) (hab : KAbelianEq k a b) (hna : n ≤ a.length) :
      a.take n = b.take n := by
    by_cases hn : n = 0
    · simp [hn]
    let z := a.take n
    have hz : z.length = n := by simp [z, List.length_take, Nat.min_eq_left hna]
    have heq := hab z (by omega) (by omega)
    have hf := hab (false :: z) (by simp) (by simp [hz]; omega)
    have ht := hab (true :: z) (by simp) (by simp [hz]; omega)
    have ha := hflow a z (by omega)
    have hb := hflow b z (by omega)
    have haz : a.take z.length = z := by simp [hz, z]
    rw [if_pos haz] at ha
    by_cases hbz : b.take z.length = z
    · simpa [hz, z] using hbz.symm
    · rw [if_neg hbz] at hb
      omega
  have hreverse (w z : List Bool) :
      occurrences w.reverse z.reverse = occurrences w z := by
    have hcard (a b : List Bool) : occurrences a b =
        ((Finset.range (a.length + 1)).filter fun i =>
          i + b.length ≤ a.length ∧ (a.drop i).take b.length = b).card := by
      unfold occurrences
      rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      simp only [List.toFinset_filter, List.toFinset_range, decide_eq_true_eq]
    have hblock (a : List Bool) (i l : ℕ) (hi : i + l ≤ a.length) :
        (a.reverse.drop (a.length - l - i)).take l = ((a.drop i).take l).reverse := by
      rw [List.drop_reverse, List.take_reverse, List.length_take,
        Nat.min_eq_left (Nat.sub_le _ _), List.drop_take]
      have h₁ : a.length - (a.length - l - i) - l = i := by omega
      have h₂ : a.length - (a.length - l - i) - i = l := by omega
      rw [h₁, h₂]
    rw [hcard, hcard]
    symm
    refine Finset.card_bij (fun i _ => w.length - z.length - i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      have hbi := hblock w i z.length hi.2.1
      refine ⟨by simp only [List.length_reverse]; omega, ?_, ?_⟩
      · simp only [List.length_reverse]
        omega
      · simpa only [List.length_reverse, hi.2.2] using hbi
    · intro i hi j hj hij
      simp only [Finset.mem_filter, Finset.mem_range] at hi hj
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, List.length_reverse] at hj
      let i := w.length - z.length - j
      have hi : i + z.length ≤ w.length := by dsimp [i]; omega
      have heq : w.length - z.length - i = j := by dsimp [i]; omega
      refine ⟨i, ?_, heq⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by dsimp [i]; omega, hi, ?_⟩
      have hh := hblock w i z.length hi
      rw [heq, hj.2.2] at hh
      exact List.reverse_injective hh.symm
  refine ⟨hprefix u v huv hnu, ?_⟩
  have hrev : KAbelianEq k u.reverse v.reverse := by
    intro z hz hzk
    simpa only [List.reverse_reverse] using
      (hreverse u z.reverse).trans ((huv z.reverse (by simpa) (by simpa)).trans
        (hreverse v z.reverse).symm)
  have hp := hprefix u.reverse v.reverse hrev (by simpa)
  have := congrArg List.reverse hp
  simpa only [List.reverse_take, List.length_reverse, List.reverse_reverse] using this

end D5.S1.Words.KAbelianLagrange
