/- GID: D5/S1/Words/MBonacciParikhStarConverse
   generality: I
   mirror-B: D5/B/S1/Words/MBonacciParikhStarConverse
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: All-start sentinel Parikh transport and the complete actual greedy converse. -/
import D5.S1.Words.MBonacciMinimumGreedy
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.MBonacciParikhStarConverse

open MBonacciSentinelDesubstitution
open MBonacciReversedPrefixFRS (sentinelIter sentinel_frs)
open MBonacciMinimumParikhDescent (parikhImage star star_subset star_injective)
open MBonacciMinimumGreedy (U S greedyScan topIndex fullGreedy periodicDigits
  sentinel_sum scan_length sentinel_top scan_sentinel minimal_abelian_complexity_greedy)
open RankOneMorphismIterationBound (subst image subst_append)
open AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)

variable {m : ℕ} (hm : 2 ≤ m)

/-- Every positive-length complete scan determines its original remainder. -/
theorem greedyScan_injective (count : ℕ) (hc : 0 < count) :
    Function.Injective (greedyScan hm count) := by
  induction count with
  | zero => omega
  | succ count ih =>
    intro r s h
    have he := List.cons.inj h
    cases count with
    | zero =>
      have hu : U hm 0 = 1 := by simp [U, image]
      simpa [hu] using he.1
    | succ count =>
      have hrem := ih (by omega) he.2
      have hr := Nat.div_add_mod r (U hm (count + 1))
      have hs := Nat.div_add_mod s (U hm (count + 1))
      rw [he.1, hrem] at hr
      omega

private theorem periodic_greedy_sentinel (n k : ℕ) (hn : 1 ≤ n)
    (h : fullGreedy hm n = periodicDigits (m := m) k) : n = S hm k := by
  have hn0 : n ≠ 0 := by omega
  have hs0 : S hm k ≠ 0 := by unfold S; omega
  have hsentinel : fullGreedy hm (S hm k) = periodicDigits (m := m) k := by
    rw [fullGreedy, if_neg hs0, sentinel_top]
    exact scan_sentinel hm k
  have hfull : fullGreedy hm n = fullGreedy hm (S hm k) :=
    h.trans hsentinel.symm
  have hlen := congrArg List.length hfull
  simp only [fullGreedy, if_neg hn0, if_neg hs0, scan_length] at hlen
  have ht : topIndex hm n = topIndex hm (S hm k) := by omega
  simp only [fullGreedy, if_neg hn0, if_neg hs0] at hfull
  rw [← ht] at hfull
  exact greedyScan_injective hm (topIndex hm n + 1) (by omega) hfull

private def Star (r : List (Fin m)) : Prop :=
  ∀ q : ℕ, ∃ b : Fin m, (factor (word hm) q (r.length + 1)).Perm (r ++ [b])

private theorem clip_permutation {α : Type*}
    (a : α) (t y : List α) (h : (a :: t).Perm (y ++ [a])) : t.Perm y := by
  exact (h.trans List.perm_append_comm).cons_inv

private theorem star_transport (r : List (Fin m)) (hr : Star hm r) : Star hm (T hm r) := by
  intro q
  obtain ⟨i, hi, hj⟩ := boundary_window hm q
  have hsum := (actual_word_laws hm).2.2.2.1
  have hs : boundary hm (i + 1) = boundary hm i + (phi hm (word hm i)).length := by
    rw [hsum (i + 1), Finset.sum_range_succ, ← hsum i]
  have htwo : (phi hm (word hm i)).length ≤ 2 := by unfold phi; split <;> simp
  have hoff : q = boundary hm i ∨ q = boundary hm i + 1 := by omega
  let v := factor (word hm) i (r.length + 1)
  obtain ⟨b, hb⟩ := hr i
  change v.Perm (r ++ [b]) at hb
  have hv : Occ hm v i := by simp [Occ, v, factor]
  have hp : (subst (phi hm) v).Perm (subst (phi hm) r ++ phi hm b) := by
    simpa [subst, List.flatMap_append] using hb.flatMap_right (phi hm)
  have hpLen := hp.length_eq
  obtain ⟨hwhole, hsentinel, _⟩ := occurrence_transport hm v i hv
  have hn : (T hm r).length + 1 = (subst (phi hm) r).length + 2 := by simp [T]
  by_cases hbLong : b.val + 1 < m
  · have hphi : phi hm b = [zero hm, rot hm b] := by simp [phi, rot, hbLong]
    rw [hphi] at hp hpLen
    have hlen : (subst (phi hm) v).length = (T hm r).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hpLen
      omega
    rcases hoff with hq | hq
    · refine ⟨rot hm b, ?_⟩
      rw [hq, ← hlen, show factor (word hm) (boundary hm i)
        (subst (phi hm) v).length = subst (phi hm) v from hwhole]
      simpa [T, List.append_assoc] using hp
    · obtain ⟨t, ht⟩ := t_head hm v
      have ho : Occ hm t (boundary hm i + 1) := by
        rw [ht] at hsentinel
        exact ((occ_cons hm _ _ _).mp hsentinel).2
      have htlen : t.length = (T hm r).length + 1 := by
        have hh := congrArg List.length ht
        simp only [T, List.length_append, List.length_cons, List.length_nil] at hh
        omega
      have hperm : (zero hm :: t).Perm ((T hm r ++ [rot hm b]) ++ [zero hm]) := by
        rw [← ht]
        have hh := hp.append_right [zero hm]
        apply hh.trans
        apply List.perm_iff_count.mpr
        intro a
        simp [T, List.count_append, List.count_cons]
      refine ⟨rot hm b, ?_⟩
      rw [hq, ← htlen, show factor (word hm) (boundary hm i + 1) t.length = t from ho]
      exact clip_permutation (zero hm) t (T hm r ++ [rot hm b]) hperm
  · have hphi : phi hm b = [zero hm] := by simp [phi, hbLong]
    rw [hphi] at hp hpLen
    have hlen : (T hm v).length = (T hm r).length + 1 := by
      simp only [List.length_append, List.length_singleton] at hpLen
      simp only [T, List.length_append, List.length_singleton]
      omega
    rcases hoff with hq | hq
    · refine ⟨zero hm, ?_⟩
      rw [hq, ← hlen, show factor (word hm) (boundary hm i) (T hm v).length = T hm v from hsentinel]
      simpa [T] using hp.append_right [zero hm]
    · let c := word hm (i + v.length)
      have hvc : Occ hm (v ++ [c]) i := by
        unfold Occ
        rw [List.length_append, List.length_singleton, factor_add, hv]
        simp [factor, c]
      have hext : Occ hm (T hm v ++ [rot hm c]) (boundary hm i) :=
        (right_extension_occurrence_iff hm v c (boundary hm i)).mpr ⟨i, rfl, hvc⟩
      obtain ⟨t, ht⟩ := t_head hm v
      have ho : Occ hm (t ++ [rot hm c]) (boundary hm i + 1) := by
        rw [ht, List.cons_append] at hext
        exact ((occ_cons hm _ _ _).mp hext).2
      have htlen : (t ++ [rot hm c]).length = (T hm r).length + 1 := by
        have hh := congrArg List.length ht
        simp only [List.length_cons] at hh
        simp only [List.length_append, List.length_singleton]
        omega
      have hperm : (zero hm :: (t ++ [rot hm c])).Perm
          ((T hm r ++ [rot hm c]) ++ [zero hm]) := by
        rw [← List.cons_append, ← ht]
        have hh := (hp.append_right [zero hm]).append_right [rot hm c]
        apply hh.trans
        apply List.perm_iff_count.mpr
        intro a
        simp [T, List.count_append, List.count_cons, Nat.add_comm, Nat.add_left_comm]
      refine ⟨rot hm c, ?_⟩
      rw [hq, ← htlen, show factor (word hm) (boundary hm i + 1)
        (t ++ [rot hm c]).length = t ++ [rot hm c] from ho]
      exact clip_permutation (zero hm) (t ++ [rot hm c]) (T hm r ++ [rot hm c]) hperm

private theorem sentinel_star (k : ℕ) : Star hm (sentinelIter hm k) := by
  induction k with
  | zero =>
    intro q
    exact ⟨word hm q, by simp [sentinelIter, factor]⟩
  | succ k ih => exact star_transport hm (sentinelIter hm k) ih

private theorem sentinel_iterate (k : ℕ) :
    sentinelIter hm k = ((T hm)^[k]) [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sentinelIter, ih, Function.iterate_succ_apply']

/-- The complete all-start image is exactly the m attained, distinct star vectors. -/
theorem sentinel_parikh_image (k : ℕ) :
    parikhImage hm (S hm k) = Set.range (star (sentinelIter hm k)) := by
  have hlen : (sentinelIter hm k).length + 1 = S hm k := by
    rw [sentinel_iterate]
    exact sentinel_sum hm k
  apply Set.Subset.antisymm
  · rintro x ⟨q, rfl⟩
    obtain ⟨b, hb⟩ := sentinel_star hm k q
    refine ⟨b, ?_⟩
    funext a
    have hc := hb.count_eq a
    simp only [List.count_append, List.count_singleton] at hc
    rw [← hlen]
    change (sentinelIter hm k).count a + (if a = b then 1 else 0) = _
    by_cases ha : a = b
    · subst a; simpa [letterCount] using hc.symm
    · simpa [letterCount, ha, Ne.symm ha] using hc.symm
  · rw [← hlen]
    exact star_subset hm (sentinelIter hm k) (sentinel_frs hm k)

private theorem sentinel_cardinality (k : ℕ) : (parikhImage hm (S hm k)).ncard = m := by
  rw [sentinel_parikh_image, Set.ncard_range_of_injective (star_injective _)]
  simp

/-- Turek's uniform minimum-complexity characterization, on the literal actual
word and complete MSB-first greedy lists, including trailing zeros. -/
theorem uniform_minimum_characterization (h5 : 5 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    ((parikhImage hm n).ncard = m ↔ ∃ k : ℕ, n = S hm k) ∧
    ((parikhImage hm n).ncard = m ↔
      ∃ k : ℕ, fullGreedy hm n = periodicDigits (m := m) k) := by
  constructor
  · constructor
    · intro hc
      obtain ⟨k, hk, _⟩ := minimal_abelian_complexity_greedy hm h5 n hn hc
      exact ⟨k, hk⟩
    · rintro ⟨k, rfl⟩
      exact sentinel_cardinality hm k
  · constructor
    · intro hc
      obtain ⟨k, _, _, hk, _⟩ := minimal_abelian_complexity_greedy hm h5 n hn hc
      exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      rw [periodic_greedy_sentinel hm n k hn hk]
      exact sentinel_cardinality hm k

#print axioms periodic_greedy_sentinel
#print axioms clip_permutation
#print axioms star_transport
#print axioms sentinel_star
#print axioms sentinel_iterate
#print axioms sentinel_cardinality

end D5.S1.Words.MBonacciParikhStarConverse

#print axioms D5.S1.Words.MBonacciMinimumGreedy.sentinel_sum
#print axioms D5.S1.Words.MBonacciMinimumGreedy.scan_length
#print axioms D5.S1.Words.MBonacciMinimumGreedy.sentinel_top
#print axioms D5.S1.Words.MBonacciMinimumGreedy.scan_sentinel
#print axioms D5.S1.Words.MBonacciReversedPrefixFRS.sentinel_frs
#print axioms D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window
#print axioms D5.S1.Words.MBonacciSentinelDesubstitution.t_head
#print axioms D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons
#print axioms D5.S1.Words.MBonacciSentinelDesubstitution.factor_add
#print axioms D5.S1.Words.MBonacciMinimumParikhDescent.star_injective
#print axioms D5.S1.Words.MBonacciMinimumParikhDescent.star_subset
#print axioms D5.S1.Words.MBonacciParikhStarConverse.greedyScan_injective
#print axioms D5.S1.Words.MBonacciParikhStarConverse.sentinel_parikh_image
#print axioms D5.S1.Words.MBonacciParikhStarConverse.uniform_minimum_characterization
