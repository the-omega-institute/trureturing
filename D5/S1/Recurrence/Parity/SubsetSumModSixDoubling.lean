/- GID: D5/S1/Recurrence/Parity/SubsetSumModSixDoubling
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/SubsetSumModSixDoubling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Subset sums modulo six satisfy the doubling conjecture of OEIS A068012. -/

import Mathlib

namespace D5.S1.Recurrence.Parity.SubsetSumModSixDoubling

open Finset

/-- The number of subsets of `{1, ..., n}` with the given sum modulo six. -/
def C (n : ℕ) (r : ZMod 6) : ℕ :=
  ((Icc 1 n).powerset.filter fun (s : Finset ℕ) => (∑ x ∈ s, (x : ZMod 6)) = r).card

/-- OEIS A068012, including the empty subset and the index zero. -/
def a (n : ℕ) : ℕ := C n 0

private def countIn (s : Finset ℕ) (r : ZMod 6) : ℕ :=
  (s.powerset.filter fun (t : Finset ℕ) => (∑ x ∈ t, (x : ZMod 6)) = r).card

private theorem count_insert (s : Finset ℕ) (x : ℕ) (hx : x ∉ s) (r : ZMod 6) :
    countIn (insert x s) r = countIn s r + countIn s (r - x) := by
  unfold countIn
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_powerset_insert hx]
  congr 1
  apply sum_congr rfl
  intro t ht
  have hxt : x ∉ t := fun h => hx (mem_powerset.mp ht h)
  rw [sum_insert hxt]
  simp only [eq_sub_iff_add_eq, add_comm]

private theorem interval_succ (n : ℕ) : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

/-- Adding the last element splits subsets into the two possible membership cases. -/
theorem count_succ (n : ℕ) (r : ZMod 6) :
    C (n + 1) r = C n r + C n (r - (n + 1 : ℕ)) := by
  change countIn (Icc 1 (n + 1)) r = _
  rw [interval_succ, count_insert _ _ (by simp)]
  rfl

/-- Once element three is available, residues separated by three have equal counts. -/
theorem count_three_periodic (m : ℕ) (hm : 3 ≤ m) (r : ZMod 6) :
    C m r = C m (r + 3) := by
  have hthree : 3 ∈ Icc 1 m := mem_Icc.mpr ⟨by omega, hm⟩
  have split (t : ZMod 6) := count_insert ((Icc 1 m).erase 3) 3 (by simp) t
  simp only [insert_erase hthree] at split
  change countIn (Icc 1 m) r = countIn (Icc 1 m) (r + 3)
  rw [split r, split (r + 3)]
  have hr : r - 3 = r + 3 := by
    rw [sub_eq_add_neg, show -(3 : ZMod 6) = 3 by decide]
  simp only [Nat.cast_ofNat, add_sub_cancel_right, hr, add_comm]

private theorem count_complement (s : Finset ℕ) (r : ZMod 6) :
    countIn s r = countIn s ((∑ x ∈ s, (x : ZMod 6)) - r) := by
  unfold countIn
  apply card_bij (fun t _ => s \ t)
  · intro t ht
    obtain ⟨ht, hr⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, by
      rw [sum_sdiff_eq_sub (mem_powerset.mp ht), hr]⟩
  · intro t ht u hu htu
    have ht' := mem_powerset.mp (mem_filter.mp ht).1
    have hu' := mem_powerset.mp (mem_filter.mp hu).1
    have h := congrArg (fun v : Finset ℕ => s \ v) htu
    simpa only [Finset.sdiff_sdiff_eq_self ht', Finset.sdiff_sdiff_eq_self hu'] using h
  · intro u hu
    obtain ⟨hu, hr⟩ := mem_filter.mp hu
    refine ⟨s \ u, mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, ?_⟩,
      Finset.sdiff_sdiff_eq_self (mem_powerset.mp hu)⟩
    rw [sum_sdiff_eq_sub (mem_powerset.mp hu), hr]
    abel

private theorem interval_sum_twice (m : ℕ) :
    (∑ x ∈ Icc 1 m, (x : ZMod 6)) * 2 = (m : ZMod 6) * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [interval_succ, sum_insert (by simp)]
    push_cast
    linear_combination ih

/-- In the residue-one phase modulo three, zero and one occur equally often. -/
theorem count_zero_eq_one (m : ℕ) (hm : 4 ≤ m) (hmod : m % 3 = 1) :
    C m 0 = C m 1 := by
  have hm6 : m % 6 = 1 ∨ m % 6 = 4 := by omega
  have hmcast : (m : ZMod 6) = 1 ∨ (m : ZMod 6) = 4 := by
    rcases hm6 with h | h
    · left
      exact (ZMod.natCast_eq_natCast_iff' m 1 6).mpr h
    · right
      exact (ZMod.natCast_eq_natCast_iff' m 4 6).mpr h
  have hdouble : (∑ x ∈ Icc 1 m, (x : ZMod 6)) * 2 = 2 := by
    have h := interval_sum_twice m
    rcases hmcast with hc | hc <;> rw [hc] at h <;> norm_num at h ⊢ <;> exact h
  have htotal : (∑ x ∈ Icc 1 m, (x : ZMod 6)) = 1 ∨
      (∑ x ∈ Icc 1 m, (x : ZMod 6)) = 4 := by
    exact (by decide : ∀ t : ZMod 6, t * 2 = 2 → t = 1 ∨ t = 4) _ hdouble
  have hcomp := count_complement (Icc 1 m) 0
  change C m 0 = C m ((∑ x ∈ Icc 1 m, (x : ZMod 6)) - 0) at hcomp
  rw [sub_zero] at hcomp
  rcases htotal with h | h
  · rwa [h] at hcomp
  · rw [h] at hcomp
    exact hcomp.trans (count_three_periodic m (by omega) 1).symm

/-- Corneth's doubling conjecture in OEIS A068012, for every index in its stated range. -/
theorem subset_sum_mod_six_doubling (n : ℕ) (hn : 2 < n) (hdiv : ¬ 3 ∣ (n - 1)) :
    a n = 2 * a (n - 1) := by
  by_cases hn3 : n = 3
  · subst n
    decide
  have hm : 3 ≤ n - 1 := by omega
  have hn' : n = (n - 1) + 1 := by omega
  have hmod : (n - 1) % 3 ≠ 0 := by
    intro h
    exact hdiv (Nat.dvd_of_mod_eq_zero h)
  have hr : (n - 1) % 6 = 1 ∨ (n - 1) % 6 = 2 ∨
      (n - 1) % 6 = 4 ∨ (n - 1) % 6 = 5 := by omega
  have hshift : C (n - 1) (0 - (n : ZMod 6)) = C (n - 1) 0 := by
    have hc : (n : ZMod 6) = (((n - 1) % 6 : ℕ) : ZMod 6) + 1 := by
      conv_lhs => rw [hn']
      rw [Nat.cast_add, Nat.cast_one]
      congr 1
      exact (ZMod.natCast_eq_natCast_iff' (n - 1) ((n - 1) % 6) 6).mpr (by omega)
    rcases hr with h | h | h | h
    · rw [h] at hc
      norm_num at hc
      rw [hc]
      norm_num
      exact (count_three_periodic (n - 1) hm 1).symm.trans
        (count_zero_eq_one (n - 1) (by omega) (by omega)).symm
    · rw [h] at hc
      norm_num at hc
      rw [hc]
      norm_num
      exact (count_three_periodic (n - 1) hm 0).symm
    · rw [h] at hc
      norm_num at hc
      rw [hc]
      norm_num
      exact (count_zero_eq_one (n - 1) (by omega) (by omega)).symm
    · rw [h] at hc
      norm_num at hc
      rw [hc]
      norm_num
      rw [show -(6 : ZMod 6) = 0 by decide]
  unfold a
  conv_lhs => rw [hn', count_succ]
  rw [← hn', hshift, two_mul]

#print axioms count_succ
#print axioms count_three_periodic
#print axioms count_zero_eq_one
#print axioms subset_sum_mod_six_doubling

end D5.S1.Recurrence.Parity.SubsetSumModSixDoubling
