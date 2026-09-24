/- GID: D5/S3/Combinatorics/Interpolation/AbrResidualFerrers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrResidualFerrers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: ABR residual exponents form the partition that reconstructs each monomial. -/

import D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening

/-!
This module formalizes Claim 3.1 of Adin--Brenti--Roichman: after subtracting
the descent exponents in stable decreasing-exponent order, the residual is a
nonnegative weakly decreasing partition.  Its column heights are the
elementary-symmetric factors used by the straightening iteration.

Source: R. M. Adin, F. Brenti, Y. Roichman, Trans. Amer. Math. Soc. 357
(2005), DOI 10.1090/S0002-9947-04-03494-4, Claim 3.1 and Lemma 3.2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrResidualPartition

open scoped BigOperators
open MvPolynomial
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening

theorem suffixHeight_antitone {n : Nat} (pi : Equiv.Perm (Fin n)) :
    Antitone (suffixHeight pi) := by
  intro i j hij
  unfold suffixHeight
  apply Finset.sum_le_sum
  intro k _
  by_cases hjk : j <= k
  · simp [hjk, hij.trans hjk]
  · simp [hjk]

theorem descentAt_indexPerm_eq_one_implies {n : Nat} (a : Fin n →₀ Nat)
    (i : Fin n) (hi : descentAt (indexPerm a) i = 1) :
    ∃ hnext : i.val + 1 < n,
      a (indexPerm a ⟨i.val + 1, hnext⟩) < a (indexPerm a i) := by
  have hanti : Antitone (fun j => a (indexPerm a j)) :=
    fun j k hjk =>
      Tuple.monotone_sort (fun x : Fin n => OrderDual.toDual (a x)) hjk
  unfold descentAt at hi
  split at hi
  next hnext =>
    split at hi
    next hdescent =>
      refine ⟨hnext, ?_⟩
      have hpos : i ≤ (⟨i.val + 1, hnext⟩ : Fin n) :=
        Fin.mk_le_mk.mpr (Nat.le_succ _)
      have hposStrict : i < (⟨i.val + 1, hnext⟩ : Fin n) :=
        Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)
      have hle := hanti hpos
      have hsort : indexPerm a =
          Tuple.sort (fun x : Fin n => OrderDual.toDual (a x)) := rfl
      exact lt_of_le_of_ne hle fun heq =>
        ((Tuple.eq_sort_iff.mp hsort).2 _ _ hposStrict heq.symm).not_gt hdescent
    next _ => omega
  next _ => omega

theorem suffixHeight_indexPerm_le_exponent {n : Nat} (a : Fin n →₀ Nat)
    (i : Fin n) : suffixHeight (indexPerm a) i ≤ a (indexPerm a i) := by
  classical
  have suffixSplit (pi : Equiv.Perm (Fin n)) (j : Fin n)
      (hj : j.val + 1 < n) :
      suffixHeight pi j = descentAt pi j + suffixHeight pi ⟨j.val + 1, hj⟩ := by
    unfold suffixHeight
    calc
      (Finset.univ.sum fun k : Fin n => if j ≤ k then descentAt pi k else 0) =
          Finset.univ.sum fun k : Fin n =>
            (if k = j then descentAt pi j else 0) +
              (if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hkj : k = j
        · subst k
          have hnle : ¬(⟨j.val + 1, hj⟩ : Fin n) ≤ j := by
            intro hle
            have hval := Fin.mk_le_mk.mp hle
            omega
          simp [hnle]
        · by_cases hjk : j ≤ k
          · have hsucc : (⟨j.val + 1, hj⟩ : Fin n) ≤ k := by
              apply Fin.mk_le_mk.mpr
              have hjk' := Fin.mk_le_mk.mp hjk
              have hval : j.val ≠ k.val := fun h => hkj (Fin.ext h.symm)
              omega
            simp [hkj, hjk, hsucc]
          · have hsucc : ¬(⟨j.val + 1, hj⟩ : Fin n) ≤ k := by
              intro h
              exact hjk (le_trans (Fin.mk_le_mk.mpr (Nat.le_succ _)) h)
            simp [hkj, hjk, hsucc]
      _ = (Finset.univ.sum fun k : Fin n => if k = j then descentAt pi j else 0) +
          Finset.univ.sum fun k : Fin n =>
            if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0 := by
        rw [Finset.sum_add_distrib]
      _ = descentAt pi j + Finset.univ.sum fun k : Fin n =>
            if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0 := by
        simp
  have hanti : Antitone (fun j => a (indexPerm a j)) :=
    fun j k hjk =>
      Tuple.monotone_sort (fun x : Fin n => OrderDual.toDual (a x)) hjk
  by_cases hnext : i.val + 1 < n
  · have ih := suffixHeight_indexPerm_le_exponent a ⟨i.val + 1, hnext⟩
    rw [suffixSplit (indexPerm a) i hnext]
    by_cases hd : descentAt (indexPerm a) i = 0
    · rw [hd, zero_add]
      exact ih.trans (hanti (Fin.mk_le_mk.mpr (Nat.le_succ _)))
    · have hdle : descentAt (indexPerm a) i ≤ 1 := by
        unfold descentAt
        split <;> split <;> simp
      have hdone : descentAt (indexPerm a) i = 1 := by omega
      obtain ⟨hnext', hstrict⟩ := descentAt_indexPerm_eq_one_implies a i hdone
      have ih' := suffixHeight_indexPerm_le_exponent a ⟨i.val + 1, hnext'⟩
      have hsuffixEq : suffixHeight (indexPerm a) ⟨i.val + 1, hnext⟩ =
          suffixHeight (indexPerm a) ⟨i.val + 1, hnext'⟩ := by
        congr
      rw [hdone]
      rw [hsuffixEq]
      omega
  · have hilast : ∀ j : Fin n, i ≤ j → j = i := by
      intro j hij
      apply Fin.ext
      simp only [Fin.le_iff_val_le_val] at hij
      have hj := j.isLt
      omega
    unfold suffixHeight
    have hzero : (Finset.univ.sum fun j : Fin n =>
        if i ≤ j then descentAt (indexPerm a) j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hij : i ≤ j
      · have hji : j = i := hilast j hij
        subst j
        unfold descentAt
        simp [hnext]
      · simp [hij]
    rw [hzero]
    exact Nat.zero_le _
termination_by n - i.val
decreasing_by
  all_goals omega

/-- ABR Claim 3.1: the residual exponents are weakly decreasing in stable
index order. -/
theorem residual_antitone {n : Nat} (a : Fin n →₀ Nat) :
    Antitone (residual a) := by
  classical
  have suffixSplit (pi : Equiv.Perm (Fin n)) (j : Fin n)
      (hj : j.val + 1 < n) :
      suffixHeight pi j = descentAt pi j + suffixHeight pi ⟨j.val + 1, hj⟩ := by
    unfold suffixHeight
    calc
      (Finset.univ.sum fun k : Fin n => if j ≤ k then descentAt pi k else 0) =
          Finset.univ.sum fun k : Fin n =>
            (if k = j then descentAt pi j else 0) +
              (if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hkj : k = j
        · subst k
          have hnle : ¬(⟨j.val + 1, hj⟩ : Fin n) ≤ j := by
            intro hle
            have hval := Fin.mk_le_mk.mp hle
            omega
          simp [hnle]
        · by_cases hjk : j ≤ k
          · have hsucc : (⟨j.val + 1, hj⟩ : Fin n) ≤ k := by
              apply Fin.mk_le_mk.mpr
              have hjk' := Fin.mk_le_mk.mp hjk
              have hval : j.val ≠ k.val := fun h => hkj (Fin.ext h.symm)
              omega
            simp [hkj, hjk, hsucc]
          · have hsucc : ¬(⟨j.val + 1, hj⟩ : Fin n) ≤ k := by
              intro h
              exact hjk (le_trans (Fin.mk_le_mk.mpr (Nat.le_succ _)) h)
            simp [hkj, hjk, hsucc]
      _ = (Finset.univ.sum fun k : Fin n => if k = j then descentAt pi j else 0) +
          Finset.univ.sum fun k : Fin n =>
            if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0 := by
        rw [Finset.sum_add_distrib]
      _ = descentAt pi j + Finset.univ.sum fun k : Fin n =>
            if (⟨j.val + 1, hj⟩ : Fin n) ≤ k then descentAt pi k else 0 := by
        simp
  cases n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n =>
      have hanti : Antitone (fun j => a (indexPerm a j)) :=
        fun j k hjk =>
          Tuple.monotone_sort
            (fun x : Fin (n + 1) => OrderDual.toDual (a x)) hjk
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      have hnext : i.castSucc.val + 1 < n + 1 := by
        rw [Fin.val_castSucc]
        omega
      have hright : (⟨i.castSucc.val + 1, hnext⟩ : Fin (n + 1)) = i.succ :=
        Fin.ext rfl
      have hsuffix := suffixSplit (indexPerm a) i.castSucc hnext
      rw [hright] at hsuffix
      have hrightBound := suffixHeight_indexPerm_le_exponent a i.succ
      have hcast : i.castSucc ≤ i.succ :=
        Fin.mk_le_mk.mpr (Nat.le_succ _)
      have hleftOrder := hanti hcast
      by_cases hd : descentAt (indexPerm a) i.castSucc = 0
      · rw [hd, zero_add] at hsuffix
        unfold AbrCoordinateBoxStraightening.residual
        rw [hsuffix]
        exact Nat.sub_le_sub_right hleftOrder _
      · have hdle : descentAt (indexPerm a) i.castSucc ≤ 1 := by
          unfold descentAt
          split <;> split <;> simp
        have hdone : descentAt (indexPerm a) i.castSucc = 1 := by omega
        obtain ⟨hnext', hstrict⟩ :=
          descentAt_indexPerm_eq_one_implies a i.castSucc hdone
        have hsame : (⟨i.castSucc.val + 1, hnext'⟩ : Fin (n + 1)) = i.succ :=
          Fin.ext rfl
        rw [hsame] at hstrict
        unfold AbrCoordinateBoxStraightening.residual
        omega


end D5.S3.Combinatorics.Interpolation.AbrResidualPartition
