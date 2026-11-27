import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
  Stage A support for Nathanson's Problem 15.

  The signed radix lemma is kept independent of the interval construction.  It
  is the modulo-and-cancellation step used to separate the labelled sums.
-/

open scoped BigOperators

namespace D5.S3.Arith.NathansonProblem15

/- The powers are indexed by `Fin m`; the hypothesis is exactly the strict
   digit-width condition needed by the first-modulus argument. -/
theorem signed_radix_injective {m : ℕ} {B : ℤ} (hB : 1 < B)
    (d e : Fin m → ℤ)
    (hdiff : ∀ i, (d i - e i).natAbs < B.natAbs)
    (h : (∑ i : Fin m, d i * B ^ i.val) =
      ∑ i : Fin m, e i * B ^ i.val) : d = e := by
  induction m with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      have hsplit (f : Fin (m + 1) → ℤ) :
          (∑ i : Fin (m + 1), f i * B ^ i.val) =
            f 0 + B * ∑ i : Fin m, f i.succ * B ^ i.val := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
        rw [Finset.mul_sum]
        simp [mul_assoc, mul_comm, mul_left_comm]
      have h0 : d 0 = e 0 := by
        have hdvd : B ∣ d 0 - e 0 := by
          have hs := congrArg (fun z : ℤ => z -
              B * ∑ i : Fin m, e i.succ * B ^ i.val) h
          rw [hsplit d, hsplit e] at hs
          exact ⟨∑ i : Fin m, e i.succ * B ^ i.val -
              ∑ i : Fin m, d i.succ * B ^ i.val, by linarith⟩
        by_cases hzero : d 0 - e 0 = 0
        · exact sub_eq_zero.mp hzero
        · have habs : B.natAbs ≤ (d 0 - e 0).natAbs :=
            Nat.le_of_dvd (Int.natAbs_pos.mpr hzero)
              (Int.natAbs_dvd_natAbs.mpr hdvd)
          have hlt := hdiff 0
          exact False.elim ((Nat.not_lt_of_ge habs) hlt)
      have htail :
          (∑ i : Fin m, d i.succ * B ^ i.val) =
            ∑ i : Fin m, e i.succ * B ^ i.val := by
        have hs := congrArg (fun z : ℤ => z - d 0) h
        rw [hsplit d, hsplit e, h0] at hs
        have hBn : (B : ℤ) ≠ 0 := by linarith
        apply (mul_left_cancel₀ hBn)
        linarith
      have htaildiff : ∀ i : Fin m, (d i.succ - e i.succ).natAbs < B.natAbs :=
        fun i => hdiff i.succ
      have hfun := ih (d := fun i => d i.succ) (e := fun i => e i.succ)
        htaildiff htail
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun hfun j

/-- The coefficient of a place in the radix expansion of a labelled sum. -/
def digit {m : ℕ} (h : ℕ) (u v : Fin m → ℕ) (i : Fin m) : ℤ :=
  (u i : ℤ) - ((h : ℤ) - 1) * (v i : ℤ)

private theorem zero_off_of_sum_eq {m : ℕ} (f : Fin m → ℕ) (i : Fin m)
    (hi : (∑ j, f j) = f i) {j : Fin m} (hj : j ≠ i) : f j = 0 := by
  have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  rw [hi] at hsplit
  have hrest : ∑ k ∈ Finset.univ.erase i, f k = 0 := by omega
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Nat.zero_le (f k))).mp hrest j
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)

/-- A collision between distinct multiplicity pairs of total weight `h` has zero digits. -/
theorem digit_eq_zero_of_collision {m h : ℕ} (hh : 2 ≤ h)
    {u v u' v' : Fin m → ℕ}
    (huv : (∑ i, (u i + v i)) = h)
    (huv' : (∑ i, (u' i + v' i)) = h)
    (heq : digit h u v = digit h u' v') (hne : (u, v) ≠ (u', v')) :
    digit h u v = 0 := by
  have hz {a b c d : Fin m → ℕ} (hcd : (∑ i, (c i + d i)) = h)
      (hsame : digit h a b = digit h c d) (i : Fin m) (hlt : b i < d i) :
      digit h c d = 0 := by
    have hgap : (b i : ℤ) + 1 ≤ (d i : ℤ) := by omega
    have hcoef : 0 ≤ (h : ℤ) - 1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hgap hcoef
    have hdigit := congrFun hsame i
    unfold digit at hdigit
    have hc : (h : ℤ) - 1 ≤ (c i : ℤ) := by
      rw [mul_add, mul_one] at hmul
      linarith [Int.natCast_nonneg (a i)]
    have hlocal : c i + d i ≤ h := by
      rw [← hcd]
      exact Finset.single_le_sum (f := fun j => c j + d j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hc' : c i = h - 1 := by omega
    have hd' : d i = 1 := by omega
    have hfull : (∑ j, (c j + d j)) = c i + d i := by omega
    funext j
    change digit h c d j = 0
    by_cases hj : j = i
    · subst j
      simp [digit, hd', show (c i : ℤ) = (h : ℤ) - 1 by omega]
    · have hoff := zero_off_of_sum_eq (fun k => c k + d k) i hfull hj
      simp [digit, show c j = 0 by omega, show d j = 0 by omega]
  have hv : v ≠ v' := by
    intro hv
    apply hne
    refine Prod.ext ?_ hv
    change u = u'
    funext i
    have hi := congrFun heq i
    rw [← hv] at hi
    unfold digit at hi
    omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact heq.trans (hz huv' heq i hlt)
  · exact hz huv heq.symm i hgt

end D5.S3.Arith.NathansonProblem15
