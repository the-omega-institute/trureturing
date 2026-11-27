import Mathlib.Algebra.BigOperators.Fin
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

end D5.S3.Arith.NathansonProblem15
