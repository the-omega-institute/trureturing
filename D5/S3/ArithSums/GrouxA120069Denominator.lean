/- GID: D5/S3/ArithSums/GrouxA120069Denominator
   generality: G
   mirror-B: D5/B/S3/ArithSums/GrouxA120069Denominator
   mirror-E: none(waiver:universal-rational-denominator-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Catalan.Basic,mathlib/module/Mathlib.Data.Rat.Lemmas]
   utility: none
   digest: The reduced denominator equality for the original Groux A120069 Catalan partial sums. -/

/-!
The finite-sum identity is the Catalan form of Mostert's identity in A119951.
The only public result is the original positive-index A120069 conjecture.
The private helpers balance and sum_formula are consumed by sum_formula and
result respectively. No escape witness is asserted. Admission is intended via
open-problem-resolution, prospectively registered in issue #27467.
-/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
namespace D5.S3.ArithSums.GrouxA120069Denominator
set_option maxHeartbeats 1000000
private theorem balance (n : ℕ) :
    ((n : ℚ) + 2) * (catalan (n+1) : ℚ) = 2 * (2*n+1) * (catalan n : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1), ← succ_mul_catalan_eq_centralBinom n] at h
  have hq : ((n : ℚ)+1) * (((n : ℚ)+2) * (catalan (n+1) : ℚ)) =
      2 * (2*n+1) * (((n : ℚ)+1) * (catalan n : ℚ)) := by exact_mod_cast h
  have hn : (n : ℚ)+1 ≠ 0 := by positivity
  apply (mul_left_cancel₀ hn)
  nlinarith [hq]
private theorem sum_formula (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 n, (catalan k : ℚ) / (4 : ℚ)^(k-1)) =
      4 - (2*n+1) * (catalan n : ℚ) / (4 : ℚ)^(n-1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [catalan_one]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    have h := balance n
    have hp : (4 : ℚ)^n = 4 * (4 : ℚ)^(n-1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
      ring
    push_cast
    rw [hp]
    field_simp
    nlinarith [h]
theorem result (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 n, (catalan k : ℚ) / (4 : ℚ)^(k-1)).den =
      ((catalan n : ℚ) / (4 : ℚ)^(n-1)).den := by
  rw [sum_formula n hn]
  let q : ℚ := (catalan n : ℚ) / (4 : ℚ)^(n-1)
  have hd : q.den ∣ 4^(n-1) := by
    have hh := Rat.den_dvd (catalan n : ℤ) ((4 : ℤ)^(n-1))
    have hh' : (q.den : ℤ) ∣ ((4^ (n-1) : ℕ) : ℤ) := by
      simpa [q, Rat.divInt_eq_div] using hh
    exact_mod_cast hh'
  have hc2 : Nat.Coprime (2*n+1) 2 := by
    simp
  have hc4 : Nat.Coprime (2*n+1) 4 := by
    convert hc2.pow_right 2 using 1
  have hc : Nat.Coprime (2*n+1) q.den := (hc4.pow_right (n-1)).of_dvd_right hd
  have hm : (((2*n+1 : ℕ) : ℚ) * q).den = q.den := by
    rw [Rat.mul_den]
    simp only [Rat.den_natCast, Rat.num_natCast, one_mul, Int.natAbs_mul,
      Int.natAbs_natCast]
    rw [(hc.mul_left q.reduced).gcd_eq_one, Nat.div_one]
  have he : (2*(n : ℚ)+1) * (catalan n : ℚ) / 4^(n-1) =
      ((2*n+1 : ℕ) : ℚ) * q := by dsimp [q]; push_cast; ring
  rw [he]
  simpa using hm
end D5.S3.ArithSums.GrouxA120069Denominator
