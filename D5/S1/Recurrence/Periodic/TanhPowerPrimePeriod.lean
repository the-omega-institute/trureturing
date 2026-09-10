/- GID: D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/TanhPowerPrimePeriod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two; result=D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two_false; claim=D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.bala_conjecture_two
   digest: A double Stirling sum has every odd prime period; Bala's prime-two claim fails. -/

import D5.S1.Recurrence.Periodic.AlternatingWeightStirlingPrimePeriod

/-!
# The double Stirling formula associated with OEIS A221077

For positive n, formula (9) is
`sum_{m=1..n} 2^(n-m) m! (m-1)! S(n,m) S(n+1,m)`.
It is taken as the definition here; the e.g.f. identity is not formalized.
The derivation is recorded in Library/Recurrence/bala2022a221077.md.
Thus the formal period and refutation concern this exact finite formula.
The asserted period need not be minimal.

Freeze prerequisite: D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod
(and its transitive StirlingPowerFactorialPrimePeriod prerequisite).
The weighted-sum period does not apply verbatim: the second Stirling factor
also depends on n. Two uses of its inclusion-exclusion API are required.
-/

open Finset
open D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod (stirling2_inclusion_exclusion)
open D5.S1.Recurrence.Periodic.AlternatingWeightStirlingPrimePeriod (pow_add_pred_prime)

namespace D5.S1.Recurrence.Periodic.TanhPowerPrimePeriod

/-- Formula (9), with a(0)=1. The e.g.f. identity itself is not formalized;
(9) is taken as the definition, with its derivation recorded in the Library note. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else
    ∑ m ∈ Ico 1 (n + 1), 2 ^ (n - m) * m.factorial * (m - 1).factorial *
      Nat.stirlingSecond n m * Nat.stirlingSecond (n + 1) m

/-- Factorial divisibility reduces the positive-index sum to 1 ≤ m < p. -/
theorem a_window (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    ((a n : ℤ) : ZMod p) = ∑ m ∈ Ico 1 p,
      (2 : ZMod p) ^ (n - m) * (m.factorial : ZMod p) *
        ((m - 1).factorial : ZMod p) * (Nat.stirlingSecond n m : ZMod p) *
          (Nat.stirlingSecond (n + 1) m : ZMod p) := by
  simp only [a, if_neg (show n ≠ 0 by omega), Int.cast_natCast, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat]
  rcases le_total (n + 1) p with h | h
  · apply sum_subset (Ico_subset_Ico_right h)
    intro m hm hmn
    have hnm : n < m := by simp only [mem_Ico] at hm hmn; omega
    simp [Nat.stirlingSecond_eq_zero_of_lt hnm]
  · symm
    apply sum_subset (Ico_subset_Ico_right h)
    intro m hm hmp
    have hpm : p ≤ m := by simp only [mem_Ico] at hm hmp; omega
    have hf : (m.factorial : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hp.pos hpm)
    simp [hf]

private theorem two_ne_zero (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

private theorem factorial_split (p m : ℕ) (hp : p.Prime) (hm : m ∈ Ico 1 p) :
    ((m - 1).factorial : ZMod p) = (m : ZMod p)⁻¹ * (m.factorial : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt (mem_Ico.mp hm).1 (mem_Ico.mp hm).2
      ((ZMod.natCast_eq_zero_iff m p).mp hz)
  have he : m.factorial = m * (m - 1).factorial := by
    have := Nat.factorial_succ (m - 1)
    simpa [Nat.sub_add_cancel (mem_Ico.mp hm).1] using this
  rw [he, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]

private theorem inclusion (p n m : ℕ) :
    (m.factorial : ZMod p) * (Nat.stirlingSecond n m : ZMod p) =
      ∑ j ∈ range (m + 1), (-1 : ZMod p) ^ (m - j) *
        (Nat.choose m j : ZMod p) * (j : ZMod p) ^ n := by
  have hi := congrArg (Int.castRingHom (ZMod p)) (stirling2_inclusion_exclusion n m)
  simpa only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] using hi

/-- A fixed exponential sum with coefficients independent of the positive index n. -/
theorem a_exponential_sum (p n : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hn : 1 ≤ n) :
    ((a n : ℤ) : ZMod p) =
      ∑ m ∈ Ico 1 p, ∑ j ∈ range (m + 1), ∑ k ∈ range (m + 1),
        ((2 : ZMod p)⁻¹ ^ m * (m : ZMod p)⁻¹ *
          ((-1 : ZMod p) ^ (m - j) * (Nat.choose m j : ZMod p)) *
          ((-1 : ZMod p) ^ (m - k) * (Nat.choose m k : ZMod p)) *
          (k : ZMod p)) * ((2 : ZMod p) * (j : ZMod p) * (k : ZMod p)) ^ n := by
  let : Fact p.Prime := ⟨hp⟩
  rw [a_window p n hp hn]
  apply sum_congr rfl
  intro m hm
  have hnormalize :
      (2 : ZMod p) ^ (n - m) * (m.factorial : ZMod p) *
        ((m - 1).factorial : ZMod p) * (Nat.stirlingSecond n m : ZMod p) *
          (Nat.stirlingSecond (n + 1) m : ZMod p) =
      (2 : ZMod p) ^ n * (2 : ZMod p)⁻¹ ^ m * (m : ZMod p)⁻¹ *
        ((m.factorial : ZMod p) * (Nat.stirlingSecond n m : ZMod p)) *
        ((m.factorial : ZMod p) * (Nat.stirlingSecond (n + 1) m : ZMod p)) := by
    by_cases hmn : m ≤ n
    · have hpow : (2 : ZMod p) ^ (n - m) = (2 : ZMod p) ^ n * (2 : ZMod p)⁻¹ ^ m := by
        simpa only [inv_pow] using pow_sub₀ (2 : ZMod p) (two_ne_zero p hp hodd) hmn
      rw [hpow, factorial_split p m hp hm]
      ring
    · simp [Nat.stirlingSecond_eq_zero_of_lt (by omega : n < m)]
  rw [hnormalize, inclusion p n m, inclusion p (n + 1) m]
  rw [Finset.mul_sum (s := range (m + 1)) (f := fun j =>
    (-1 : ZMod p) ^ (m - j) * (Nat.choose m j : ZMod p) * (j : ZMod p) ^ n),
    sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [mul_pow, mul_pow, pow_succ]
  ring

/-- Bala's odd-prime period for formula (9); minimality is not asserted. -/
theorem bala_conjecture_odd (p n : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hn : 1 ≤ n) :
    ((a (n + (p - 1)) : ℤ) : ZMod p) = ((a n : ℤ) : ZMod p) := by
  rw [a_exponential_sum p _ hp hodd (by omega), a_exponential_sum p n hp hodd hn]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  rw [pow_add_pred_prime hp _ n hn]

/-- The p=2 instance of the literal Bala claim, named for the refutation certificate. -/
def bala_conjecture_two : Prop :=
  ∀ n : ℕ, 1 ≤ n → ((a (n + (2 - 1)) : ℤ) : ZMod 2) = ((a n : ℤ) : ZMod 2)

/-- Formula (9) gives a(1)=1 and a(2)=8, refuting the claimed period at p=2. -/
theorem bala_conjecture_two_false : ¬ bala_conjecture_two := by
  intro h
  have hc := h 1 (by omega)
  norm_num [a, Finset.sum_Ico_succ_top, Nat.stirlingSecond, Nat.factorial] at hc
  exact (by decide : (8 : ZMod 2) ≠ 1) hc

#print axioms a
#print axioms a_window
#print axioms a_exponential_sum
#print axioms bala_conjecture_odd
#print axioms bala_conjecture_two
#print axioms bala_conjecture_two_false

end D5.S1.Recurrence.Periodic.TanhPowerPrimePeriod
