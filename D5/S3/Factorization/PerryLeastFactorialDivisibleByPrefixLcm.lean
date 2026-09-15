/- GID: D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm
   generality: I
   mirror-B: D5/B/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Bertrand, mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: For n >= 5, the least factorial divisible by the prefix lcm is indexed by the largest prime <= n. -/

import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Nat

namespace D5.S3.Factorization.PerryLeastFactorialDivisibleByPrefixLcm

/-- Every prefix lcm from five onward divides the factorial of its largest prime. -/
theorem prefix_lcm_dvd_factorial_of_maximal_prime
    (n p : ℕ) (hn : 5 ≤ n) (hp : p.Prime)
    (hmax : ∀ q, q.Prime → q ≤ n → q ≤ p) :
    Nat.lcmUpto n ∣ (p !) := by
  rw [Nat.lcmUpto, Finset.lcm_dvd_iff]
  intro m hm
  simp only [Finset.mem_Icc] at hm
  by_cases hmp : m ≤ p
  · exact Nat.dvd_factorial (m := m) (n := p) (by omega) hmp
  have hpm : p < m := Nat.lt_of_not_ge hmp
  obtain ⟨r, hrPrime, hpr, hr2p⟩ :=
    Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have hnr : n < r := by
    by_contra! hrn
    have := hmax r hrPrime hrn
    omega
  have hm2p : m < 2 * p :=
    lt_of_lt_of_le (lt_of_le_of_lt hm.2 hnr) hr2p
  have hmNotPrime : ¬m.Prime := by
    intro hmPrime
    have := hmax m hmPrime hm.2
    omega
  have hm2 : 2 ≤ m := by omega
  let a := m.minFac
  let b := m / a
  have haPrime : a.Prime := by
    simpa [a] using Nat.minFac_prime (show m ≠ 1 by omega)
  have ha2 : 2 ≤ a := haPrime.two_le
  have haDvd : a ∣ m := by
    simpa [a] using Nat.minFac_dvd m
  have hab : a * b = m := by
    simpa [b] using Nat.mul_div_cancel' haDvd
  have habOrder : a ≤ b := by
    simpa [a, b] using Nat.minFac_le_div (by omega : 0 < m) hmNotPrime
  have h2b : 2 * b ≤ m := by
    calc
      2 * b ≤ a * b := Nat.mul_le_mul_right b ha2
      _ = m := hab
  have hbp : b < p := by omega
  by_cases habLt : a < b
  · have haPred : a ≤ b - 1 := by omega
    have haFactorial : a ∣ (b - 1)! :=
      Nat.dvd_factorial haPrime.pos haPred
    have habFactorial : a * b ∣ b ! := by
      have hbPos : 0 < b := by omega
      have hbFactorial : b ! = b * (b - 1)! := by
        simpa [Nat.sub_add_cancel hbPos] using Nat.factorial_succ (b - 1)
      calc
        a * b ∣ b * (b - 1)! := by
          simpa [Nat.mul_comm] using Nat.mul_dvd_mul haFactorial (dvd_refl b)
        _ = b ! := hbFactorial.symm
    exact hab ▸ habFactorial.trans (Nat.factorial_dvd_factorial hbp.le)
  · have habEq : a = b := Nat.le_antisymm habOrder (Nat.le_of_not_gt habLt)
    have hmSquare : m = a * a := by rw [← hab, habEq]
    have hp5 : 5 ≤ p := hmax 5 Nat.prime_five hn
    have haNeTwo : a ≠ 2 := by
      intro ha
      have hm4 : m = 4 := by simpa [ha] using hmSquare
      omega
    have h2ap : 2 * a ≤ p := by
      by_cases haThree : a = 3
      · have hm9 : m = 9 := by simpa [haThree] using hmSquare
        have h7n : 7 ≤ n := by
          omega
        have hp7 : 7 ≤ p := hmax 7 Nat.prime_seven h7n
        omega
      · have ha5 : 5 ≤ a :=
          haPrime.five_le_of_ne_two_of_ne_three haNeTwo haThree
        obtain ⟨s, hsPrime, h2as, hs4a⟩ :=
          Nat.exists_prime_lt_and_le_two_mul (2 * a) (by omega)
        have h4aSquare : 2 * (2 * a) ≤ a * a := by
          calc
            2 * (2 * a) = 4 * a := by omega
            _ ≤ a * a := Nat.mul_le_mul_right a (by omega)
        have hsn : s ≤ n := by
          calc
            s ≤ 2 * (2 * a) := hs4a
            _ ≤ a * a := h4aSquare
            _ = m := hmSquare.symm
            _ ≤ n := hm.2
        exact h2as.le.trans (hmax s hsPrime hsn)
    have haFactorial : a ∣ a ! := Nat.dvd_factorial haPrime.pos le_rfl
    have haSquareFactorial : a * a ∣ (2 * a)! := by
      simpa [two_mul] using
        (Nat.mul_dvd_mul haFactorial haFactorial).trans
          (Nat.factorial_mul_factorial_dvd_factorial_add a a)
    exact hmSquare.symm ▸
      haSquareFactorial.trans (Nat.factorial_dvd_factorial h2ap)

/-- Perry's A094802 conjecture, stated without introducing a largest-prime function. -/
theorem result (n p : ℕ) (hn : 5 ≤ n) (hp : p.Prime) (hpn : p ≤ n)
    (hmax : ∀ q, q.Prime → q ≤ n → q ≤ p) :
    IsLeast {k : ℕ | Nat.lcmUpto n ∣ (k !)} p := by
  refine ⟨prefix_lcm_dvd_factorial_of_maximal_prime n p hn hp hmax, ?_⟩
  intro k hk
  apply hp.dvd_factorial.mp
  apply Nat.dvd_trans ?_ hk
  unfold Nat.lcmUpto
  apply Finset.dvd_lcm
  exact Finset.mem_Icc.mpr ⟨hp.pos, hpn⟩

#print axioms prefix_lcm_dvd_factorial_of_maximal_prime
#print axioms result

end D5.S3.Factorization.PerryLeastFactorialDivisibleByPrefixLcm
