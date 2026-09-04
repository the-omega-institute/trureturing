/- GID: D5/S3/PrimeForms/PrimaryPseudoperfectPorts
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PrimaryPseudoperfectPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Primary pseudoperfect numbers have exact reciprocal and prime-extension laws. -/

import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository searches for `IsPPN`, `squarefreeDeriv`, primary pseudoperfect numbers,
     Egyptian-fraction characterizations, and the corresponding prime-factor sums found no
     existing D5 declaration.
   * Pinned Mathlib has no primary-pseudoperfect predicate or reciprocal-sum theorem. Its exact
     supporting lemmas `Nat.cast_div`, `Nat.dvd_of_mem_primeFactors`, and
     `Nat.prime_of_mem_primeFactors` are used below instead of reproving cast or divisor facts.
   * The nonzero hypothesis on the reciprocal theorem excludes Lean's totalized `1 / 0 = 0`.
-/

namespace D5.S3.PrimeForms.PrimaryPseudoperfectPorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The sum of `n / p` over the distinct prime divisors of `n`. -/
def squarefreeDeriv (n : Nat) : Nat :=
  ∑ p ∈ n.primeFactors, n / p

/-- A primary pseudoperfect number is a nontrivial squarefree natural whose prime-factor
quotients sum to one less than the number. -/
def IsPPN (n : Nat) : Prop :=
  Squarefree n ∧ 1 < n ∧ n = 1 + squarefreeDeriv n

/-- Casting the quotient sum to the rationals turns it into `n` times the reciprocal-prime sum.
This is the arithmetic bridge used by both directions of the characterization. -/
theorem squarefreeDeriv_cast (n : Nat) :
    (squarefreeDeriv n : Rat) =
      (n : Rat) * ∑ p ∈ n.primeFactors, 1 / (p : Rat) := by
  classical
  rw [squarefreeDeriv, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp)]
  · ring
  · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- For a nonzero natural, the Egyptian-fraction identity is equivalent to the integral
quotient-sum identity. -/
theorem reciprocal_sum_eq_one_iff (n : Nat) (hn : n ≠ 0) :
    1 / (n : Rat) + ∑ p ∈ n.primeFactors, 1 / (p : Rat) = 1 ↔
      n = 1 + squarefreeDeriv n := by
  let reciprocalSum : Rat := ∑ p ∈ n.primeFactors, 1 / (p : Rat)
  have hnRat : (n : Rat) ≠ 0 := by exact_mod_cast hn
  have hcast : (squarefreeDeriv n : Rat) = (n : Rat) * reciprocalSum := by
    simpa [reciprocalSum] using squarefreeDeriv_cast n
  change 1 / (n : Rat) + reciprocalSum = 1 ↔ n = 1 + squarefreeDeriv n
  constructor
  · intro hreciprocal
    have hRat : (n : Rat) = 1 + (squarefreeDeriv n : Rat) := by
      calc
        (n : Rat) = (n : Rat) * 1 := by ring
        _ = (n : Rat) * (1 / (n : Rat) + reciprocalSum) := by rw [hreciprocal]
        _ = 1 + (n : Rat) * reciprocalSum := by field_simp [hnRat]
        _ = 1 + (squarefreeDeriv n : Rat) := by rw [← hcast]
    exact_mod_cast hRat
  · intro hintegral
    have hRat : (n : Rat) = 1 + (squarefreeDeriv n : Rat) := by
      exact_mod_cast hintegral
    calc
      1 / (n : Rat) + reciprocalSum =
          (1 + (n : Rat) * reciprocalSum) / (n : Rat) := by
            field_simp [hnRat]
      _ = (n : Rat) / (n : Rat) := by rw [← hcast, ← hRat]
      _ = 1 := div_self hnRat

/-- Primary pseudoperfectness is exactly squarefreeness, nontriviality, and the reciprocal-sum
identity over the distinct prime factors. -/
theorem isPPN_iff_reciprocal_sum (n : Nat) :
    IsPPN n ↔
      Squarefree n ∧ 1 < n ∧
        1 / (n : Rat) + ∑ p ∈ n.primeFactors, 1 / (p : Rat) = 1 := by
  constructor
  · rintro ⟨hsquarefree, hn, hderiv⟩
    exact ⟨hsquarefree, hn, (reciprocal_sum_eq_one_iff n (by omega)).2 hderiv⟩
  · rintro ⟨hsquarefree, hn, hreciprocal⟩
    exact ⟨hsquarefree, hn, (reciprocal_sum_eq_one_iff n (by omega)).1 hreciprocal⟩

/-- Adjoining a new prime multiplies every old quotient by that prime and contributes the old
number as the one new quotient. -/
theorem squarefreeDeriv_mul_prime (K p : Nat) (hK : K ≠ 0) (hp : p.Prime)
    (hpK : ¬p ∣ K) :
    squarefreeDeriv (K * p) = p * squarefreeDeriv K + K := by
  classical
  have hpNotMem : p ∉ K.primeFactors := by
    intro hpMem
    exact hpK (Nat.dvd_of_mem_primeFactors hpMem)
  have hdisjoint : Disjoint K.primeFactors {p} :=
    Finset.disjoint_singleton_right.mpr hpNotMem
  rw [squarefreeDeriv, Nat.primeFactors_mul hK hp.ne_zero, hp.primeFactors,
    Finset.sum_union hdisjoint, Finset.sum_singleton]
  calc
    (∑ r ∈ K.primeFactors, K * p / r) + K * p / p =
        (∑ r ∈ K.primeFactors, p * (K / r)) + K := by
      congr 1
      · apply Finset.sum_congr rfl
        intro r hr
        rw [mul_comm K p, Nat.mul_div_assoc p (Nat.dvd_of_mem_primeFactors hr)]
      · simpa [mul_comm] using Nat.mul_div_right K hp.pos
    _ = p * squarefreeDeriv K + K := by rw [squarefreeDeriv, Finset.mul_sum]

/-- Adjoining two distinct new primes gives the corresponding two-step quotient expansion. -/
theorem squarefreeDeriv_mul_two_primes (K p q : Nat) (hK : K ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpK : ¬p ∣ K) (hqK : ¬q ∣ K) (hpq : p ≠ q) :
    squarefreeDeriv (K * p * q) = q * (p * squarefreeDeriv K + K) + K * p := by
  have hqKp : ¬q ∣ K * p := by
    intro hqProduct
    rcases hq.dvd_mul.mp hqProduct with hqDivK | hqDivP
    · exact hqK hqDivK
    · exact hpq ((Nat.dvd_prime_two_le hp hq.two_le).mp hqDivP).symm
  rw [squarefreeDeriv_mul_prime (K * p) q (mul_ne_zero hK hp.ne_zero) hq hqKp,
    squarefreeDeriv_mul_prime K p hK hp hpK]

/-- A primary pseudoperfect number remains primary pseudoperfect after multiplication by a prime
equal to its successor. -/
theorem isPPN_mul_succ (K : Nat) (hK : IsPPN K) (hprime : (K + 1).Prime) :
    IsPPN (K * (K + 1)) := by
  have hK0 : K ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hK.2.1)
  have hnotDvd : ¬K + 1 ∣ K :=
    Nat.not_dvd_of_pos_of_lt (by omega) (Nat.lt_succ_self K)
  have hcoprime : K.Coprime (K + 1) :=
    (hprime.coprime_iff_not_dvd.mpr hnotDvd).symm
  refine ⟨(Nat.squarefree_mul hcoprime).2 ⟨hK.1, hprime.squarefree⟩, ?_, ?_⟩
  · nlinarith [hK.2.1]
  · rw [squarefreeDeriv_mul_prime K (K + 1) hK0 hprime hnotDvd]
    nlinarith [hK.2.2]

/-- For two distinct new primes, the two-prime extension is primary pseudoperfect exactly when
the integer factor equation holds. The integral formulation avoids truncated natural subtraction. -/
theorem isPPN_mul_two_primes_iff (K p q : Nat) (hK : IsPPN K)
    (hp : p.Prime) (hq : q.Prime) (hpK : ¬p ∣ K) (hqK : ¬q ∣ K) (hpq : p ≠ q) :
    IsPPN (K * p * q) ↔
      ((p : Int) - K) * ((q : Int) - K) = (K : Int) ^ 2 + 1 := by
  have hK0 : K ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hK.2.1)
  have hqKp : ¬q ∣ K * p := by
    intro hqProduct
    rcases hq.dvd_mul.mp hqProduct with hqDivK | hqDivP
    · exact hqK hqDivK
    · exact hpq ((Nat.dvd_prime_two_le hp hq.two_le).mp hqDivP).symm
  have hcoprimeKp : K.Coprime p := (hp.coprime_iff_not_dvd.mpr hpK).symm
  have hcoprimeKpQ : (K * p).Coprime q := (hq.coprime_iff_not_dvd.mpr hqKp).symm
  have hsquarefreeKp : Squarefree (K * p) :=
    (Nat.squarefree_mul hcoprimeKp).2 ⟨hK.1, hp.squarefree⟩
  have hsquarefree : Squarefree (K * p * q) :=
    (Nat.squarefree_mul hcoprimeKpQ).2 ⟨hsquarefreeKp, hq.squarefree⟩
  have hderiv := squarefreeDeriv_mul_two_primes K p q hK0 hp hq hpK hqK hpq
  have hderivInt :
      (squarefreeDeriv (K * p * q) : Int) =
        (q : Int) * ((p : Int) * squarefreeDeriv K + K) + (K : Int) * p := by
    exact_mod_cast hderiv
  have hKInt : (K : Int) = 1 + squarefreeDeriv K := by
    exact_mod_cast hK.2.2
  constructor
  · intro hproduct
    have hproductInt' :
        (K : Int) * p * q = 1 + (squarefreeDeriv (K * p * q) : Int) := by
      exact_mod_cast hproduct.2.2
    rw [hderivInt] at hproductInt'
    have hpqInt :
        (p : Int) * q = (K : Int) * p + (K : Int) * q + 1 := by
      linear_combination hproductInt' - (p : Int) * (q : Int) * hKInt
    nlinarith [hpqInt]
  · intro hfactor
    have hpqInt :
        (p : Int) * q = (K : Int) * p + (K : Int) * q + 1 := by
      nlinarith [hfactor]
    refine ⟨hsquarefree, ?_, ?_⟩
    · nlinarith [hK.2.1, hp.two_le, hq.two_le]
    · rw [hderiv]
      have hproductInt :
          (K : Int) * p * q =
            1 + (q : Int) * ((p : Int) * squarefreeDeriv K + K) + (K : Int) * p := by
        linear_combination (p : Int) * (q : Int) * hKInt + hpqInt
      have hproductNat :
          K * p * q = 1 + q * (p * squarefreeDeriv K + K) + K * p := by
        exact_mod_cast hproductInt
      simpa [add_assoc] using hproductNat

/-- The first five primary pseudoperfect numbers satisfy the definition directly. -/
theorem primary_pseudoperfect_numerical_chain :
    IsPPN 2 ∧ IsPPN 6 ∧ IsPPN 42 ∧ IsPPN 1806 ∧ IsPPN 47058 := by
  have hderivTwo : squarefreeDeriv 2 = 1 := by
    have h := squarefreeDeriv_mul_prime 1 2 (by norm_num) Nat.prime_two (by norm_num)
    simpa [squarefreeDeriv] using h
  have htwo : IsPPN 2 := by
    exact ⟨Nat.squarefree_two, by norm_num, by omega⟩
  have hsix : IsPPN 6 := by
    simpa using isPPN_mul_succ 2 htwo (by norm_num)
  have hfortyTwo : IsPPN 42 := by
    simpa using isPPN_mul_succ 6 hsix (by norm_num)
  have heighteenOhSix : IsPPN 1806 := by
    simpa using isPPN_mul_succ 42 hfortyTwo (by norm_num)
  have hprimeEleven : Nat.Prime 11 := by norm_num
  have hprimeTwentyThree : Nat.Prime 23 := by norm_num
  have hprimeThirtyOne : Nat.Prime 31 := by norm_num
  have hsquarefreeSixtySix : Squarefree (6 * 11) :=
    (Nat.squarefree_mul (by norm_num)).2 ⟨hsix.1, hprimeEleven.squarefree⟩
  have hsquarefreeFifteenEighteen : Squarefree (6 * 11 * 23) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨hsquarefreeSixtySix, hprimeTwentyThree.squarefree⟩
  have hsquarefreeFortySevenThousand : Squarefree (6 * 11 * 23 * 31) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨hsquarefreeFifteenEighteen, hprimeThirtyOne.squarefree⟩
  have hderivSix :=
    squarefreeDeriv_mul_prime 2 3 (by norm_num) (by norm_num) (by norm_num)
  have hderivSixtySix :=
    squarefreeDeriv_mul_prime 6 11 (by norm_num) hprimeEleven (by norm_num)
  have hderivFifteenEighteen :=
    squarefreeDeriv_mul_prime 66 23 (by norm_num) hprimeTwentyThree (by norm_num)
  have hderivFortySevenThousand :=
    squarefreeDeriv_mul_prime 1518 31 (by norm_num) hprimeThirtyOne (by norm_num)
  norm_num [hderivTwo] at hderivSix
  norm_num [hderivSix] at hderivSixtySix
  norm_num [hderivSixtySix] at hderivFifteenEighteen
  norm_num [hderivFifteenEighteen] at hderivFortySevenThousand
  have hfortySevenThousand : IsPPN 47058 := by
    refine ⟨by simpa using hsquarefreeFortySevenThousand, by norm_num, ?_⟩
    omega
  exact ⟨htwo, hsix, hfortyTwo, heighteenOhSix, hfortySevenThousand⟩

#print axioms squarefreeDeriv_cast
#print axioms reciprocal_sum_eq_one_iff
#print axioms isPPN_iff_reciprocal_sum
#print axioms squarefreeDeriv_mul_prime
#print axioms squarefreeDeriv_mul_two_primes
#print axioms isPPN_mul_succ
#print axioms isPPN_mul_two_primes_iff
#print axioms primary_pseudoperfect_numerical_chain

end D5.S3.PrimeForms.PrimaryPseudoperfectPorts
