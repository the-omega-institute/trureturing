/- GID: D5/S3/PrimeForms/PrimaryPseudoperfectPorts
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PrimaryPseudoperfectPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Primary pseudoperfect numbers satisfy reciprocal, coprime-product, and port laws. -/

import Mathlib

namespace D5.S3.PrimeForms.PrimaryPseudoperfectPorts

/-- The sum of the complementary prime divisors of `n`. -/
def squarefreeDeriv (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, n / p

/-- A squarefree primary pseudoperfect number, in integral form. -/
def IsPPN (n : ℕ) : Prop :=
  Squarefree n ∧ 1 < n ∧ n = 1 + squarefreeDeriv n

/-- The natural-number residual transported through a coprime factor. -/
def portDelta (R c B : ℕ) : ℕ :=
  c * B - R * squarefreeDeriv B

/-- Multiplying the reciprocal prime-factor sum by `n` recovers its integral derivative. -/
private theorem mul_reciprocal_primeFactors {n : ℕ} :
    (n : ℚ) * (∑ p ∈ n.primeFactors, 1 / (p : ℚ)) = (squarefreeDeriv n : ℚ) := by
  rw [Finset.mul_sum]
  simp only [squarefreeDeriv, Nat.cast_sum]
  exact Finset.sum_congr rfl fun p hp ↦ by
    rw [Nat.cast_div_charZero (Nat.dvd_of_mem_primeFactors hp)]
    ring

private theorem reciprocal_eq_one_iff {n : ℕ} (hn : n ≠ 0) :
    (1 / (n : ℚ) + ∑ p ∈ n.primeFactors, 1 / (p : ℚ) = 1) ↔
      n = 1 + squarefreeDeriv n := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  constructor
  · intro h
    have hmul := congrArg (fun x : ℚ ↦ (n : ℚ) * x) h
    rw [mul_add, mul_reciprocal_primeFactors] at hmul
    simp [hnq] at hmul
    exact_mod_cast hmul.symm
  · intro h
    apply mul_left_cancel₀ hnq
    rw [mul_add, mul_reciprocal_primeFactors]
    simp [hnq]
    exact_mod_cast h.symm

private theorem isPPN_iff_reciprocal {n : ℕ} :
    IsPPN n ↔
      Squarefree n ∧ 1 < n ∧
        (1 / (n : ℚ) + ∑ p ∈ n.primeFactors, 1 / (p : ℚ) = 1) := by
  constructor
  · rintro ⟨hsq, hgt, heq⟩
    exact ⟨hsq, hgt, (reciprocal_eq_one_iff (by omega)).2 heq⟩
  · rintro ⟨hsq, hgt, heq⟩
    exact ⟨hsq, hgt, (reciprocal_eq_one_iff (by omega)).1 heq⟩

/-- The reciprocal equation is equivalent to the integral equation, and characterizes PPNs. -/
theorem reciprocal_eq_one_and_isPPN_iff (n : ℕ) :
    (n ≠ 0 →
      ((1 / (n : ℚ) + ∑ p ∈ n.primeFactors, 1 / (p : ℚ) = 1) ↔
        n = 1 + squarefreeDeriv n)) ∧
    (IsPPN n ↔
      Squarefree n ∧ 1 < n ∧
        (1 / (n : ℚ) + ∑ p ∈ n.primeFactors, 1 / (p : ℚ) = 1)) := by
  exact ⟨fun hn ↦ reciprocal_eq_one_iff hn, isPPN_iff_reciprocal⟩

private theorem mul_div_prime_factor_left
    {A B p : ℕ} (hpA : p ∣ A) : A * B / p = (A / p) * B := by
  rw [mul_comm A B, Nat.mul_div_assoc B hpA, mul_comm]

private theorem mul_div_prime_factor_right
    {A B p : ℕ} (hpB : p ∣ B) : A * B / p = A * (B / p) := by
  exact Nat.mul_div_assoc A hpB

/-- The complementary-prime-divisor sum obeys a Leibniz rule on coprime inputs. -/
theorem squarefreeDeriv_mul {A B : ℕ} (hAB : A.Coprime B) :
    squarefreeDeriv (A * B) =
      A * squarefreeDeriv B + B * squarefreeDeriv A := by
  rw [squarefreeDeriv, hAB.primeFactors_mul, Finset.sum_union hAB.disjoint_primeFactors]
  unfold squarefreeDeriv
  have hleft :
      (∑ p ∈ A.primeFactors, A * B / p) = (∑ p ∈ A.primeFactors, A / p) * B := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p hp ↦
      mul_div_prime_factor_left (Nat.dvd_of_mem_primeFactors hp)
  have hright :
      (∑ p ∈ B.primeFactors, A * B / p) = A * (∑ p ∈ B.primeFactors, B / p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp ↦
      mul_div_prime_factor_right (Nat.dvd_of_mem_primeFactors hp)
  rw [hleft, hright]
  ac_rfl

/-- Port composition substitutes the residual produced by the first coprime factor. -/
theorem portDelta_mul {A B R c : ℕ} (hAB : A.Coprime B) :
    portDelta R c (A * B) = portDelta (R * A) (portDelta R c A) B := by
  rw [portDelta, squarefreeDeriv_mul hAB, portDelta, portDelta]
  simp only [mul_add, Nat.sub_mul, Nat.sub_sub, mul_assoc]
  congr 1
  ring

/-- Extending a PPN by a coprime squarefree factor is equivalent to a unit residual. -/
theorem isPPN_mul_iff_port {K C : ℕ} (hK : IsPPN K)
    (hC : Squarefree C) (hCgt : 1 < C) (hKC : K.Coprime C) :
    IsPPN (K * C) ↔ C - K * squarefreeDeriv C = 1 := by
  rcases hK with ⟨hKsq, hKgt, hKppn⟩
  constructor
  · rintro ⟨_, _, hKCppn⟩
    rw [squarefreeDeriv_mul hKC] at hKCppn
    have hCeq : C = 1 + K * squarefreeDeriv C := by
      nlinarith
    omega
  · intro hport
    refine ⟨(Nat.squarefree_mul hKC).2 ⟨hKsq, hC⟩, ?_, ?_⟩
    · nlinarith
    · rw [squarefreeDeriv_mul hKC]
      have hCeq : C = 1 + K * squarefreeDeriv C := by
        omega
      nlinarith

@[simp]
private theorem squarefreeDeriv_prime {p : ℕ} (hp : p.Prime) :
    squarefreeDeriv p = 1 := by
  rw [squarefreeDeriv, hp.primeFactors]
  simp only [Finset.sum_singleton]
  exact Nat.div_self hp.pos

private theorem isPPN_mul_succ_of_prime {K : ℕ} (hK : IsPPN K)
    (hprime : (K + 1).Prime) : IsPPN (K * (K + 1)) := by
  apply (isPPN_mul_iff_port hK hprime.squarefree hprime.one_lt (by simp)).2
  rw [squarefreeDeriv_prime hprime]
  omega

private theorem coprime_primes_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : p.Coprime q := by
  rw [hp.coprime_iff_not_dvd]
  intro hpdivq
  rcases (Nat.dvd_prime hq).1 hpdivq with hpone | hpq'
  · exact hp.ne_one hpone
  · exact hpq hpq'

private theorem port_two_prime_algebra {K p q : ℕ} (hKp : K < p) (hKq : K < q) :
    p * q - K * (p + q) = 1 ↔ (p - K) * (q - K) = K ^ 2 + 1 := by
  have hpK : K ≤ p := Nat.le_of_lt hKp
  have hqK : K ≤ q := Nat.le_of_lt hKq
  have hpSub := Nat.sub_add_cancel hpK
  have hqSub := Nat.sub_add_cancel hqK
  constructor
  · intro hport
    have hEq : p * q = 1 + K * (p + q) := by omega
    nlinarith
  · intro hfactor
    have hEq : p * q = 1 + K * (p + q) := by nlinarith
    omega

private theorem isPPN_mul_two_primes_iff {K p q : ℕ} (hK : IsPPN K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpnK : ¬ p ∣ K) (hqnK : ¬ q ∣ K)
    (hKp : K < p) (hKq : K < q) :
    IsPPN (K * p * q) ↔ (p - K) * (q - K) = K ^ 2 + 1 := by
  have hpqcop : p.Coprime q := coprime_primes_of_ne hp hq hpq
  have hpqsq : Squarefree (p * q) :=
    (Nat.squarefree_mul hpqcop).2 ⟨hp.squarefree, hq.squarefree⟩
  have hpqgt : 1 < p * q := by nlinarith [hp.two_le, hq.two_le]
  have hKpCop : K.Coprime p := (hp.coprime_iff_not_dvd.2 hpnK).symm
  have hKqCop : K.Coprime q := (hq.coprime_iff_not_dvd.2 hqnK).symm
  have hKpq : K.Coprime (p * q) := hKpCop.mul_right hKqCop
  have hderiv : squarefreeDeriv (p * q) = p + q := by
    rw [squarefreeDeriv_mul hpqcop, squarefreeDeriv_prime hp, squarefreeDeriv_prime hq]
    omega
  rw [mul_assoc, isPPN_mul_iff_port hK hpqsq hpqgt hKpq, hderiv]
  exact port_two_prime_algebra hKp hKq

private theorem ppn_two : IsPPN 2 := by
  refine ⟨Nat.prime_two.squarefree, by norm_num, ?_⟩
  rw [squarefreeDeriv_prime Nat.prime_two]

private theorem ppn_six : IsPPN 6 := by
  simpa using isPPN_mul_succ_of_prime ppn_two (by norm_num : Nat.Prime (2 + 1))

private theorem ppn_forty_two : IsPPN 42 := by
  simpa using isPPN_mul_succ_of_prime ppn_six (by norm_num : Nat.Prime (6 + 1))

private theorem ppn_eighteen_oh_six : IsPPN 1806 := by
  simpa using isPPN_mul_succ_of_prime ppn_forty_two (by norm_num : Nat.Prime (42 + 1))

private theorem ppn_forty_seven_thousand_fifty_eight : IsPPN 47058 := by
  have hC : Squarefree 7843 := by
    rw [show 7843 = 11 * (23 * 31) by norm_num]
    exact (Nat.squarefree_mul (by norm_num : Nat.Coprime 11 (23 * 31))).2
      ⟨(by norm_num : Nat.Prime 11).squarefree,
        (Nat.squarefree_mul (by norm_num : Nat.Coprime 23 31)).2
          ⟨(by norm_num : Nat.Prime 23).squarefree,
            (by norm_num : Nat.Prime 31).squarefree⟩⟩
  have hcop : Nat.Coprime 6 7843 := by norm_num
  have hderiv : squarefreeDeriv 7843 = 1307 := by
    conv_lhs => rw [show 7843 = 11 * (23 * 31) by norm_num]
    rw [squarefreeDeriv_mul (by norm_num : Nat.Coprime 11 (23 * 31)),
      squarefreeDeriv_mul (by norm_num : Nat.Coprime 23 31),
      squarefreeDeriv_prime (by norm_num : Nat.Prime 11),
      squarefreeDeriv_prime (by norm_num : Nat.Prime 23),
      squarefreeDeriv_prime (by norm_num : Nat.Prime 31)]
  have h : IsPPN (6 * 7843) :=
    (isPPN_mul_iff_port ppn_six hC (by norm_num) hcop).2 (by rw [hderiv])
  norm_num at h ⊢
  exact h

/-- The one-prime and two-prime inheritance laws, together with the first five PPNs. -/
theorem isPPN_companions :
    (∀ {K : ℕ}, IsPPN K → (K + 1).Prime → IsPPN (K * (K + 1))) ∧
    (∀ {K p q : ℕ}, IsPPN K → p.Prime → q.Prime → p ≠ q →
      ¬ p ∣ K → ¬ q ∣ K → K < p → K < q →
      (IsPPN (K * p * q) ↔ (p - K) * (q - K) = K ^ 2 + 1)) ∧
    (IsPPN 2 ∧ IsPPN 6 ∧ IsPPN 42 ∧ IsPPN 1806 ∧ IsPPN 47058) := by
  refine ⟨?_, ?_, ppn_two, ppn_six, ppn_forty_two,
    ppn_eighteen_oh_six, ppn_forty_seven_thousand_fifty_eight⟩
  · exact fun hK hprime ↦ isPPN_mul_succ_of_prime hK hprime
  · exact fun hK hp hq hpq hpnK hqnK hKp hKq ↦
      isPPN_mul_two_primes_iff hK hp hq hpq hpnK hqnK hKp hKq

-- Fidelity witnesses: the domains are inhabited and every conditional hypothesis is satisfiable.
example : ℕ := 2

example : (2 : ℕ) ≠ 0 := by norm_num

example : Nat.Coprime 2 3 := by norm_num

example : IsPPN 2 ∧ Squarefree 3 ∧ 1 < 3 ∧ Nat.Coprime 2 3 := by
  exact ⟨ppn_two, (by norm_num : Nat.Prime 3).squarefree, by norm_num, by norm_num⟩

example :
    IsPPN 2 ∧ Nat.Prime 3 ∧ Nat.Prime 7 ∧ 3 ≠ 7 ∧
      ¬ 3 ∣ 2 ∧ ¬ 7 ∣ 2 ∧ 2 < 3 ∧ 2 < 7 := by
  exact ⟨ppn_two, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

end D5.S3.PrimeForms.PrimaryPseudoperfectPorts

#print axioms D5.S3.PrimeForms.PrimaryPseudoperfectPorts.reciprocal_eq_one_and_isPPN_iff
#print axioms D5.S3.PrimeForms.PrimaryPseudoperfectPorts.squarefreeDeriv_mul
#print axioms D5.S3.PrimeForms.PrimaryPseudoperfectPorts.portDelta_mul
#print axioms D5.S3.PrimeForms.PrimaryPseudoperfectPorts.isPPN_mul_iff_port
#print axioms D5.S3.PrimeForms.PrimaryPseudoperfectPorts.isPPN_companions
