/- GID: D5/S3/Arith/FactorialRatio/BalaA361034Parity
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaA361034Parity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's A361034 factorial quotient is odd exactly at shifted powers of two. -/

/-
escape_witness: of_digits_sum_one
admission_basis: open-problem-resolution (#18606; Proved)
Direct frozen dependencies: the declarations listed below belong to
D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.
The scoped report records declaration statement_id values:
  mul_div_reduce = sha256:efd40ec129eaf47b98931b54d218f23ba6af1038ded8e8765adab500e978e1c9;
  factorial_prod_dvd_of_floor = sha256:50335c191d9334cd159b0c8f8c463c3090bb5624f2a0108461ea86f752952f0e.
No module pin is used as a declaration ID.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21857
The sequence and claim use the source expressions with natural division.
The shared quotient_odd theorem is also used by BalaA361035Parity.result.
Declarations (same-delivery helpers expanded for proof classification):
  quartic_floor: proof_shape: bind-only; escape_witness: none; consumers: rough_integrality.
    Direct frozen dependencies: OeisA347854BalaHalfIndexIntegral.mul_div_reduce.
  rough_integrality: proof_shape: bind-only; escape_witness: none; consumers: integrality.
    Direct frozen dependencies: OeisA347854BalaHalfIndexIntegral.mul_div_reduce, OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor.
  binary_factorial_balance: proof_shape: bind-only; escape_witness: none; consumers: integrality, quotient_valuation.
    Direct frozen dependencies: none.
  factorial_four: proof_shape: bind-only; escape_witness: none; consumers: integrality, quotient_valuation.
    Direct frozen dependencies: none.
  integrality: proof_shape: bind-only; escape_witness: none; consumers: quotient_valuation, quotient_odd.
    Direct frozen dependencies: OeisA347854BalaHalfIndexIntegral.mul_div_reduce, OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor.
  quotient_valuation: proof_shape: bind-only; escape_witness: none; consumers: quotient_odd.
    Direct frozen dependencies: OeisA347854BalaHalfIndexIntegral.mul_div_reduce, OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor.
  of_digits_sum_zero: proof_shape: bind-only; escape_witness: none; consumers: of_digits_sum_one.
    Direct frozen dependencies: none.
  of_digits_sum_one: proof_shape: content; escape_witness: of_digits_sum_one; consumers: binary_sum_one.
    Direct frozen dependencies: none.
  binary_sum_one: proof_shape: content; escape_witness: of_digits_sum_one; consumers: quotient_odd.
    Direct frozen dependencies: none.
  quotient_odd: proof_shape: content; escape_witness: of_digits_sum_one; consumers: result, BalaA361035Parity.result.
    Direct frozen dependencies: OeisA347854BalaHalfIndexIntegral.mul_div_reduce, OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor.
  a: proof_shape: bind-only; escape_witness: none; consumers: claim, result.
    Direct frozen dependencies: none.
  claim: proof_shape: bind-only; escape_witness: none; consumers: result.
    Direct frozen dependencies: none.
  result: proof_shape: content; escape_witness: of_digits_sum_one; consumers: settling result.
    Direct frozen dependencies: OeisA347854BalaHalfIndexIntegral.mul_div_reduce, OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor.
-/

import D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.Arith.FactorialRatio.BalaA361034Parity
open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

private lemma quartic_floor (n j q : ℕ) (hq : 0 < q) :
    n / q + 3 * ((n + j) / q) + j / q ≤ (4 * n) / q + (4 * j) / q := by
  rw [mul_div_reduce 4 n q hq, mul_div_reduce 4 j q hq, Nat.add_div hq]
  split_ifs with hc
  · have hlow : 4 ≤ (4 * (n % q) + 4 * (j % q)) / q := by
      apply (Nat.le_div_iff_mul_le hq).2
      omega
    have hu := Nat.add_div_le_div_add_div_add_one (4 * (n % q)) (4 * (j % q)) q
    omega
  · have hzero : 0 ≤ (4 * (n % q)) / q + (4 * (j % q)) / q := Nat.zero_le _
    omega

private lemma rough_integrality (n j : ℕ) :
    n.factorial * (n + j).factorial ^ 3 * j.factorial ∣
      (4 * n).factorial * (4 * j).factorial := by
  have h := factorial_prod_dvd_of_floor [4*n, 4*j] [n, n+j, n+j, n+j, j]
    (by
      intro q hq
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hf := quartic_floor n j q hq
      omega)
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, one_mul, pow_succ, pow_zero, mul_assoc] using h

private lemma binary_factorial_balance (n : ℕ) :
    n.factorial.factorization 2 + (Nat.digits 2 n).sum = n := by
  have h := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  have hs := Nat.digit_sum_le 2 n
  norm_num at h
  omega

private lemma factorial_four (n : ℕ) :
    (4*n).factorial.factorization 2 = n.factorial.factorization 2 + 3*n := by
  have h1 := Nat.factorization_factorial_mul (n := n) Nat.prime_two
  have h2 := Nat.factorization_factorial_mul (n := 2*n) Nat.prime_two
  norm_num [← mul_assoc] at h1 h2
  omega

private lemma integrality (C j n : ℕ) (hC : 0 < C) (hj : 0 < j)
    (hc : 8 * j.factorial * C = (4*j).factorial)
    (hv : C.factorization 2 = 3*j-3) :
    n.factorial * (n+j).factorial^3 ∣ C * (4*n).factorial := by
  have hr := rough_integrality n j
  have hr' : j.factorial * (n.factorial * (n+j).factorial^3) ∣
      j.factorial * (8 * (C * (4*n).factorial)) := by
    convert hr using 1 <;> (try rw [← hc]) <;> ring
  have hd : n.factorial * (n+j).factorial^3 ∣ 8 * (C * (4*n).factorial) :=
    Nat.dvd_of_mul_dvd_mul_left (Nat.factorial_pos j) hr'
  apply (Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)).mp
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    have hf := factorial_four n
    have hb := binary_factorial_balance (n+j)
    have hs : 0 < (Nat.digits 2 (n+j)).sum :=
      List.sum_pos_iff_exists_pos_nat.mpr
        ⟨_, List.getLast_mem (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)),
          Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 (by omega))⟩
    simp only [Nat.factorization_mul (by positivity : n.factorial ≠ 0)
        (by positivity : (n+j).factorial^3 ≠ 0),
      Nat.factorization_mul (by omega : C ≠ 0) (Nat.factorial_ne_zero (4*n)),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    omega
  · have h := (Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)).mpr hd p hp
    have h8 : (8:ℕ).factorization p = 0 := by
      rw [show (8:ℕ) = 2^3 from rfl, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      rw [Nat.factorization_eq_zero_of_not_dvd (by
        intro hdiv
        have := (Nat.dvd_prime Nat.prime_two).1 hdiv
        rcases this with h | h
        · exact hp.ne_one h
        · exact hp2 h)]
    simpa only [Nat.factorization_mul (by decide : (8:ℕ) ≠ 0)
      (by positivity : C * (4*n).factorial ≠ 0), Finsupp.add_apply, h8, zero_add] using h

private lemma quotient_valuation (C j n : ℕ) (hC : 0 < C) (hj : 0 < j)
    (hc : 8 * j.factorial * C = (4*j).factorial)
    (hv : C.factorization 2 = 3*j-3) :
    (C * (4*n).factorial / (n.factorial * (n+j).factorial^3)).factorization 2 =
      3 * ((Nat.digits 2 (n+j)).sum - 1) := by
  rw [Nat.factorization_div (integrality C j n hC hj hc hv)]
  simp only [Finsupp.tsub_apply,
    Nat.factorization_mul (by omega : C ≠ 0) (Nat.factorial_ne_zero (4*n)),
    Nat.factorization_mul (Nat.factorial_ne_zero n) (by positivity : (n+j).factorial^3 ≠ 0),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hf := factorial_four n
  have hb := binary_factorial_balance (n+j)
  have hs : 0 < (Nat.digits 2 (n+j)).sum :=
      List.sum_pos_iff_exists_pos_nat.mpr
        ⟨_, List.getLast_mem (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)),
          Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 (by omega))⟩
  omega

private lemma of_digits_sum_zero (b : ℕ) (L : List ℕ) (hL : L.sum = 0) :
    Nat.ofDigits b L = 0 := by
  induction L
  case nil => rfl
  case cons d L ih =>
    simp only [List.sum_cons] at hL
    have hd : d = 0 := by exact Nat.eq_zero_of_add_eq_zero_right hL
    have ht : L.sum = 0 := by exact Nat.eq_zero_of_add_eq_zero_left hL
    simp [Nat.ofDigits_cons, hd, ih ht]

private lemma of_digits_sum_one (b : ℕ) (L : List ℕ) (hL : L.sum = 1) :
    ∃ k : ℕ, Nat.ofDigits b L = b^k := by
  induction L
  case nil => simp at hL
  case cons d L ih =>
    simp only [List.sum_cons] at hL
    by_cases hd : d = 0
    · subst d
      obtain ⟨k, hk⟩ := ih (by omega)
      exact ⟨k+1, by simp [Nat.ofDigits_cons, hk, pow_succ']⟩
    · have hd1 : d = 1 := by omega
      exact ⟨0, by simp [Nat.ofDigits_cons, hd1, of_digits_sum_zero b L (by omega)]⟩

private lemma binary_sum_one (m : ℕ) :
    (Nat.digits 2 m).sum = 1 ↔ ∃ k : ℕ, m = 2^k := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := of_digits_sum_one 2 (Nat.digits 2 m) h
    exact ⟨k, by simpa only [Nat.ofDigits_digits] using hk⟩
  · rintro ⟨k,rfl⟩
    rw [show (2:ℕ)^k = 2^k * 1 by omega, Nat.digits_base_pow_mul (by decide) (by decide)]
    simp

lemma quotient_odd (C j n : ℕ) (hC : 0 < C) (hj : 0 < j)
    (hc : 8 * j.factorial * C = (4*j).factorial)
    (hv : C.factorization 2 = 3*j-3) :
    Odd (C * (4*n).factorial / (n.factorial * (n+j).factorial^3)) ↔
      ∃ k : ℕ, n+j = 2^k := by
  have hd := integrality C j n hC hj hc hv
  have hq : C * (4*n).factorial / (n.factorial * (n+j).factorial^3) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (by positivity) hd) (by positivity)).ne'
  have hz := Nat.factorization_eq_zero_iff
    (C * (4*n).factorial / (n.factorial * (n+j).factorial^3)) 2
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  rw [← show (C * (4*n).factorial / (n.factorial * (n+j).factorial^3)).factorization 2 = 0 ↔
    ¬2 ∣ C * (4*n).factorial / (n.factorial * (n+j).factorial^3) by
      simpa only [Nat.prime_two, not_true_eq_false, hq, or_false, false_or] using hz]
  rw [quotient_valuation C j n hC hj hc hv]
  have hs : 0 < (Nat.digits 2 (n+j)).sum :=
      List.sum_pos_iff_exists_pos_nat.mpr
        ⟨_, List.getLast_mem (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)),
          Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 (by omega))⟩
  rw [show 3 * ((Nat.digits 2 (n+j)).sum - 1) = 0 ↔ (Nat.digits 2 (n+j)).sum = 1 by omega]
  exact binary_sum_one (n+j)


/-- `a(n) = 2520*(4*n)!/(n!*(n+2)!^3)`. -/
def a (n : ℕ) : ℕ := 2520 * (4 * n).factorial / (n.factorial * (n + 2).factorial ^ 3)

/-- The conjecture of A361034: `a(n)` is odd iff `n = 2^k - 2` for some `k >= 1`. -/
def claim : Prop := ∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 2


theorem result : claim := by
  intro n
  have h := D5.S3.Arith.FactorialRatio.BalaA361034Parity.quotient_odd 2520 2 n (by decide) (by decide)
    (by norm_num [Nat.factorial]) (by decide +kernel)
  change Odd (2520 * (4*n).factorial / (n.factorial * (n+2).factorial^3)) ↔ _
  rw [h]
  constructor
  · rintro ⟨k, hk⟩
    have hkm : 1 ≤ k := by
      by_contra hlt
      have hh : k < 1 := by exact Nat.lt_of_not_le hlt
      interval_cases k; norm_num at hk
    exact ⟨k, hkm, by omega⟩
  · rintro ⟨k, hkm, hk⟩
    have hp : 2 ≤ (2:ℕ)^k := by
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hkm
      norm_num at hh
      omega
    exact ⟨k, by omega⟩

end D5.S3.Arith.FactorialRatio.BalaA361034Parity
