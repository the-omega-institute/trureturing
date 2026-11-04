/- GID: D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts
   generality: I
   mirror-B: D5/B/S3/Arith/Factorization/OeisA343881KageyPowerProducts
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.claim; result=D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.result; claim=D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.claim
   digest: The exponent coordinates of 12 and 72 refute eventual equality in A343881. -/
/-
result: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies:
  D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates.firstSuccess
    declaration statement_id: sha256:89650709672e1beaa0cd3fca68036536bad4a2805dd3a0651c23e3f573a84352
  D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates.firstSuccess_eq_find
    declaration statement_id: sha256:454734b615edf2d6da5c0bbb9ea3cd480213d8e629e4f4aa3766dd013226cb9a
  Consumers: none (settling result).
not_works_seventy_two: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none. Consumer: result.
defined_at_twelve: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none. Consumer: result.
Works, A064549, claim: source definitions; Direct frozen dependencies: none.
The minimum expression is inlined in claim; its proof uses the existing firstSuccess owner.
admission_basis: open-problem-resolution (#18686; Refuted)
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

set_option autoImplicit false

namespace D5.S3.Arith.Factorization.OeisA343881KageyPowerProducts

open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates (firstSuccess firstSuccess_eq_find)

/-- `k^x * m^y = c^n` for some positive integers `c`, `x` and `y` where `x < n` and `y < n`. -/
def Works (n k m : ℕ) : Prop :=
  ∃ c x y : ℕ, 0 < c ∧ 0 < x ∧ 0 < y ∧ x < n ∧ y < n ∧ k ^ x * m ^ y = c ^ n

/-- A064549: `a(n) = n * Product_{primes p|n} p`. -/
def A064549 (k : ℕ) : ℕ := k * ∏ p ∈ k.primeFactors, p

open Classical in
/-- A343881 ("Conjecture: T(p,k) = A064549(k) for fixed k > 1 and sufficiently large p."), with `p`
prime. -/
def claim : Prop := ∀ k : ℕ, 1 < k → ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
  (if h : ∃ m, k < m ∧ Works p k m then Nat.find h else 0) = A064549 k


private theorem not_works_seventy_two (n : ℕ) : ¬ Works n 12 72 := by
  rintro ⟨c, x, y, hc, hx, hy, hxn, hyn, hpow⟩
  have f12 : (12 : ℕ).factorization = 2 • (2 : ℕ).factorization + (3 : ℕ).factorization := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  have f72 : (72 : ℕ).factorization = 3 • (2 : ℕ).factorization + 2 • (3 : ℕ).factorization := by
    rw [show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow,
      Nat.factorization_pow]
  have hv (q : ℕ) : x * (12 : ℕ).factorization q + y * (72 : ℕ).factorization q =
      n * c.factorization q := by
    have h := congrArg (fun z : ℕ => z.factorization q) hpow
    simpa only [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (12 : ℕ) ≠ 0))
      (pow_ne_zero _ (by norm_num : (72 : ℕ) ≠ 0)), Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] using h
  have h2 : 2 * x + 3 * y = n * c.factorization 2 := by
    have h := hv 2
    norm_num [f12, f72, Nat.prime_two.factorization, Nat.prime_three.factorization] at h
    simp only [Nat.factorization_def _ Nat.prime_two] at h ⊢
    omega
  have h3 : x + 2 * y = n * c.factorization 3 := by
    have h := hv 3
    norm_num [f12, f72, Nat.prime_two.factorization, Nat.prime_three.factorization] at h
    simp only [Nat.factorization_def _ Nat.prime_three] at h ⊢
    omega
  have d2 : n ∣ 2 * x + 3 * y := ⟨c.factorization 2, h2⟩
  have d3 : n ∣ x + 2 * y := ⟨c.factorization 3, h3⟩
  have dy : n ∣ y := by
    have hd := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd d3 2) d2
    have he : 2 * (x + 2 * y) - (2 * x + 3 * y) = y := by omega
    rwa [he] at hd
  have hnle : n ≤ y := Nat.le_of_dvd hy dy
  omega

private theorem defined_at_twelve (p : ℕ) (hp : p.Prime) : ∃ m, 12 < m ∧ Works p 12 m := by
  by_cases hp2 : p = 2
  · subst p
    exact ⟨27, by norm_num, 18, 1, 1, by norm_num⟩
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    refine ⟨144, by norm_num, 12, p - 2, 1, by norm_num, by omega,
      by norm_num, by omega, by omega, ?_⟩
    rw [pow_one, show (144 : ℕ) = 12 ^ 2 by norm_num, ← pow_add,
      Nat.sub_add_cancel (by omega : 2 ≤ p)]

theorem result : ¬ D5.S3.Arith.Factorization.OeisA343881KageyPowerProducts.claim := by
  classical
  intro hclaim
  obtain ⟨N, hN⟩ := hclaim 12 (by norm_num)
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  have ha : A064549 12 = 72 := by
    have h : Nat.primeFactors 12 = {2, 3} := by
      rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.prime_three.primeFactors]
      rfl
    simp [A064549, h]
  let P : ℕ → Prop := fun m => 12 < m ∧ Works p 12 m
  have he := defined_at_twelve p hp
  have hmin : @Nat.find P (Classical.decPred P) he = Nat.find he := by
    exact Nat.find.congr_simp rfl he
  have ht : firstSuccess P = 72 := by
    rw [firstSuccess_eq_find he, hmin]
    have h := (hN p hp hNp).trans ha
    rwa [dite_eq_left he] at h
  have hw : Works p 12 (firstSuccess P) := by
    rw [firstSuccess_eq_find he]
    exact (@Nat.find_spec P (Classical.decPred P) he).2
  exact not_works_seventy_two p (ht ▸ hw)

end D5.S3.Arith.Factorization.OeisA343881KageyPowerProducts
