/- GID: D5/S3/Arith/Congruence/HannaPrimePowerCorrection
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/HannaPrimePowerCorrection
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral square-weight corrections equal p minus one at every positive prime power. -/

/-
Paul D. Hanna, OEIS A384819, revision 14, COMMENTS:
"Conjecture: a(p^n) = p - 1 when p is prime for n >= 1."
admission_basis: open-problem-resolution (#21787; Proved)
IsCorrection: proof_shape: bind-only (definition); escape_witness: none;
  consumers: claim, correction_ghost, result; Direct frozen dependencies: F1.
claim: proof_shape: bind-only (definition); escape_witness: none;
  consumers: result; Direct frozen dependencies: F1.
correction_ghost: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F1, F4, F2, F5.
prime_power_difference: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F2, F3.
bounded_prime_powers: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: none.
result: proof_shape: bind-only; escape_witness: none;
  consumers: none (settling result); Direct frozen dependencies: F1, F4, F2, F3, F5.
Direct frozen dependencies (same-delivery definitions and proofs inlined):
F2, F3 and F5 identify the frozen private baseline declarations; their original
statements and proofs are public in the owner source and require an owner re-pin.
F1: D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.IntegralSeries
  statement_id: sha256:63e70f464749e368856bfaa91133b0adfeda478327572310319dbf6077b632cb
F2: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.divisorGhost
  statement_id: sha256:21956ccba4e2bdcbe6fcfaf5b134408727aa6d13d982fd91797da7202f724a89
F3: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.divisor_ghost_gauss
  statement_id: sha256:a84a3717291a6bc1ccaff8862f6fb8f2ace466334b087eb4df46a014e1146c46
F4: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponentialSum
  statement_id: sha256:011c3ffffaa4e8d1dcbdeb263ad502ee54def47d35b5b4b833b360f4360f996e
F5: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.integral_input_ledger
  statement_id: sha256:253bdd2ac3ba2a10cf4c8a1e8b766071033402a664e185b0a0b964b3bc943690
The source exponential is written literally in IsCorrection; proofs use the existing
exponentialSum through definitional correspondence.
The public integral_input_ledger, divisorGhost and divisor_ghost_gauss are reused from
D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25058
No nonnegative ledger or exponential-coefficient assumption is imposed.
The proof is symbolic and quantifies over all primes and positive exponents.
-/

import D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

/-! Bounded integral square-weight corrections stabilize on prime-power chains. -/

namespace D5.S3.Arith.Congruence.HannaPrimePowerCorrection

open PowerSeries Finset
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)
open D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
  (exponentialSum integral_input_ledger divisorGhost divisor_ghost_gauss)

/-- The bounds and formal integral-coefficient condition in A384819's NAME. -/
def IsCorrection (a : ℕ → ℤ) : Prop :=
  (∀ m : ℕ, 1 ≤ m → 0 ≤ a m ∧ a m < (m : ℤ)) ∧
    IntegralSeries (PowerSeries.subst
      (PowerSeries.mk fun m =>
        if m = 0 then 0 else ((m : ℚ) ^ 2 - (a m : ℚ)) / (m : ℚ))
      (PowerSeries.exp ℚ))

/-- The sole COMMENTS conjecture of OEIS A384819, including every prime. -/
def claim : Prop :=
  ∀ a : ℕ → ℤ, IsCorrection a →
    ∀ (p : ℕ) (r : ℕ), Nat.Prime p → 1 ≤ r → a (p ^ r) = (p : ℤ) - 1

private theorem correction_ghost (a : ℕ → ℤ) (ha : IsCorrection a) :
    ∃ c : ℕ → ℤ, ∀ m : ℕ, m ≠ 0 →
      (m : ℤ) ^ 2 - a m = ∑ d ∈ m.divisors, (d : ℤ) * c d := by
  have hi : IntegralSeries (exponentialSum (fun m => (m : ℚ) ^ 2 - (a m : ℚ))) := ha.2
  obtain ⟨c, hc⟩ := integral_input_ledger _ hi
  refine ⟨c, ?_⟩
  intro m hm
  have h := hc m (Nat.pos_of_ne_zero hm)
  dsimp only [divisorGhost] at h
  exact_mod_cast h

private theorem prime_power_difference (a c : ℕ → ℤ)
    (hc : ∀ m : ℕ, m ≠ 0 → (m : ℤ) ^ 2 - a m =
      ∑ d ∈ m.divisors, (d : ℤ) * c d)
    (p : ℕ) (hp : p.Prime) (k : ℕ) :
    (p : ℤ) ^ (k + 1) ∣
      ((p ^ (k + 1) : ℕ) : ℤ) ^ 2 - a (p ^ (k + 1)) -
      (((p ^ k : ℕ) : ℤ) ^ 2 - a (p ^ k)) := by
  rw [hc _ (pow_ne_zero _ hp.ne_zero), hc _ (pow_ne_zero _ hp.ne_zero)]
  simpa only [one_mul, divisorGhost] using (divisor_ghost_gauss c p hp k 1 Nat.one_pos)

private theorem bounded_prime_powers (a : ℕ → ℤ)
    (ha : ∀ m : ℕ, 1 ≤ m → 0 ≤ a m ∧ a m < (m : ℤ))
    (hd : ∀ (p : ℕ), p.Prime → ∀ k : ℕ,
      (p : ℤ) ^ (k + 1) ∣
        ((p ^ (k + 1) : ℕ) : ℤ) ^ 2 - a (p ^ (k + 1)) -
        (((p ^ k : ℕ) : ℤ) ^ 2 - a (p ^ k))) :
    ∀ (p r : ℕ), p.Prime → 1 ≤ r → a (p ^ r) = (p : ℤ) - 1 := by
  intro p r hp hr
  have h1 : a 1 = 0 := by
    have := ha 1 le_rfl
    norm_num at this
    omega
  have hpZ : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hall : ∀ k : ℕ, a (p ^ (k + 1)) = (p : ℤ) - 1 := by
    intro k
    induction k with
    | zero =>
      have h := hd p hp 0
      simp only [Nat.zero_add, pow_one, pow_zero, Nat.cast_one, one_pow, h1, sub_zero] at h
      have hz : (p : ℤ) ∣ a p - ((p : ℤ) - 1) := by
        have hsq : (p : ℤ) ∣ (p : ℤ) ^ 2 := dvd_pow_self _ (by omega)
        convert (hsq.sub h).sub (dvd_refl (p : ℤ)) using 1; ring
      have hb := ha p hp.pos
      have hm := (Int.modEq_iff_dvd.mpr hz).symm.eq
      rw [Int.emod_eq_of_lt hb.1 hb.2,
        Int.emod_eq_of_lt (by omega : 0 ≤ (p : ℤ) - 1) (by omega)] at hm
      simpa using hm
    | succ k ih =>
      have h := hd p hp (k + 1)
      simp only [Nat.add_assoc, show 1 + 1 = 2 from Nat.one_add 1] at h
      have hbig : (p : ℤ) ^ (k + 2) ∣ ((p : ℤ) ^ (k + 2)) ^ 2 := by
        exact dvd_pow_self _ (by omega)
      have hsmall : (p : ℤ) ^ (k + 2) ∣ ((p : ℤ) ^ (k + 1)) ^ 2 := by
        rw [← pow_mul]
        exact pow_dvd_pow (p : ℤ) (by omega : k + 2 ≤ (k + 1) * 2)
      have hz : (p : ℤ) ^ (k + 2) ∣ a (p ^ (k + 2)) - a (p ^ (k + 1)) := by
        push_cast at h
        convert (hbig.sub hsmall).sub h using 1; ring
      rw [ih] at hz
      have hb := ha (p ^ (k + 2)) (Nat.one_le_pow _ _ hp.pos)
      have hmodpos : 0 < (p : ℤ) ^ (k + 2) := pow_pos (by omega) _
      have hplt : (p : ℤ) - 1 < (p : ℤ) ^ (k + 2) := by
        have ht : (p : ℤ) ≤ (p : ℤ) ^ (k + 2) := le_self_pow₀ (by omega) (by omega)
        omega
      have hm := (Int.modEq_iff_dvd.mpr hz).symm.eq
      rw [Int.emod_eq_of_lt hb.1 (by exact_mod_cast hb.2),
        Int.emod_eq_of_lt (by omega : 0 ≤ (p : ℤ) - 1) hplt] at hm
      simpa [Nat.add_assoc] using hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  exact hall k

theorem result : claim := by
  intro a ha
  obtain ⟨c, hc⟩ := correction_ghost a ha
  exact bounded_prime_powers a ha.1 (fun p hp k => prime_power_difference a c hc p hp k)

end D5.S3.Arith.Congruence.HannaPrimePowerCorrection
