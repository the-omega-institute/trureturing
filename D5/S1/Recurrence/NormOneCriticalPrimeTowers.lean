/- GID: D5/S1/Recurrence/NormOneCriticalPrimeTowers
   generality: I
   mirror-B: none(waiver:external-uniqueness-refutation)
   mirror-E: none(waiver:unbounded-prime-power-exponents)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/NormOneCriticalPrimeTowers.criticalPrimeUniqueness; result=D5/S1/Recurrence/NormOneCriticalPrimeTowers.refutes_critical_prime_uniqueness; claim=D5/S1/Recurrence/NormOneCriticalPrimeTowers.criticalPrimeUniqueness
   digest: The original companion at golden trace L_8=47 has both complete fixed-point towers 3^e and 5^e. The lifting engine evaluates a commutative polynomial identity at an integer matrix. -/

import D5.S1.Recurrence.NormOneCriticalPrimes
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.NormOneCriticalPrimeTowers

open Matrix Polynomial LucasEvenDescent LucasCompanion NormOneCriticalPrimes
open scoped Matrix

abbrev IntMatrix := Matrix (Fin 2) (Fin 2) ℤ

/-- The very same companion, before reduction. -/
def integralCompanion (a : ℤ) : IntMatrix := !![a, -1; 1, 0]

/-- Entrywise reduction is a ring homomorphism; multiplication is not changed. -/
def reduceMatrix (m : ℕ) : IntMatrix →+* Matrix (Fin 2) (Fin 2) (ZMod m) :=
  (Int.castRingHom (ZMod m)).mapMatrix

lemma reduction_is_companion (a : ℤ) (m : ℕ) :
    reduceMatrix m (integralCompanion a) =
      (↑(companion (a : ZMod m) (1 : (ZMod m)ˣ)) : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reduceMatrix, integralCompanion, companion]

lemma period_eq_reduced_order (a : ℤ) (m : ℕ) :
    period a m = orderOf (reduceMatrix m (integralCompanion a)) := by
  rw [reduction_is_companion]
  unfold period matrixPeriod
  exact orderOf_units.symm

private lemma cast_mul_matrix (n : ℕ) (A : IntMatrix) : (n : IntMatrix) * A = n • A := by
  rw [nsmul_eq_mul]

/-- A polynomial identity is evaluated at B. Matrices are not incorrectly given a
CommSemiring instance to use the commutative binomial theorem. -/
theorem matrix_prime_power_expansion (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (B : IntMatrix) (j : ℕ) :
    ∃ C : IntMatrix,
      (1 + p • B) ^ (p ^ j) = 1 + (p ^ (j + 1)) • (B + p • C) := by
  have hv : (p : Polynomial ℤ) ∣ (p : Polynomial ℤ) := dvd_refl _
  have ht : (p : Polynomial ℤ) * p * p ∣ (p : Polynomial ℤ) ^ p := by
    rw [show (p : Polynomial ℤ) * p * p = (p : Polynomial ℤ) ^ 3 by ring]
    exact pow_dvd_pow _ hp3
  obtain ⟨D, hD⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq
    (R := Polynomial ℤ) (u := (p : Polynomial ℤ)) (v := (p : Polynomial ℤ)) hp hv ht X j
  refine ⟨Polynomial.aeval B D, ?_⟩
  have he := congrArg (fun f : Polynomial ℤ => Polynomial.aeval B f) hD
  simp only [map_add, map_mul, map_pow, map_one, map_natCast, Polynomial.aeval_X] at he
  rw [← pow_succ] at he
  simpa only [← Nat.cast_pow, cast_mul_matrix] using he

/-- Exact multiplication-depth expansion from a verified first return seed. -/
theorem seeded_matrix_power (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (A B : IntMatrix) (hseed : A ^ p = 1 + p • B) (j : ℕ) :
    ∃ C : IntMatrix, A ^ (p ^ (j + 1)) = 1 + (p ^ (j + 1)) • (B + p • C) := by
  obtain ⟨C, hC⟩ := matrix_prime_power_expansion p hp hp3 B j
  refine ⟨C, ?_⟩
  rw [← hseed, ← pow_mul] at hC
  simpa only [pow_succ'] using hC

lemma reduced_shift_eq_one_iff (m k : ℕ) (B : IntMatrix) :
    reduceMatrix m (1 + k • B) = 1 ↔
      ∀ i j : Fin 2, (m : ℤ) ∣ (k : ℤ) * B i j := by
  rw [map_add, map_one, add_eq_left]
  constructor
  · intro h i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    have hij := congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod m) => A i j) h
    simpa only [reduceMatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
      Int.coe_castRingHom, Matrix.smul_apply, Int.nsmul_eq_mul, Matrix.zero_apply] using hij
  · intro h
    ext i j
    have hij := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr (h i j)
    simpa only [reduceMatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
      Int.coe_castRingHom, Matrix.smul_apply, Int.nsmul_eq_mul, Matrix.zero_apply] using hij

private lemma primitive_corrected (p : ℕ) (b c : ℤ) (hb : ¬ (p : ℤ) ∣ b) :
    ¬ (p : ℤ) ∣ b + (p : ℤ) * c := by
  intro h
  apply hb
  simpa using dvd_sub h (show (p : ℤ) ∣ (p : ℤ) * c from ⟨c, rfl⟩)

private lemma not_next_power (p k : ℕ) (hp : 0 < p) (b : ℤ)
    (hb : ¬ (p : ℤ) ∣ b) :
    ¬ (p : ℤ) ^ (k + 1) ∣ (p : ℤ) ^ k * b := by
  rintro ⟨d, hd⟩
  apply hb
  refine ⟨d, ?_⟩
  have hpz : (p : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (ne_of_gt hp))
  apply mul_left_cancel₀ hpz
  simpa only [pow_succ, mul_assoc] using hd

/-- One primitive entry of the first defect gives the exact entire period tower.
The return seed and its primitive entry are checked explicitly for the witnesses below. -/
theorem order_tower_of_seed (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (A B : IntMatrix) (hseed : A ^ p = 1 + p • B)
    (hbase : orderOf (reduceMatrix p A) = p)
    (i j : Fin 2) (hprimitive : ¬ (p : ℤ) ∣ B i j)
    (e : ℕ) (he : 0 < e) : orderOf (reduceMatrix (p ^ e) A) = p ^ e := by
  letI : Fact p.Prime := ⟨hp⟩
  cases e with
  | zero => omega
  | succ e =>
      cases e with
      | zero =>
          change orderOf (reduceMatrix (p ^ 1) A) = p ^ 1
          rw [pow_one]
          exact hbase
      | succ k =>
          apply orderOf_eq_prime_pow
          · intro h
            obtain ⟨C, hC⟩ := seeded_matrix_power p hp hp3 A B hseed k
            have hz : reduceMatrix (p ^ (k + 1 + 1))
                (1 + (p ^ (k + 1)) • (B + p • C)) = 1 := by
              rw [← hC, map_pow]
              exact h
            have hd := (reduced_shift_eq_one_iff _ _ _).mp hz i j
            have hc : ¬ (p : ℤ) ∣ B i j + (p : ℤ) * C i j :=
              primitive_corrected p (B i j) (C i j) hprimitive
            apply not_next_power p (k + 1) hp.pos (B i j + (p : ℤ) * C i j) hc
            simpa only [Nat.cast_pow, Matrix.add_apply, Matrix.smul_apply,
              Int.nsmul_eq_mul] using hd
          · obtain ⟨C, hC⟩ := seeded_matrix_power p hp hp3 A B hseed (k + 1)
            rw [← map_pow, hC]
            apply (reduced_shift_eq_one_iff _ _ _).mpr
            intro i' j'
            exact ⟨(B + p • C) i' j', rfl⟩

private def seedThree : IntMatrix := !![34576, -736; 736, -16]
private def seedFive : IntMatrix := !![45785971, -974611; 974611, -20746]

private lemma seed_three_identity : integralCompanion 47 ^ 3 = 1 + 3 • seedThree := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integralCompanion, seedThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma seed_five_identity : integralCompanion 47 ^ 5 = 1 + 5 • seedFive := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integralCompanion, seedFive, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- First complete fixed-point tower for the single parameter 47. -/
theorem golden_trace_three_tower (e : ℕ) (he : 0 < e) : period 47 (3 ^ e) = 3 ^ e := by
  rw [period_eq_reduced_order]
  refine order_tower_of_seed 3 Nat.prime_three (by decide)
    (integralCompanion 47) seedThree seed_three_identity ?_ 0 0 ?_ e he
  · rw [← period_eq_reduced_order]
    exact (prime_fixed_iff_parameter_two 47 3 Nat.prime_three).mpr (by decide)
  · norm_num [seedThree]

/-- Second complete fixed-point tower for that same parameter. -/
theorem golden_trace_five_tower (e : ℕ) (he : 0 < e) : period 47 (5 ^ e) = 5 ^ e := by
  rw [period_eq_reduced_order]
  refine order_tower_of_seed 5 Nat.prime_five (by decide)
    (integralCompanion 47) seedFive seed_five_identity ?_ 0 0 ?_ e he
  · rw [← period_eq_reduced_order]
    exact (prime_fixed_iff_parameter_two 47 5 Nat.prime_five).mpr (by decide)
  · norm_num [seedFive]

/-- A prime with a complete fixed-point power tower, the strongest natural reading
of the unnumbered critical-prime claim following Conjecture 6.5. -/
def FullCriticalTower (a : ℤ) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ e : ℕ, 0 < e → period a (p ^ e) = p ^ e

def criticalPrimeUniqueness : Prop :=
  ∀ a : ℤ, 2 < a → ∀ p q : ℕ, FullCriticalTower a p → FullCriticalTower a q → p = q

/-- The published uniqueness observation fails even when every positive exponent is required. -/
theorem refutes_critical_prime_uniqueness : ¬ criticalPrimeUniqueness := by
  intro h
  have he := h 47 (by decide) 3 5
    ⟨Nat.prime_three, golden_trace_three_tower⟩
    ⟨Nat.prime_five, golden_trace_five_tower⟩
  norm_num at he

#print axioms reduction_is_companion
#print axioms period_eq_reduced_order
#print axioms cast_mul_matrix
#print axioms matrix_prime_power_expansion
#print axioms seeded_matrix_power
#print axioms reduced_shift_eq_one_iff
#print axioms primitive_corrected
#print axioms not_next_power
#print axioms order_tower_of_seed
#print axioms seed_three_identity
#print axioms seed_five_identity
#print axioms golden_trace_three_tower
#print axioms golden_trace_five_tower
#print axioms refutes_critical_prime_uniqueness

end D5.S1.Recurrence.NormOneCriticalPrimeTowers
