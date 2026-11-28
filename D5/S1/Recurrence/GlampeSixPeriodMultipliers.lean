/- GID: D5/S1/Recurrence/GlampeSixPeriodMultipliers
   generality: I
   mirror-B: D5/B/S1/Recurrence/GlampeSixPeriodMultipliers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.LinearRecurrence]
   utility: none
   digest: Scaled six-period recurrences admit exactly the multipliers congruent to one mod six. -/

import OmegaBuild.Commands
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.IntervalCases

/-!
The multiplier question of Glampe et al., arXiv:2610.15131v1, equation (10),
for the integer recurrence with seeds `(1, 0)` and coefficients `(t, -t²)`.
-/

compile_only_with_mathlib

namespace D5.S1.Recurrence.GlampeSixPeriodMultipliers

open scoped BigOperators

private def recurrence (t : ℤ) : LinearRecurrence ℤ where
  order := 2
  coeffs := ![-(t ^ 2), t]

/-- The integer recurrence with seeds `1, 0` and coefficients `-t², t` in ascending order. -/
def scaledGibonacci (t : ℤ) : ℕ → ℤ :=
  (recurrence t).mkSol ![1, 0]

private def periodValue (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 | 5 => 1
  | 1 | 4 => 0
  | _ => -1

private theorem periodValue_step (n : ℕ) :
    periodValue (n + 2) = periodValue (n + 1) - periodValue n := by
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by decide)
  unfold periodValue
  rw [Nat.add_mod n 2, Nat.add_mod n 1]
  generalize n % 6 = r at *
  interval_cases r <;> decide

private theorem scaledGibonacci_eq (t : ℤ) (n : ℕ) :
    scaledGibonacci t n = t ^ n * periodValue n := by
  symm
  apply (recurrence t).eq_mk_of_is_sol_of_eq_init (u := fun m => t ^ m * periodValue m) _ _ n
  · intro m
    change t ^ (m + 2) * periodValue (m + 2) =
      ∑ i : Fin 2, (![-(t ^ 2), t] : Fin 2 → ℤ) i * (t ^ (m + i) * periodValue (m + i))
    rw [periodValue_step, pow_add t m 2, Fin.sum_univ_two]
    simp [pow_succ t m]
    ring
  · intro i
    fin_cases i
    · change t ^ 0 * periodValue 0 = 1
      simp [periodValue]
    · change t ^ 1 * periodValue 1 = 0
      simp [periodValue]

private theorem periodValue_mul_of_mod_one {k : ℕ} (hk : k % 6 = 1) (n : ℕ) :
    periodValue (k * n) = periodValue n := by
  unfold periodValue
  rw [Nat.mul_mod, hk, one_mul, Nat.mod_mod]

private theorem scaledGibonacci_monomial (t : ℤ) {k : ℕ} (hk : k % 6 = 1) (n : ℕ) :
    scaledGibonacci t (k * n) = scaledGibonacci t n ^ k := by
  have hpos : 0 < k := by omega
  have hodd : Odd k := Nat.odd_iff.mpr (by omega)
  have hperiod : periodValue n ^ k = periodValue n := by
    have hlt : n % 6 < 6 := Nat.mod_lt _ (by decide)
    unfold periodValue
    generalize n % 6 = r at *
    interval_cases r <;> simp [zero_pow (Nat.ne_of_gt hpos), hodd.neg_one_pow]
  rw [scaledGibonacci_eq, scaledGibonacci_eq, periodValue_mul_of_mod_one hk, mul_pow, hperiod,
    Nat.mul_comm k n, pow_mul]

/-- A fixed coefficient vector and a fixed sign bit per degree yield the identity at every index
exactly for the residue one modulo six. The sufficient witness has sole coefficient `cₖ = 1`
and an all-false mask. -/
theorem multipliers_iff {K : Type*} [Field K] [CharZero K] (t : ℤ) (ht : 2 ≤ t.natAbs)
    (k : ℕ) (hk : 0 < k) :
    (∃ (c : Fin (k + 1) → K) (mask : Fin (k + 1) → Bool), ∀ n : ℕ,
      (scaledGibonacci t (k * n) : K) =
        ∑ i, c i * (if mask i then (-1 : K) ^ n else 1) * (scaledGibonacci t n : K) ^ i.val)
      ↔ k % 6 = 1 := by
  constructor
  · rintro ⟨c, mask, hidentity⟩
    have hpow : Function.Injective (fun n : ℕ => ((t ^ n : ℤ) : K)) :=
      Int.cast_injective.comp (Int.pow_right_injective (by omega))
    have hzero₁ : scaledGibonacci t 1 = 0 := by
      rw [scaledGibonacci_eq]
      simp [periodValue]
    have hzero₇ : scaledGibonacci t 7 = 0 := by
      rw [scaledGibonacci_eq]
      simp [periodValue]
    have hsame : (scaledGibonacci t k : K) = (scaledGibonacci t (k * 7) : K) := by
      have h₁ := hidentity 1
      have h₇ := hidentity 7
      simp only [mul_one, hzero₁, hzero₇, Int.cast_zero, pow_one,
        (show Odd (7 : ℕ) by decide).neg_one_pow] at h₁ h₇
      exact h₁.trans h₇.symm
    have hseven : periodValue (k * 7) = periodValue k := by
      unfold periodValue
      rw [Nat.mul_mod k 7]
      norm_num
    rw [scaledGibonacci_eq, scaledGibonacci_eq, hseven, Int.cast_mul, Int.cast_mul] at hsame
    have hzero : periodValue k = 0 := by
      by_contra h
      have hcast : (periodValue k : K) ≠ 0 := Int.cast_ne_zero.mpr h
      have heq := hpow (mul_right_cancel₀ hcast hsame)
      omega
    have hresidue : k % 6 = 1 ∨ k % 6 = 4 := by
      have hlt : k % 6 < 6 := Nat.mod_lt _ (by decide)
      unfold periodValue at hzero
      generalize k % 6 = r at *
      interval_cases r <;> simp_all
    rcases hresidue with hone | hfour
    · exact hone
    let p : Polynomial K := ∑ i, Polynomial.C (c i) * Polynomial.X ^ i.val
    have hEven (n : ℕ) (hn : Even n) :
        (scaledGibonacci t (k * n) : K) = p.eval (scaledGibonacci t n : K) := by
      simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_C_mul, hn.neg_one_pow] using hidentity n
    have hmultiple (a : ℕ) : scaledGibonacci t (a * 6) = t ^ (a * 6) := by
      rw [scaledGibonacci_eq]
      simp [periodValue, Nat.mul_mod_left]
    have hp : p = Polynomial.X ^ k := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply Set.infinite_of_injective_forall_mem
        (f := fun j : ℕ => ((t ^ (j * 6) : ℤ) : K))
      · intro a b hab
        have heq := hpow hab
        omega
      · intro j
        have hj : Even (j * 6) := ⟨j * 3, by omega⟩
        have hvalue := (hEven (j * 6) hj).symm
        rw [hmultiple, ← Nat.mul_assoc, hmultiple] at hvalue
        change p.eval ((t ^ (j * 6) : ℤ) : K) = (Polynomial.X ^ k).eval _
        rw [Polynomial.eval_X_pow, ← Int.cast_pow, ← pow_mul]
        rwa [Nat.mul_comm (j * 6) k, ← Nat.mul_assoc]
    have htwo : periodValue (k * 2) = -1 := by
      unfold periodValue
      rw [Nat.mul_mod, hfour]
      decide
    have hkeven : Even k := Nat.even_iff.mpr (by omega)
    have hvalue := hEven 2 (by decide)
    rw [hp, Polynomial.eval_X_pow, scaledGibonacci_eq t (k * 2),
      scaledGibonacci_eq t 2, htwo] at hvalue
    simp only [periodValue, Int.cast_neg, Int.cast_pow,
      mul_neg, mul_one, neg_pow, hkeven.neg_one_pow, one_mul] at hvalue
    rw [← pow_mul, Nat.mul_comm 2 k] at hvalue
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht
    have hnonzero : ((t : K) ^ (k * 2)) ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.mpr ht0)
    exact False.elim (hnonzero (neg_eq_self.mp hvalue))
  · intro hresidue
    refine ⟨fun i => if i = Fin.last k then 1 else 0, fun _ => false, ?_⟩
    intro n
    rw [scaledGibonacci_monomial t hresidue, Int.cast_pow, Finset.sum_eq_single (Fin.last k)]
    · simp
    · intro i _ hi
      simp [hi]
    · simp

end D5.S1.Recurrence.GlampeSixPeriodMultipliers
