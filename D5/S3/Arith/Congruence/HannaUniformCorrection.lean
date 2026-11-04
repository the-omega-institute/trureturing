/- GID: D5/S3/Arith/Congruence/HannaUniformCorrection
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/HannaUniformCorrection
   mirror-E: none(waiver:symbolic-unbounded-family)
   anchors: []
   utility: none
   digest: Bounded corrections and positive Euler exponents for every integer power weight. -/

/- admission_basis: escape-witness. Proposed content: exponent_bounds proves a simultaneous positive lower and power upper bound through strong induction and the proper-divisor budget. The prime-power conclusions consume the generalized original owner induction, never a duplicate square proof. Every weight is an integer and weight_cast supplies the nonnegative-domain correspondence. utility none: unbounded symbolic family. Source attribution: the square results are due to Su; Bala owns the cited universal shift (not extended here); all-s literature novelty is unverified. -/


import D5.S1.Recurrence.Witt.BoundedEulerCorrection
import D5.S3.Arith.Divisors.ProperDivisorPowerBudget
import D5.S3.Arith.Congruence.HannaPrimePowerCorrection

noncomputable section

namespace D5.S3.Arith.Congruence.HannaUniformCorrection

open Finset PowerSeries
open D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open D5.S1.Recurrence.Witt.BoundedEulerCorrection
open D5.S3.Arith.Divisors.ProperDivisorPowerBudget

/-- Natural powers are used for the integer recursion; `weight_cast` below
identifies them with the requested integer powers on the full nonnegative domain. -/
def weight (s : ℤ) (n : ℕ) : ℤ := (n : ℤ) ^ s.toNat

def a (s : ℤ) : ℕ → ℤ := correction (weight s)
def c (s : ℤ) : ℕ → ℤ := ledger (weight s)

/-- The actual rational formal exponential, with an integer weight parameter. -/
def F (s : ℤ) : PowerSeries ℚ :=
  exponentialSum (fun n => (n : ℚ) ^ s - (a s n : ℚ))

def IsPowerCorrection (s : ℤ) (b : ℕ → ℤ) : Prop :=
  (∀ n, 0 < n → 0 ≤ b n ∧ b n < (n : ℤ)) ∧
    D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.IntegralSeries
      (exponentialSum (fun n => (n : ℚ) ^ s - (b n : ℚ)))

theorem weight_cast (s : ℤ) (hs : 0 ≤ s) (n : ℕ) :
    (weight s n : ℚ) = (n : ℚ) ^ s := by
  rw [← Int.toNat_of_nonneg hs]
  simp [weight]

theorem correction_spec (s : ℤ) : IsCorrection (weight s) (a s) :=
  correction_integral (weight s)

private theorem power_correction_iff (s : ℤ) (hs : 0 ≤ s) (b : ℕ → ℤ) :
    IsPowerCorrection s b ↔ IsCorrection (weight s) b := by
  have he : (fun n => (n : ℚ) ^ s - (b n : ℚ)) =
      (fun n => ((weight s n - b n : ℤ) : ℚ)) := by
    funext n
    rw [Int.cast_sub, weight_cast s hs n]
  simp only [IsPowerCorrection, IsCorrection, he]

/-- Existence and uniqueness on exactly the positive indices. -/
theorem correction_exists_unique (s : ℤ) (hs : 0 ≤ s) :
    IsPowerCorrection s (a s) ∧
      ∀ b, IsPowerCorrection s b → ∀ n, 0 < n → b n = a s n := by
  refine ⟨(power_correction_iff s hs _).mpr (correction_spec s), ?_⟩
  intro b hb n hn
  exact correction_unique (weight s) b ((power_correction_iff s hs b).mp hb) n hn

/-- Actual exponent-to-exponential equality, with the primitive ledger's
zero-based indexing shifted explicitly to positive part sizes. -/
theorem euler_representation (s : ℤ) (hs : 0 ≤ s) :
    (eulerSeries (fun i => c s (i + 1))).map (Int.castRingHom ℚ) = F s := by
  apply euler_series_exponential
  intro n hn
  have hc : divisorGhost (fun d => c s (d - 1 + 1)) n = divisorGhost (c s) n := by
    unfold divisorGhost
    apply sum_congr rfl
    intro d hd
    rw [Nat.sub_add_cancel (Nat.pos_of_mem_divisors hd)]
  rw [hc, ← weight_cast s hs n]
  exact_mod_cast correction_equation (weight s) n hn

/-- Each positive-index exponent is between one and the stipulated power bound.
The lower bound uses the finite complementary-divisor estimate. -/
theorem exponent_bounds (s : ℤ) (hs : 2 ≤ s) :
    ∀ n, 0 < n → 1 ≤ c s n ∧ c s n ≤ (n : ℤ) ^ (s.toNat - 1) := by
  have hsN : 2 ≤ s.toNat := by omega
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hab := (correction_spec s).1 n hn
    have he := correction_equation (weight s) n hn
    change weight s n - a s n = divisorGhost (c s) n at he
    have hsplit : divisorGhost (c s) n = properGhost (c s) n + (n : ℤ) * c s n := by
      rw [divisorGhost, ← Nat.cons_self_properDivisors hn.ne', sum_cons]
      simp only [properGhost]
      ring
    rw [hsplit] at he
    have hT0 : 0 ≤ properGhost (c s) n := by
      apply sum_nonneg
      intro d hd
      exact mul_nonneg (Nat.cast_nonneg d)
        (le_trans (by norm_num) (ih d (Nat.mem_properDivisors.mp hd).2
          (Nat.pos_of_mem_properDivisors hd)).1)
    have hTle : properGhost (c s) n ≤ ∑ d ∈ n.properDivisors, (d : ℤ) ^ s.toNat := by
      apply sum_le_sum
      intro d hd
      have hb := (ih d (Nat.mem_properDivisors.mp hd).2
        (Nat.pos_of_mem_properDivisors hd)).2
      calc
        (d : ℤ) * c s d ≤ (d : ℤ) * (d : ℤ) ^ (s.toNat - 1) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d)
        _ = (d : ℤ) ^ s.toNat := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ s.toNat)]
    have hbudget := power_budget s.toNat n hsN hn
    have hpow : (n : ℤ) ^ s.toNat = (n : ℤ) * (n : ℤ) ^ (s.toNat - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ s.toNat)]
    dsimp only [weight] at he
    constructor <;> nlinarith

/-- Every prime, including two, has the same correction at each positive power. -/
theorem correction_prime_power (s : ℤ) (hs : 2 ≤ s) (p r : ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) : a s (p ^ r) = (p : ℤ) - 1 := by
  apply D5.S3.Arith.Congruence.HannaPrimePowerCorrection.bounded_power_corrections
    s.toNat (by omega) (a s) (correction_spec s).1 _ p r hp hr
  intro q hq k
  have h := divisor_ghost_gauss (c s) q hq k 1 Nat.one_pos
  simp only [one_mul] at h
  rw [← correction_equation (weight s) _ (pow_pos hq.pos _),
    ← correction_equation (weight s) _ (pow_pos hq.pos _)] at h
  exact h

private theorem ghost_prime_power_step (b : ℕ → ℤ) (p k : ℕ) (hp : p.Prime) :
    divisorGhost b (p ^ (k + 1)) - divisorGhost b (p ^ k) =
      (p : ℤ) ^ (k + 1) * b (p ^ (k + 1)) := by
  simp only [divisorGhost, Nat.sum_divisors_prime_pow hp]
  rw [sum_range_succ]
  push_cast
  ring

private theorem exponent_one (s : ℤ) : c s 1 = 1 := by
  have h := correction_equation (weight s) 1 Nat.one_pos
  have hb := (correction_spec s).1 1 Nat.one_pos
  norm_num [weight, divisorGhost] at h hb
  change 1 - a s 1 = c s 1 at h
  omega

theorem exponent_prime (s : ℤ) (hs : 2 ≤ s) (p : ℕ) (hp : p.Prime) :
    c s p = (p : ℤ) ^ (s.toNat - 1) - 1 := by
  have h := ghost_prime_power_step (c s) p 0 hp
  simp only [zero_add, pow_one, pow_zero] at h
  rw [← correction_equation (weight s) p hp.pos,
    ← correction_equation (weight s) 1 Nat.one_pos,
    correction_prime_power s hs p 1 hp le_rfl] at h
  have ha1 : a s 1 = 0 := by
    have := (correction_spec s).1 1 Nat.one_pos
    omega
  simp only [weight, ha1, one_pow, sub_zero] at h
  have he : (p : ℤ) ^ s.toNat = (p : ℤ) * (p : ℤ) ^ (s.toNat - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ s.toNat)]
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rw [he] at h
  nlinarith

theorem exponent_prime_power (s : ℤ) (hs : 2 ≤ s) (p r : ℕ)
    (hp : p.Prime) (hr : 2 ≤ r) :
    c s (p ^ r) = (p : ℤ) ^ (s.toNat * (r - 1) - r) * ((p : ℤ) ^ s.toNat - 1) := by
  have hr1 : 1 ≤ r := by omega
  have hrm : 1 ≤ r - 1 := by omega
  have hsN : 2 ≤ s.toNat := by omega
  have hexp : r ≤ s.toNat * (r - 1) := by nlinarith
  have h := ghost_prime_power_step (c s) p (r - 1) hp
  rw [Nat.sub_add_cancel hr1] at h
  rw [← correction_equation (weight s) _ (pow_pos hp.pos _),
    ← correction_equation (weight s) _ (pow_pos hp.pos _),
    correction_prime_power s hs p r hp hr1,
    correction_prime_power s hs p (r - 1) hp hrm] at h
  simp only [weight, Nat.cast_pow, ← pow_mul] at h
  have hpow : (p : ℤ) ^ r *
      ((p : ℤ) ^ (s.toNat * (r - 1) - r) * ((p : ℤ) ^ s.toNat - 1)) =
      (p : ℤ) ^ (r * s.toNat) - (p : ℤ) ^ ((r - 1) * s.toNat) := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_add]
    rw [show r + (s.toNat * (r - 1) - r) = (r - 1) * s.toNat by omega]
    rw [← pow_add]
    congr 2
    omega
  have hp0 : (p : ℤ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  apply mul_left_cancel₀ hp0
  rw [hpow]
  linear_combination -h

end D5.S3.Arith.Congruence.HannaUniformCorrection
