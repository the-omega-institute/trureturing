/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTrianglePowerTail
   generality: I
   mirror-B: none(waiver:prime-triangle-correction-input)
   mirror-E: none(waiver:prime-triangle-correction)
   anchors: []
   utility: none
   digest: The ordinary prime triangle differs from the Mangoldt triangle by the exact square contribution and an explicit higher-power tail. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle
import Mathlib.NumberTheory.Chebyshev

/-! The prime-square correction to the Mangoldt triangle and an explicit bound
for the higher prime powers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerTail

open Finset PrimeQuarterTriangle

open private triangleWeight_bounds triangleWeight_eq_zero_of_le primeTriangleSum_eq_prefix from
  D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle

/-- The contribution of one exponent, with every power up to `4*x` included. -/
private def primePowerTriangleSum (x : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Ioc 0 ⌊(4 * x) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime,
    Real.log (p : ℝ) * triangleWeight x ((p : ℝ) ^ k)

/-- The exact square contribution, with logarithm of the prime base and
endpoints `x < p² ≤ 4*x`. -/
def squareTriangleSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊4 * x⌋₊).filter
      (fun p : ℕ => x < (p : ℝ) ^ (2 : ℕ) ∧ (p : ℝ) ^ (2 : ℕ) ≤ 4 * x),
    Real.log (p : ℝ) * triangleWeight x ((p : ℝ) ^ (2 : ℕ))

/-- The weighted contribution of exponents at least three. -/
def primeTrianglePowerTail (x : ℝ) : ℝ :=
  ∑ k ∈ Ioc 2 ⌊Real.log (4 * x) / Real.log 2⌋₊, primePowerTriangleSum x k

private theorem primePowerTriangleSum_one {x : ℝ} (hx : 0 ≤ x) :
    primePowerTriangleSum x 1 = primeTriangleSum x := by
  rw [primeTriangleSum_eq_prefix hx]
  simp only [primePowerTriangleSum, Nat.cast_one, div_one, Real.rpow_one, pow_one]

private theorem primePowerTriangleSum_two {x : ℝ} (hx : 0 ≤ 4 * x) :
    primePowerTriangleSum x 2 = squareTriangleSum x := by
  let primes := (Ioc 0 ⌊(4 * x) ^ ((1 : ℝ) / 2)⌋₊).filter Nat.Prime
  have hprimes : (Nat.primesLE ⌊4 * x⌋₊).filter
        (fun p : ℕ => x < (p : ℝ) ^ (2 : ℕ) ∧ (p : ℝ) ^ (2 : ℕ) ≤ 4 * x) =
      primes.filter (fun p : ℕ => x < (p : ℝ) ^ (2 : ℕ)) := by
    ext p
    simp only [primes, mem_filter, Nat.mem_primesLE, mem_Ioc]
    have hroot : (p : ℝ) ≤ (4 * x) ^ ((1 : ℝ) / 2) ↔ (p : ℝ) ^ (2 : ℕ) ≤ 4 * x := by
      rw [one_div]
      simpa only [Real.rpow_two] using
        (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) hx (by norm_num : (0 : ℝ) < 2))
    rw [Nat.le_floor_iff hx, Nat.le_floor_iff (Real.rpow_nonneg hx ((1 : ℝ) / 2)), hroot]
    constructor
    · rintro ⟨⟨_, hp⟩, hlo, hhi⟩
      exact ⟨⟨⟨hp.pos, hhi⟩, hp⟩, hlo⟩
    · rintro ⟨⟨⟨_, hhi⟩, hp⟩, hlo⟩
      have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      have hp_le_sq : (p : ℝ) ≤ (p : ℝ) ^ (2 : ℕ) := le_self_pow₀ hp₁ (by decide)
      exact ⟨⟨hp_le_sq.trans hhi, hp⟩, hlo, hhi⟩
  unfold squareTriangleSum
  rw [hprimes]
  change (∑ p ∈ primes, Real.log (p : ℝ) * triangleWeight x ((p : ℝ) ^ (2 : ℕ))) = _
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro p hp hpnot
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hle : (p : ℝ) ^ (2 : ℕ) ≤ x := le_of_not_gt fun hlt =>
    hpnot (Finset.mem_filter.mpr ⟨hp, hlt⟩)
  rw [triangleWeight_eq_zero_of_le (pow_pos hp₀ _) hle, mul_zero]

private theorem mangoldtHingeSum_eq_sum_powers {x : ℝ} (hx : 0 ≤ 4 * x) :
    mangoldtHingeSum x =
      ∑ k ∈ Icc 1 ⌊Real.log (4 * x) / Real.log 2⌋₊, primePowerTriangleSum x k := by
  let weight (n : ℕ) := ArithmeticFunction.vonMangoldt n * triangleWeight x (n : ℝ)
  change (∑ n ∈ Ioc 0 ⌊4 * x⌋₊, weight n) = _
  calc
    _ = ∑ n ∈ (Ioc 0 ⌊4 * x⌋₊).filter IsPrimePow, weight n := by
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hn : IsPrimePow n
      · rw [if_pos hn]
      · rw [if_neg hn, show weight n = 0 by
          simp only [weight, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_mul]]
    _ = ∑ k ∈ Icc 1 ⌊Real.log (4 * x) / Real.log 2⌋₊,
          ∑ p ∈ (Ioc 0 ⌊(4 * x) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime,
            weight (p ^ k) := Chebyshev.sum_PrimePow_eq_sum_sum weight hx
    _ = _ := by
      unfold primePowerTriangleSum
      refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun p hp => ?_
      have hk₀ : k ≠ 0 := ne_of_gt (show 0 < k from (Finset.mem_Icc.mp hk).1)
      simp only [weight, ArithmeticFunction.vonMangoldt_apply_pow hk₀,
        ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2, Nat.cast_pow]

private theorem two_le_powerCutoff {y : ℝ} (hy : 4 ≤ y) :
    2 ≤ ⌊Real.log y / Real.log 2⌋₊ := by
  apply Nat.le_floor
  rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  calc
    ((2 : ℕ) : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by rw [Real.log_pow]
    _ ≤ Real.log y := Real.log_le_log (by positivity)
      (by simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using hy)

/-- Subtracting the ordinary prime triangle leaves exactly the prime-square
triangle and the higher-power tail, for every real `x ≥ 1`. -/
theorem mangoldtHingeSum_sub_primeTriangleSum {x : ℝ} (hx : 1 ≤ x) :
    mangoldtHingeSum x - primeTriangleSum x = squareTriangleSum x + primeTrianglePowerTail x := by
  have hx₀ : 0 ≤ x := by linarith
  have h4x : 0 ≤ 4 * x := by positivity
  let K : ℕ := ⌊Real.log (4 * x) / Real.log 2⌋₊
  have hK₂ : 2 ≤ K := two_le_powerCutoff (y := 4 * x) (by linarith)
  have hK₁ : 1 ≤ K := by omega
  have hexponents : Ioc (1 : ℕ) K = Icc 2 K := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [mangoldtHingeSum_eq_sum_powers h4x]
  change (∑ k ∈ Icc 1 K, primePowerTriangleSum x k) - primeTriangleSum x =
    squareTriangleSum x + ∑ k ∈ Ioc 2 K, primePowerTriangleSum x k
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := primePowerTriangleSum x) hK₁, hexponents,
    ← Finset.add_sum_Ioc_eq_sum_Icc (f := primePowerTriangleSum x) hK₂,
    primePowerTriangleSum_one hx₀, primePowerTriangleSum_two h4x]
  ring

private theorem primePowerTriangleSum_bounds {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ primePowerTriangleSum x k ∧
      primePowerTriangleSum x k ≤ Chebyshev.theta ((4 * x) ^ ((1 : ℝ) / (k : ℝ))) := by
  have hweight (p : ℕ) (hp : p.Prime) :
      triangleWeight x ((p : ℝ) ^ k) ∈ Set.Icc (0 : ℝ) 1 := by
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact triangleWeight_bounds hx (pow_pos hp₀ k)
  have hlog (p : ℕ) (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  constructor
  · unfold primePowerTriangleSum
    refine Finset.sum_nonneg fun p hp => ?_
    have hprime := (Finset.mem_filter.mp hp).2
    exact mul_nonneg (hlog p hprime) (hweight p hprime).1
  · rw [primePowerTriangleSum, Chebyshev.theta]
    refine Finset.sum_le_sum fun p hp => ?_
    have hprime := (Finset.mem_filter.mp hp).2
    exact mul_le_of_le_one_right (hlog p hprime) (hweight p hprime).2

/-- The higher-power tail is nonnegative and bounded by the unweighted
Chebyshev contribution of those powers. The explicit estimate uses one cube
root term and `K - 3` fourth-root terms, with subtraction in `ℕ`. -/
theorem primeTrianglePowerTail_bounds {x : ℝ} (hx : 1 ≤ x) :
    let K := ⌊Real.log (4 * x) / Real.log 2⌋₊
    let T := ∑ k ∈ Ioc 2 K, Chebyshev.theta ((4 * x) ^ ((1 : ℝ) / (k : ℝ)))
    0 ≤ primeTrianglePowerTail x ∧ primeTrianglePowerTail x ≤ T ∧
      T ≤ Real.log 4 * ((4 * x) ^ ((1 : ℝ) / 3) +
        ((K - 3 : ℕ) : ℝ) * (4 * x) ^ ((1 : ℝ) / 4)) := by
  have hx₀ : 0 ≤ x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold primeTrianglePowerTail
    exact Finset.sum_nonneg fun k _ => (primePowerTriangleSum_bounds hx₀ k).1
  · unfold primeTrianglePowerTail
    exact Finset.sum_le_sum fun k _ => (primePowerTriangleSum_bounds hx₀ k).2
  · let K : ℕ := ⌊Real.log (4 * x) / Real.log 2⌋₊
    let thetaTerm (k : ℕ) := Chebyshev.theta ((4 * x) ^ ((1 : ℝ) / (k : ℝ)))
    change (∑ k ∈ Ioc 2 K, thetaTerm k) ≤ Real.log 4 *
      ((4 * x) ^ ((1 : ℝ) / 3) + ((K - 3 : ℕ) : ℝ) * (4 * x) ^ ((1 : ℝ) / 4))
    have hbase : 1 ≤ 4 * x := by linarith
    have h4x : 0 ≤ 4 * x := by positivity
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hcube : thetaTerm 3 ≤ Real.log 4 * (4 * x) ^ ((1 : ℝ) / 3) := by
      simpa only [thetaTerm, Nat.cast_ofNat] using
        (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg h4x ((1 : ℝ) / 3)))
    have hquartic : (∑ k ∈ Ioc 3 K, thetaTerm k) ≤
        ((K - 3 : ℕ) : ℝ) * (Real.log 4 * (4 * x) ^ ((1 : ℝ) / 4)) := by
      calc
        _ ≤ ∑ _k ∈ Ioc 3 K, Real.log 4 * (4 * x) ^ ((1 : ℝ) / 4) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk₄ : (4 : ℝ) ≤ k := by
            exact_mod_cast (show 4 ≤ k from (Finset.mem_Ioc.mp hk).1)
          exact (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg h4x ((1 : ℝ) / (k : ℝ)))).trans
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase
              (one_div_le_one_div_of_le (by norm_num) hk₄)) hlog)
        _ = _ := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    -- The enlarged exponent set also covers the empty tail when `K < 3`.
    have hsubset : Ioc (2 : ℕ) K ⊆ insert 3 (Ioc 3 K) := by
      intro k hk
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hk
      by_cases he : k = 3
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_Ioc.mpr ⟨by omega, hhi⟩))
    calc
      _ ≤ ∑ k ∈ insert 3 (Ioc 3 K), thetaTerm k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun k _ _ => Chebyshev.theta_nonneg _
      _ = thetaTerm 3 + ∑ k ∈ Ioc 3 K, thetaTerm k :=
        Finset.sum_insert (by simp [Finset.mem_Ioc])
      _ ≤ Real.log 4 * (4 * x) ^ ((1 : ℝ) / 3) +
          ((K - 3 : ℕ) : ℝ) * (Real.log 4 * (4 * x) ^ ((1 : ℝ) / 4)) :=
        add_le_add hcube hquartic
      _ = _ := by ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerTail
