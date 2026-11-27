/- GID: D5/S3/Arith/Robin/AllSupportRobinPrimeBlock
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/AllSupportRobinPrimeBlock
   mirror-E: none(waiver:analytic-prime-cost-estimate)
   anchors: []
   utility: none
   digest: A weighted Chebyshev theta integral lower bounds the actual Robin prime cost. -/

/-
The prime-square comparison adapts Robin1984 contributors'
Analytic/PrimeCostLowerBound.lean (robin_prime_square_reference_sign and
robin_minimum_prime_cost_ge_block) at commit
5ce18bf3487c68d9353276ef5811057f60d17808 (Apache-2.0).
The lower-end cancellation is the one in Analytic/PrimeSquareAbelBound.lean
(robin_complete_prime_square_block_eq) at the same pin.
https://github.com/kimihiro64/Robin1984/tree/5ce18bf3487c68d9353276ef5811057f60d17808/Robin1984/Analytic

This draft uses the exact native finite Abel formula and the primeCost
definition from the companion AllSupportRobinCost.lean draft.
-/
import D5.S3.Arith.Robin.AllSupportRobinCost
import D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel

/-! Lower bound for the Robin prime cost by a finite weighted Chebyshev integral. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.AllSupportRobinCost

open MeasureTheory
open scoped BigOperators
open D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel (finite_theta_abel)
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace (weight)

private theorem square_mul_log_le {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    x ^ 2 * Real.log x ≤ y ^ 2 * Real.log y := by
  have hx0 : 0 < x := by linarith
  exact mul_le_mul (pow_le_pow_left₀ hx0.le hxy 2) (Real.log_le_log hx0 hxy)
    (Real.log_pos hx).le (sq_nonneg y)

/-- The theta prefix pays for the lower endpoint of the reciprocal-square sum. -/
private theorem prime_cost_ge_square_block {h s : ℝ} (hh : 1 < h) (hs : 1 < s)
    (hsb : s ≤ h / 2) (hden : h * Real.log h ≤ s ^ 2 * Real.log s) :
    Chebyshev.theta s / (s ^ 2 * Real.log s) +
        (∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊h / 2⌋₊).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤
      primeCost h := by
  classical
  have hs0 : 0 ≤ s := by linarith
  have hhPos : 0 < h := by linarith
  have hsDen : 0 < s ^ 2 * Real.log s :=
    mul_pos (pow_pos (by linarith : 0 < s) 2) (Real.log_pos hs)
  have hprice (p : ℕ) (hp : 1 < (p : ℝ)) :
      Real.log (p : ℝ) / (s ^ 2 * Real.log s) ≤ primePrice h p := by
    unfold primePrice
    exact div_le_div_of_nonneg_left (Real.log_pos hp).le
      (mul_pos hhPos (Real.log_pos hh)) hden
  have hsmall : Chebyshev.theta s / (s ^ 2 * Real.log s) ≤
      ∑ p ∈ Nat.primesLE ⌊s⌋₊, min (primePrice h p) ((p : ℝ)⁻¹ ^ 2) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    have hp2 : 0 < (p : ℝ) ^ 2 := pow_pos (by linarith : 0 < (p : ℝ)) 2
    have hps : (p : ℝ) ≤ s := (Nat.le_floor_iff hs0).mp (Nat.le_of_mem_primesLE hp)
    have hcompare : Real.log (p : ℝ) / (s ^ 2 * Real.log s) ≤ 1 / (p : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ hsDen hp2).mpr
      rw [one_mul, mul_comm (Real.log (p : ℝ))]
      exact square_mul_log_le hp1 hps
    exact le_min (hprice p hp1) (by simpa only [one_div, inv_pow] using hcompare)
  have hlarge :
      (∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊h / 2⌋₊).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤
        ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊h / 2⌋₊).filter Nat.Prime,
          min (primePrice h p) ((p : ℝ)⁻¹ ^ 2) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast hprime.one_lt
    have hp2 : 0 < (p : ℝ) ^ 2 := pow_pos (by linarith : 0 < (p : ℝ)) 2
    have hsp : s < (p : ℝ) := (Nat.floor_lt hs0).mp (Finset.mem_Ioc.mp hinterval).1
    have hcompare : (1 : ℝ) / (p : ℝ) ^ 2 ≤ Real.log (p : ℝ) / (s ^ 2 * Real.log s) := by
      apply (div_le_div_iff₀ hp2 hsDen).mpr
      rw [one_mul, mul_comm (Real.log (p : ℝ))]
      exact square_mul_log_le hs hsp.le
    have hinv : (1 : ℝ) / (p : ℝ) ^ 2 = (p : ℝ)⁻¹ ^ 2 := by
      simp only [one_div, inv_pow]
    exact le_min (hcompare.trans (hprice p hp1)) hinv.le
  have hsubset : Nat.primesLE ⌊s⌋₊ ⊆ Nat.primesLE ⌊h / 2⌋₊ :=
    Nat.primesLE_mono (Nat.floor_mono hsb)
  have hdiff : Nat.primesLE ⌊h / 2⌋₊ \ Nat.primesLE ⌊s⌋₊ =
      (Finset.Ioc ⌊s⌋₊ ⌊h / 2⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpb, hp⟩, hpNot⟩
      exact ⟨⟨lt_of_not_ge (fun hps => hpNot ⟨hps, hp⟩), hpb⟩, hp⟩
    · rintro ⟨⟨hsp, hpb⟩, hp⟩
      exact ⟨⟨hpb, hp⟩, fun hps => (not_le_of_gt hsp) hps.1⟩
  have hsum := Finset.sum_sdiff hsubset
    (f := fun p : ℕ => min (primePrice h p) ((p : ℝ)⁻¹ ^ 2))
  rw [hdiff] at hsum
  unfold primeCost
  rw [← hsum]
  exact (add_le_add hsmall hlarge).trans_eq (add_comm _ _)

/-- The full positive prime cost pays the bulk weighted theta integral on
`(sqrt (2*h), h/2]`. Primes at the lower endpoint enter only the theta
prefix. The upper endpoint is included in the reciprocal-square sum. -/
theorem theta_weight_two_block_le_prime_cost {h : ℝ} (hh : 8 ≤ h) :
    (∫ t in Set.Ioc (Real.sqrt (2 * h)) (h / 2), Chebyshev.theta t * weight 2 t) ≤
      primeCost h := by
  let s := Real.sqrt (2 * h)
  let b := h / 2
  have hhPos : 0 < h := by linarith
  have htwoh : 0 ≤ 2 * h := by positivity
  have hs : 1 < s := by
    have hs2 : (2 : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
    linarith
  have hsb : s ≤ b := by
    change Real.sqrt (2 * h) ≤ h / 2
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith only [mul_nonneg hhPos.le (sub_nonneg.mpr hh)]
  have hden : h * Real.log h ≤ s ^ 2 * Real.log s := by
    calc
      h * Real.log h ≤ h * Real.log h + h * Real.log 2 :=
        le_add_of_nonneg_right (mul_nonneg hhPos.le (Real.log_nonneg (by norm_num)))
      _ = s ^ 2 * Real.log s := by
        dsimp only [s]
        rw [Real.sq_sqrt htwoh, Real.log_sqrt htwoh,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hhPos.ne']
        ring
  have hcost := prime_cost_ge_square_block (show 1 < h by linarith) hs hsb hden
  have habel := finite_theta_abel hs hsb
  rw [intervalIntegral.integral_of_le hsb] at habel
  have htop : 0 ≤ Chebyshev.theta b / (b ^ 2 * Real.log b) :=
    div_nonneg (Chebyshev.theta_nonneg b)
      (mul_nonneg (sq_nonneg b) (Real.log_pos (hs.trans_le hsb)).le)
  change (∫ t in Set.Ioc s b, Chebyshev.theta t * weight 2 t) ≤ primeCost h
  have hblock :
      Chebyshev.theta b / (b ^ 2 * Real.log b) +
        (∫ t in Set.Ioc s b, Chebyshev.theta t * weight 2 t) ≤ primeCost h := by
    change Chebyshev.theta s / (s ^ 2 * Real.log s) +
      (∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤
        primeCost h at hcost
    rw [habel] at hcost
    linarith only [hcost]
  linarith only [hblock, htop]

end D5.S3.Arith.Robin.AllSupportRobinCost
