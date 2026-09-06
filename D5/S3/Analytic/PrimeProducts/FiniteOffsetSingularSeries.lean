/- GID: D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries
   generality: G
   mirror-B: D5/B/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prime blocking checks coexist with a convergent all-prime singular series. -/

import D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion
import D5.S3.Analytic.PrimeProducts.FormalFactorTableCounterexamples

/- Library-search audit: the frozen residue criterion supplies both blocking
   clauses. Mathlib supplies Bernoulli's lower bound and prime-square summability.
   D5 and Mathlib body searches found no quadratic binomial upper remainder bound
   or finite-integer-offset singular-series convergence theorem. The upstream
   PrimeGapsLib singularSeries uses a different sieve-data local factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries

open FiniteLocalResidueBlockingCriterion
open FormalFactorTableCounterexamples

/-- The source's local correlation correction at a prime. -/
noncomputable def offsetLocalFactor (H : Finset Int) (p : Nat.Primes) : Real :=
  (1 - (localResidueCount H p.val : Real) / p.val) /
    (1 - 1 / (p.val : Real)) ^ H.card

/-- The numerical singular series retains the full prime index. -/
noncomputable def offsetSingularSeries (H : Finset Int) : Real :=
  ∏' p : Nat.Primes, offsetLocalFactor H p

private theorem binomial_remainder_le (x : Real) (hx : 0 <= x) (hx1 : x <= 1)
    (n : Nat) : (1 - x) ^ n - (1 - n * x) <= (n : Real) ^ 2 * x ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hidentity :
        (1 - x) ^ (n + 1) - (1 - (n + 1 : Nat) * x) =
          (1 - x) * ((1 - x) ^ n - (1 - n * x)) + n * x ^ 2 := by
      push_cast
      rw [pow_succ]
      ring
    rw [hidentity]
    have hstep := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hx1)
    have hn : (0 : Real) <= n := Nat.cast_nonneg n
    have hproduct : 0 <= x * ((n : Real) ^ 2 * x ^ 2) := by positivity
    push_cast
    nlinarith [sq_nonneg x, mul_nonneg hn (sq_nonneg x)]

private theorem offset_factor_deviation_summable (H : Finset Int) :
    Summable (fun p : Nat.Primes => |offsetLocalFactor H p - 1|) := by
  classical
  let diameter := (H.product H).sup (fun ab => (ab.2 - ab.1).natAbs)
  have residue_stabilizes (p : Nat.Primes) (hp : diameter < p.val) :
      localResidueCount H p.val = H.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have habcast : (a : ZMod p.val) = (b : ZMod p.val) := neg_injective hab
    have hdvd : (p.val : Int) ∣ b - a :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub a b p.val).mp habcast
    have hbound : (b - a).natAbs < (p.val : Int).natAbs := by
      simpa only [Int.natAbs_natCast] using
        (Finset.le_sup (f := fun ab : Int × Int => (ab.2 - ab.1).natAbs)
          (show (a, b) ∈ H.product H from Finset.mem_product.mpr ⟨ha, hb⟩)).trans_lt hp
    exact (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hbound)).symm
  have denominator_pos (p : Nat.Primes) :
      0 < (1 - 1 / (p.val : Real)) ^ H.card := by
    have hp : (1 : Real) < p.val := by exact_mod_cast p.property.one_lt
    exact pow_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hp)) _
  have tail_formula (p : Nat.Primes) (hp : diameter < p.val) :
      offsetLocalFactor H p - 1 =
        ((1 - (H.card : Real) / p.val) - (1 - 1 / (p.val : Real)) ^ H.card) /
          (1 - 1 / (p.val : Real)) ^ H.card := by
    dsimp only [offsetLocalFactor]
    rw [residue_stabilizes p hp, div_sub_one (ne_of_gt (denominator_pos p))]
  have quadratic_tail : exists C : Real, 0 < C ∧
      forall p : Nat.Primes, diameter < p.val ->
        |offsetLocalFactor H p - 1| <= C / (p.val : Real) ^ 2 := by
    refine ⟨((H.card : Real) ^ 2 + 1) / (1 / 2 : Real) ^ H.card, by positivity, ?_⟩
    intro p hp
    have hp2 : (2 : Real) <= p.val := by exact_mod_cast p.property.two_le
    let x : Real := 1 / p.val
    have hx : 0 <= x := by positivity
    have hxh : x <= 1 / 2 := by
      dsimp only [x]
      exact one_div_le_one_div_of_le (by positivity) hp2
    have hden : (1 / 2 : Real) ^ H.card <= (1 - x) ^ H.card :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hrem := binomial_remainder_le x hx (by linarith) H.card
    have hnonneg : 0 <= (1 - x) ^ H.card - (1 - H.card * x) := by
      have h := one_add_mul_le_pow (R := Real) (a := -x) (by linarith) H.card
      simp only [mul_neg, ← sub_eq_add_neg] at h
      exact sub_nonneg.mpr h
    rw [tail_formula p hp, abs_div, abs_of_pos (denominator_pos p)]
    have hnum : |1 - (H.card : Real) / p.val - (1 - 1 / (p.val : Real)) ^ H.card| <=
        (H.card : Real) ^ 2 * x ^ 2 := by
      have heq : 1 - (H.card : Real) / p.val - (1 - 1 / (p.val : Real)) ^ H.card =
          -((1 - x) ^ H.card - (1 - H.card * x)) := by dsimp only [x]; ring
      rw [heq, abs_neg, abs_of_nonneg hnonneg]
      exact hrem
    calc
      _ <= ((H.card : Real) ^ 2 * x ^ 2) / (1 / 2 : Real) ^ H.card :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ <= (((H.card : Real) ^ 2 + 1) * x ^ 2) / (1 / 2 : Real) ^ H.card := by
        gcongr
        linarith
      _ = _ := by dsimp only [x]; ring
  obtain ⟨C, _, htail⟩ := quadratic_tail
  have hsum : Summable (fun p : Nat.Primes => C / (p.val : Real) ^ 2) := by
    simpa only [Nat.Primes, div_eq_mul_inv, one_mul, Function.comp_apply] using
      ((Real.summable_one_div_nat_pow.mpr Nat.one_lt_two).subtype
        (fun p : Nat => p.Prime)).mul_left C
  apply hsum.of_norm_bounded_eventually
  have htend : Filter.Tendsto (fun p : Nat.Primes => p.val) Filter.cofinite Filter.atTop :=
    Nat.cofinite_eq_atTop ▸ Subtype.val_injective.tendsto_cofinite
  filter_upwards [htend.eventually (Filter.eventually_gt_atTop diameter)] with p hp
  simpa only [Real.norm_eq_abs, abs_abs] using htail p hp

/-- Blocking reduces to small primes, while the numerical correction is a
convergent product of the source's local factors over all primes. -/
theorem finite_offset_blocking_and_singular_series
    (H : Finset Int) (k : Nat) (hcard : H.card = k) :
    (forall p : Nat.Primes, k < p.val ->
      localResidueCount H p.val <= k ∧ localResidueCount H p.val < p.val) ∧
    ((forall p : Nat.Primes, localResidueCount H p.val < p.val) ↔
      forall p : Nat.Primes, p.val <= k -> localResidueCount H p.val < p.val) ∧
    HasProd (offsetLocalFactor H) (offsetSingularSeries H) := by
  obtain ⟨hlarge, hsmall⟩ := finite_local_residue_blocking_criterion H k hcard
  refine ⟨hlarge, hsmall, ?_⟩
  exact (absolute_convergence_admission_gives_multipliable (offsetLocalFactor H)
    (offset_factor_deviation_summable H)).hasProd

#print axioms offsetLocalFactor
#print axioms offsetSingularSeries
#print axioms binomial_remainder_le
#print axioms offset_factor_deviation_summable
#print axioms finite_offset_blocking_and_singular_series

end D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries
