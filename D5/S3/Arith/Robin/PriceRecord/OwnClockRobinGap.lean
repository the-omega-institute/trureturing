/- GID: D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/OwnClockRobinGap
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Fixed-support own-clock decomposition for the original sigma/n Robin margin. -/

/- UNCOMPILED SOURCE CANDIDATE. No kernel or axiom-closure acceptance claimed.
The exact GoldenResource sigma identity and support factorization are reused.
Every supported integer exponent is at least one, and no support completion
or 5040-domain reduction is smuggled into the statement. -/

import D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
import D5.S3.Arith.GoldenResourceObjectiveFactorization
import D5.S3.Weil.GronwallLowerEnvelope

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.OwnClockRobinGap

open Real Finset
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Weil.GronwallLowerEnvelope
open D5.S0.Diagonal.MarginBound (bernoulliKL)

def supportInteger (S : Finset ℕ) (a : ℕ → ℕ) : ℕ := ∏ p ∈ S, p ^ a p

private lemma support_integer_pos {S : Finset ℕ} (hS : primeSupport S) (a : ℕ → ℕ) :
    0 < supportInteger S a := by
  exact prod_pos (fun p hp => pow_pos (hS p hp).pos _)

private lemma support_factorization {S : Finset ℕ} (hS : primeSupport S) (a : ℕ → ℕ) :
    (supportInteger S a).factorization = ∑ p ∈ S, Finsupp.single p (a p) := by
  rw [supportInteger, Nat.factorization_prod (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)]
  exact sum_congr rfl (fun p hp => (hS p hp).factorization_pow)

private lemma support_factorization_apply {S : Finset ℕ} (hS : primeSupport S)
    (a : ℕ → ℕ) (p : ℕ) :
    (supportInteger S a).factorization p = if p ∈ S then a p else 0 := by
  classical
  rw [support_factorization hS a]
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

private lemma support_subset {S : Finset ℕ} (hS : primeSupport S) (a : ℕ → ℕ) :
    (supportInteger S a).primeFactors ⊆ S := by
  intro p hp
  by_contra hn
  have hp' : p ∈ (supportInteger S a).factorization.support := by
    simpa only [Nat.support_factorization] using hp
  apply (Finsupp.mem_support_iff.mp hp')
  simpa [hn] using support_factorization_apply hS a p

private lemma support_exact {S : Finset ℕ} (hS : primeSupport S) (a : ℕ → ℕ)
    (ha : ∀ p ∈ S, 1 ≤ a p) : (supportInteger S a).primeFactors = S := by
  apply Finset.Subset.antisymm (support_subset hS a)
  intro p hp
  rw [← Nat.support_factorization, Finsupp.mem_support_iff,
    support_factorization_apply hS a p, if_pos hp]
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (ha p hp))

private lemma benefit_nat {p a : ℕ} (hp : p.Prime) :
    benefit p (a : ℝ) = goldenPrimeLocalObjective 0 p a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (p : ℝ) ^ (-((a : ℝ) + 1)) = ((p : ℝ)⁻¹) ^ (a + 1) := by
    rw [show -((a : ℝ) + 1) = -((a + 1 : ℕ) : ℝ) by push_cast; ring,
      rpow_neg hp0.le, rpow_natCast, inv_pow]
  simp only [benefit, goldenPrimeLocalObjective, hpow, rpow_neg_one,
    zero_mul, sub_zero]

/-- The logarithmic clock is that of the actual product, without a model parameter. -/
lemma support_integer_log {S : Finset ℕ} (hS : primeSupport S) (a : ℕ → ℕ) :
    log (supportInteger S a : ℝ) = clock S (fun p => (a p : ℝ)) := by
  have hp0 (p : ℕ) (hp : p ∈ S) : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
  simp only [supportInteger, Nat.cast_prod, Nat.cast_pow]
  rw [log_prod (fun p hp => pow_ne_zero _ (hp0 p hp))]
  simp only [log_pow, clock]

/-- Exact original-objective mapping: the finite support is the support used
in the sigma product, not a free gamma or a substituted toy objective. -/
lemma phi_eq_robin_margin {S : Finset ℕ} (hS : primeSupport S) (a : ℕ → ℕ) :
    phi S (fun p => (a p : ℝ)) = robinLogMargin (supportInteger S a) := by
  have hn : 1 ≤ supportInteger S a := support_integer_pos hS a
  have hsum := golden_resource_objective_sum_on 0 hn S (support_subset hS a)
  rw [golden_resource_sigma_identity 0 hn] at hsum
  simp only [zero_mul, sub_zero] at hsum
  have hlocal : (∑ p ∈ S, benefit p (a p : ℝ)) =
      ∑ p ∈ S, goldenPrimeLocalObjective 0 p ((supportInteger S a).factorization p) := by
    apply sum_congr rfl
    intro p hp
    rw [support_factorization_apply hS a p, if_pos hp, benefit_nat (hS p hp)]
  rw [phi, hlocal, ← hsum, ← support_integer_log hS a]
  rfl

private lemma integer_cast_toNat {S : Finset ℕ} (a : ℕ → ℤ)
    (ha : ∀ p ∈ S, 1 ≤ a p) {p : ℕ} (hp : p ∈ S) :
    ((a p).toNat : ℝ) = (a p : ℝ) := by
  have hnonneg : 0 ≤ a p := (by norm_num : (0 : ℤ) ≤ 1).trans (ha p hp)
  exact_mod_cast (Int.toNat_of_nonneg hnonneg)

private lemma phi_congr {S : Finset ℕ} {x y : ℕ → ℝ}
    (hxy : ∀ p ∈ S, x p = y p) : phi S x = phi S y := by
  have hclock : clock S x = clock S y := by
    apply sum_congr rfl
    intro p hp
    rw [hxy p hp]
  have hbenefit : (∑ p ∈ S, benefit p (x p)) = ∑ p ∈ S, benefit p (y p) := by
    apply sum_congr rfl
    intro p hp
    rw [hxy p hp]
  simp only [phi, hclock, hbenefit]

/-- For EVERY fixed prime support of size at least three and EVERY supported
integer exponent vector >=1, the original margin has the exact three-term
identity and dominates the finite floor/ceiling sum at its OWN clock.
The theorem includes the nonnegative components; T is never identified with L.
The integer n is literally product p^(a_p.toNat), so signed integer notation
does not remove any admissible vector or alter any exponent on S. -/
theorem original_margin_own_clock_gap {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (a : ℕ → ℤ) (ha : ∀ p ∈ S, 1 ≤ a p) :
    let x : ℕ → ℝ := fun p => (a p : ℝ)
    let n := supportInteger S (fun p => (a p).toNat)
    n.primeFactors = S ∧
    log (n : ℝ) = clock S x ∧
    robinLogMargin n - realInfimum S =
      (phi S (ownBoundary S x) - realInfimum S) +
        (∑ p ∈ S, priceLoss p (ownPrice S x) (x p)) +
          tangentRemainder (clock S x) (clock S (ownBoundary S x)) ∧
    0 ≤ phi S (ownBoundary S x) - realInfimum S ∧
    (∀ p ∈ S, 0 ≤ priceLoss p (ownPrice S x) (x p)) ∧
    0 ≤ tangentRemainder (clock S x) (clock S (ownBoundary S x)) ∧
    0 ≤ roundingSum S x ∧ roundingSum S x ≤ robinLogMargin n - realInfimum S ∧
    (∀ p ∈ S,
      ((p : ℝ) ^ (2 : ℕ) < cutoff (ownPrice S x) →
        priceLoss p (ownPrice S x) (x p) =
          bernoulliKL (cutoff (ownPrice S x))⁻¹ (probability p (x p)) /
            (1 - (cutoff (ownPrice S x))⁻¹) ∧
        integerGap p (ownPrice S x) =
          min (bernoulliKL (cutoff (ownPrice S x))⁻¹
              (probability p (⌊critical p (ownPrice S x)⌋ : ℤ)) /
                (1 - (cutoff (ownPrice S x))⁻¹))
            (bernoulliKL (cutoff (ownPrice S x))⁻¹
              (probability p (⌈critical p (ownPrice S x)⌉ : ℤ)) /
                (1 - (cutoff (ownPrice S x))⁻¹))) ∧
      (cutoff (ownPrice S x) ≤ (p : ℝ) ^ (2 : ℕ) →
        boundary p (ownPrice S x) = 1 ∧ integerGap p (ownPrice S x) = 0 ∧
        0 ≤ ownPrice S x - 1 / ((p : ℝ) ^ (2 : ℕ) - 1) ∧
        0 ≤ bernoulliKL ((p : ℝ) ^ (-2 : ℝ)) (probability p (x p)) /
          (1 - (p : ℝ) ^ (-2 : ℝ)) ∧
        priceLoss p (ownPrice S x) (x p) =
          bernoulliKL ((p : ℝ) ^ (-2 : ℝ)) (probability p (x p)) /
            (1 - (p : ℝ) ^ (-2 : ℝ)) +
              (ownPrice S x - 1 / ((p : ℝ) ^ (2 : ℕ) - 1)) * (x p - 1) * log p)) := by
  dsimp only
  let x : ℕ → ℝ := fun p => (a p : ℝ)
  let A : ℕ → ℕ := fun p => (a p).toNat
  have hx : admissible S x := by intro p hp; exact_mod_cast ha p hp
  have heq : ∀ p ∈ S, (A p : ℝ) = x p := by
    intro p hp
    exact integer_cast_toNat a ha hp
  have hA : ∀ p ∈ S, 1 ≤ A p := by
    intro p hp
    have hR : (1 : ℝ) ≤ (A p : ℝ) := by rw [heq p hp]; exact hx p hp
    exact_mod_cast hR
  have hclock : log (supportInteger S A : ℝ) = clock S x := by
    rw [support_integer_log hS A]
    apply sum_congr rfl
    intro p hp
    rw [heq p hp]
  have hmargin : robinLogMargin (supportInteger S A) = phi S x :=
    (phi_eq_robin_margin hS A).symm.trans (phi_congr heq)
  have hd := own_clock_decomposition hS hcard hx
  have hg := all_integer_gap hS hcard a ha
  refine ⟨support_exact hS A hA, hclock, ?_⟩
  rw [hmargin]
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, hg.1, hg.2, ?_⟩
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
  have hlam := own_price_pos hS hcard hx
  constructor
  · intro hactive
    exact ⟨(active_loss hpR hlam hactive (hx p hp)).1,
      active_integer_gap hpR hlam hactive⟩
  · intro hinactive
    exact inactive_loss hpR hlam hinactive (hx p hp)

end D5.S3.Arith.Robin.PriceRecord.OwnClockRobinGap
