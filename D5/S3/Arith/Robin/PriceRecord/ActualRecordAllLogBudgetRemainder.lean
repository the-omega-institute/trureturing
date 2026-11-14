/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Uniform all-fixed-real-log nonfirst remainder via an actual prefix-budget integer. -/

/- PREPARED SOURCE: UNCOMPILED_UNACCEPTED.
   Reconciled from the completed B snapshot (SHA256 a585dea0bd90c3a8...).
   The prefix source remains the completed snapshot (SHA256 39ab43e196ffb2b7...).
   Apply the exact producer patches supplied with this reconciliation before elaboration.
   ActualRecordCriticalResidual retains namespace ActualRecordHigherLayerResidual,
   already opened below; its exact record_prime_escape proof is only exposed.
   No build, parser, kernel check, registration or official acceptance was run.

   Mathematical inputs: the completed ordinary Pro calculation, corrected by
   the independent prefix-budget audit: theta_error_log_power already suffices
   for every fixed real logarithmic exponent. No exponential PNT reproof is used.
   Existing record mass/rigidity suppliers retain their original attribution.
   External X is the reference-price clock, never identified with log(N_X).
   Every loss below has the SAME original reference X, including losses at k. -/

import D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
import D5.S3.Arith.Robin.PriceRecord.ActualRecordCriticalResidual
import D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import D5.S3.Arith.Robin.PrimeValuation5040Bridge
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder

open Finset Filter Real
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (theta_error_log_power)
open D5.S3.Arith.Robin.PrimeValuation5040Bridge (primeBlock_factorization primeBlock_pos)
open D5.S3.Factorization.PrimePowers.FiniteCrtJoin (primePowerProduct)

def higherCore (n : ℕ) : ℕ :=
  primePowerProduct n.primeFactors (fun p => n.factorization p - 1)

def prefixInteger (Q : ℕ) : ℕ :=
  primePowerProduct (Nat.primesLE Q) (fun _ => 1)

theorem higher_core_pos (n : ℕ) : 0 < higherCore n :=
  primeBlock_pos (fun _ hp => Nat.prime_of_mem_primeFactors hp) _

theorem prefix_integer_pos (Q : ℕ) : 0 < prefixInteger Q :=
  primeBlock_pos (fun _ hp => (Nat.mem_primesLE.mp hp).2) _

private theorem higher_core_factorization (n p : ℕ) :
    (higherCore n).factorization p = n.factorization p - 1 := by
  classical
  rw [higherCore, primeBlock_factorization
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)]
  split_ifs with hp
  · rfl
  · have hz : n.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hp
    simp [hz]

private theorem prefix_integer_factorization (Q p : ℕ) :
    (prefixInteger Q).factorization p = if p ∈ Nat.primesLE Q then 1 else 0 := by
  exact primeBlock_factorization (fun _ hp => (Nat.mem_primesLE.mp hp).2) _ p

theorem higher_core_log {n P : ℕ} (hn : 0 < n)
    (hprefix : n.primeFactors = Nat.primesLE P) :
    log (higherCore n : ℝ) = log (n : ℝ) - Chebyshev.theta (P : ℝ) := by
  classical
  have hprod : log (higherCore n : ℝ) =
      ∑ p ∈ n.primeFactors, ((n.factorization p - 1 : ℕ) : ℝ) * log p := by
    simp only [higherCore, primePowerProduct, Nat.cast_prod, Nat.cast_pow]
    rw [Real.log_prod (fun p hp => pow_ne_zero _
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
    simp only [Real.log_pow]
  have hnlog : log (n : ℝ) =
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have htheta : Chebyshev.theta (P : ℝ) = ∑ p ∈ n.primeFactors, log p := by
    rw [hprefix, Chebyshev.theta_eq_sum_primesLE_log]
  rw [hprod, htheta, hnlog, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hv : 1 ≤ n.factorization p :=
    ((Nat.prime_of_mem_primeFactors hp).dvd_iff_one_le_factorization hn.ne').mp
      (Nat.dvd_of_mem_primeFactors hp)
  rw [Nat.cast_sub hv]
  ring

theorem prefix_integer_log (Q : ℕ) :
    log (prefixInteger Q : ℝ) = Chebyshev.theta (Q : ℝ) := by
  classical
  simp only [prefixInteger, primePowerProduct, Nat.cast_prod, pow_one]
  rw [Real.log_prod (fun p hp => by
    exact_mod_cast (Nat.mem_primesLE.mp hp).2.ne_zero)]
  exact (Chebyshev.theta_eq_sum_primesLE_log Q).symm

/-- The finite construction keeps every higher coordinate of n, including ties.
    It makes no record or optimality assertion about the constructed integer. -/
theorem prefix_budget_integer {n Q : ℕ} (hQ : 2 ≤ Q)
    (hsupport : ∀ p : ℕ, p.Prime → 2 ≤ n.factorization p → p ≤ Q) :
    let k := higherCore n * prefixInteger Q
    2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧
    log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) ∧
    ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →
      (j ≤ k.factorization p ↔ j ≤ n.factorization p) := by
  classical
  dsimp only
  let k := higherCore n * prefixInteger Q
  have hk0 : 0 < k := Nat.mul_pos (higher_core_pos n) (prefix_integer_pos Q)
  have hv (p : ℕ) : k.factorization p =
      n.factorization p - 1 + if p ∈ Nat.primesLE Q then 1 else 0 := by
    rw [show k = higherCore n * prefixInteger Q from rfl,
      Nat.factorization_mul (higher_core_pos n).ne' (prefix_integer_pos Q).ne',
      Finsupp.add_apply, higher_core_factorization, prefix_integer_factorization]
  have hpref : k.primeFactors = Nat.primesLE Q := by
    ext p
    constructor
    · intro hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hvpos : 1 ≤ k.factorization p :=
        (hprime.dvd_iff_one_le_factorization hk0.ne').mp (Nat.dvd_of_mem_primeFactors hp)
      by_cases hpQ : p ∈ Nat.primesLE Q
      · exact hpQ
      · rw [hv, if_neg hpQ] at hvpos
        exact False.elim (hpQ (Nat.mem_primesLE.mpr
          ⟨hsupport p hprime (by omega), hprime⟩))
    · intro hp
      have hprime := (Nat.mem_primesLE.mp hp).2
      apply hprime.mem_primeFactors _ hk0.ne'
      apply (hprime.dvd_iff_one_le_factorization hk0.ne').mpr
      rw [hv, if_pos hp]
      omega
  have h2dvd : 2 ∣ k := Nat.dvd_of_mem_primeFactors
    (hpref.symm ▸ Nat.mem_primesLE.mpr ⟨hQ, Nat.prime_two⟩)
  refine ⟨Nat.le_of_dvd hk0 h2dvd, hpref, ?_, ?_⟩
  · rw [Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (higher_core_pos n).ne')
        (by exact_mod_cast (prefix_integer_pos Q).ne'), prefix_integer_log]
  · intro p hp j hj
    rw [hv]
    by_cases hpQ : p ∈ Nat.primesLE Q
    · rw [if_pos hpQ]
      omega
    · rw [if_neg hpQ]
      have hnsmall : n.factorization p < 2 := by
        by_contra! hh
        exact hpQ (Nat.mem_primesLE.mpr ⟨hsupport p hp hh, hp⟩)
      omega

private theorem price_pos {X : ℝ} (hX : 1 < X) : 0 < referencePrice X :=
  ActualRecordHigherLayerResidual.reference_price_pos hX

/- The canonical optimizer's minimal divisibility gives a strict predecessor record. -/
private theorem canonical_record {X : ℝ} (hX : 12 < X) :
    2 ≤ strictInteger (referencePrice X) ∧
    (∀ n : ℕ, 0 < n → n < strictInteger (referencePrice X) →
      goldenResourceObjective (referencePrice X) n <
        goldenResourceObjective (referencePrice X) (strictInteger (referencePrice X))) ∧
    (largestPrime (strictInteger (referencePrice X)) : ℝ) < X := by
  let q := referencePrice X
  let N := strictInteger q
  have hq : 0 < q := price_pos (by linarith)
  have hspec := strictInteger_spec hq
  obtain ⟨r, hr11, hXr, hrX, hroot, _⟩ := half_shift_cutoff hX
  have hroot' : firstLayerPrice r = q := by simpa [q, referencePrice,
    D5.S3.Arith.Robin.ActualTwoPriceDefect.price] using hroot
  have hactive (p : ℕ) (hp : p.Prime) :
      1 ≤ N.factorization p ↔ (p : ℝ) < r := by
    rw [strict_layer_iff hq hp le_rfl,
      golden_layer_marginal_one_eq_log_one_add_inv hp]
    change q < firstLayerPrice (p : ℝ) ↔ (p : ℝ) < r
    rw [← hroot']
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    constructor
    · intro hh
      by_contra! hnot
      exact (not_lt_of_ge (firstLayerPrice_strictAnti.antitoneOn
        (show 1 < r by linarith) hp1 hnot)) hh
    · exact fun hh => firstLayerPrice_strictAnti hp1 (show 1 < r by linarith) hh
  have h2 : 2 ∣ N := (Nat.prime_two.dvd_iff_one_le_factorization
    (by have := hspec.1; omega : N ≠ 0)).mpr
      ((hactive 2 Nat.prime_two).mpr (by norm_num; linarith))
  have hN2 : 2 ≤ N := Nat.le_of_dvd (by have := hspec.1; omega) h2
  have hrec : ∀ n, 0 < n → n < N →
      goldenResourceObjective q n < goldenResourceObjective q N := by
    intro n hn hnm
    have hle := hspec.2.2.1 n (by omega)
    by_contra! hnot
    have heq := le_antisymm hle hnot
    have hnopt : IsGoldenResourceOptimal q n := by
      intro k hk
      rw [heq]
      exact hspec.2.2.1 k hk
    exact (Nat.le_of_dvd hn (hspec.2.2.2 n (by omega) hnopt)).not_gt hnm
  have hne : N.primeFactors.Nonempty := by
    exact ⟨2, Nat.prime_two.mem_primeFactors h2 (by omega)⟩
  obtain ⟨p, hp, hsup⟩ := exists_mem_eq_sup N.primeFactors hne id
  have hv : 1 ≤ N.factorization p :=
    ((Nat.prime_of_mem_primeFactors hp).dvd_iff_one_le_factorization
      (by omega : N ≠ 0)).mp (Nat.dvd_of_mem_primeFactors hp)
  have hpX := ((hactive p (Nat.prime_of_mem_primeFactors hp)).mp hv).trans
    (by linarith : r < X)
  refine ⟨hN2, hrec, ?_⟩
  change ((N.primeFactors.sup id : ℕ) : ℝ) < X
  rw [hsup]
  exact hpX

/- Clamp only the family parameter outside the tail. For X>13 this family is
   literally strictInteger(referencePrice X), not an alternative optimizer. -/
private def canonical (X : ℝ) : ℕ := strictInteger (referencePrice (max X 13))

private theorem canonical_escape :
    Tendsto (fun X : ℝ => (largestPrime (canonical X) : ℝ)) atTop atTop := by
  have hprice : Tendsto (fun X : ℝ => referencePrice X) atTop (𝓝 0) := by
    simpa only [referencePrice, one_div, Function.comp_def, id_eq] using
      tendsto_inv_atTop_zero.comp (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop)
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes ⌈B⌉₊
  have hpMarg : 0 < goldenLayerMarginal p 1 := by
    rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact div_pos (log_pos (by have := one_div_pos.mpr hp0; linarith)) hp.log_pos
  filter_upwards [eventually_gt_atTop (13 : ℝ),
    hprice.eventually (eventually_lt_nhds hpMarg)] with X hX hsmall
  have hq := price_pos (by linarith : 1 < X)
  have hv : 1 ≤ (canonical X).factorization p := by
    simpa only [canonical, max_eq_left hX.le] using
      (strict_layer_iff hq hp le_rfl).mpr hsmall
  have hN0 : canonical X ≠ 0 := by
    have hh := (canonical_record (by linarith [le_max_right X 13] : 12 < max X 13)).1
    change 2 ≤ canonical X at hh
    omega
  have hmem := hp.mem_primeFactors ((hp.dvd_iff_one_le_factorization hN0).mpr hv) hN0
  have hle : p ≤ largestPrime (canonical X) := le_sup (f := id) hmem
  exact (Nat.le_ceil B).trans ((by exact_mod_cast hpB : (⌈B⌉₊ : ℝ) ≤ p).trans
    (by exact_mod_cast hle))

private theorem canonical_core_bounds : ∀ᶠ X : ℝ in atTop,
    let N := strictInteger (referencePrice X)
    0 ≤ log (higherCore N : ℝ) ∧ log (higherCore N : ℝ) ≤ 2 * sqrt X ∧
    ∀ p : ℕ, p.Prime → 2 ≤ N.factorization p → (p : ℝ) ≤ 2 * sqrt X := by
  let m := canonical
  let q : ℝ → ℝ := fun X => referencePrice (max X 13)
  have hm (X : ℝ) : 2 ≤ m X :=
    (canonical_record (lt_of_lt_of_le (by norm_num) (le_max_right X 13))).1
  have hq (X : ℝ) : 0 < q X := price_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 13) (le_max_right X 13))
  have hrec (X : ℝ) :=
    (canonical_record (lt_of_lt_of_le (by norm_num) (le_max_right X 13))).2.1
  have hmass := (record_mass_limits m q hm hq hrec canonical_escape).1
  have hlayer := record_layer_ratio m q hm hq hrec canonical_escape 2 (by norm_num)
  have hmassSmall := hmass.eventually (eventually_lt_nhds
    (show sqrt (2 : ℝ) < 2 by nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]))
  have hlayerSmall := hlayer.eventually (eventually_lt_nhds (by norm_num : (2 : ℝ) < 4))
  filter_upwards [eventually_gt_atTop (13 : ℝ), hmassSmall, hlayerSmall,
    canonical_escape.eventually_gt_atTop 0] with X hX hH hL hP
  let N := strictInteger (referencePrice X)
  have hcan : canonical X = N := by simp only [canonical, max_eq_left hX.le, N]
  have hrecX := (canonical_record (by linarith : 12 < X)).2.1
  have hN := (canonical_record (by linarith : 12 < X)).1
  change 2 ≤ N at hN
  have hpref := (price_record_prime_structure hN (price_pos (by linarith)) hrecX).2
  have hlog := higher_core_log (by omega : 0 < N) hpref
  have hPN : (largestPrime N : ℝ) < X := (canonical_record (by linarith)).2.2
  have hPN0 : 0 < (largestPrime N : ℝ) := by simpa only [hcan] using hP
  have hH' : log (higherCore N : ℝ) < 2 * sqrt (largestPrime N : ℝ) := by
    apply (div_lt_iff₀ (sqrt_pos.mpr hPN0)).mp
    simpa only [m, q, hcan, hlog] using hH
  have hL' : (layerPrime N 2 : ℝ) ^ 2 < 4 * (largestPrime N : ℝ) := by
    apply (div_lt_iff₀ hPN0).mp
    simpa only [m, hcan] using hL
  refine ⟨log_nonneg (by exact_mod_cast
      (show 1 ≤ higherCore N by have := higher_core_pos N; omega)),
    hH'.le.trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hPN.le) (by norm_num)), ?_⟩
  intro p hp hv
  have hpQ : p ≤ layerPrime N 2 := by
    have hN0 : N ≠ 0 := by omega
    have hv1 : 1 ≤ N.factorization p := (by norm_num : 1 ≤ (2 : ℕ)).trans hv
    have hmem : p ∈ N.primeFactors := hp.mem_primeFactors
      ((hp.dvd_iff_one_le_factorization hN0).mpr hv1) hN0
    exact (le_sup (f := id) (mem_filter.mpr ⟨hmem, hv⟩)).trans (le_max_right _ _)
  have hs := sq_sqrt (show 0 ≤ X by linarith)
  have hQ0 : (0 : ℝ) ≤ layerPrime N 2 := Nat.cast_nonneg _
  have hQ : (layerPrime N 2 : ℝ) ≤ 2 * sqrt X := by
    nlinarith [sqrt_nonneg X]
  exact (by exact_mod_cast hpQ : (p : ℝ) ≤ layerPrime N 2).trans hQ

/- The crossing is on NATURAL indices; no next-prime API, primality of Q,
   or implication theta(P)=theta(Q) -> P=Q is used. -/
private theorem theta_step_bound {Q : ℕ} (hQ : 2 ≤ Q) :
    Chebyshev.theta ((Q + 1 : ℕ) : ℝ) - Chebyshev.theta (Q : ℝ) ≤
      log ((Q + 1 : ℕ) : ℝ) := by
  classical
  have hsub : Nat.primesLE Q ⊆ Nat.primesLE (Q + 1) := Nat.primesLE_mono (by omega)
  have hdiff : Nat.primesLE (Q + 1) \ Nat.primesLE Q ⊆ {Q + 1} := by
    intro p hp
    obtain ⟨hpa, hpb⟩ := mem_sdiff.mp hp
    obtain ⟨hpQ, hprime⟩ := Nat.mem_primesLE.mp hpa
    have hn : ¬ p ≤ Q := fun hh => hpb (Nat.mem_primesLE.mpr ⟨hh, hprime⟩)
    simpa only [mem_singleton] using (show p = Q + 1 by omega)
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
    ← sum_sdiff hsub, add_sub_cancel_right]
  calc
    _ ≤ ∑ p ∈ ({Q + 1} : Finset ℕ), log (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hdiff (fun p hp _ => by
        have he : p = Q + 1 := mem_singleton.mp hp
        subst p
        exact log_nonneg (by exact_mod_cast (show 1 ≤ Q + 1 by omega)))
    _ = _ := by simp

private theorem theta_crossing {Y : ℝ}
    (hY : Chebyshev.theta (2 : ℝ) ≤ Y) :
    ∃ Q : ℕ, 2 ≤ Q ∧ Chebyshev.theta (Q : ℝ) ≤ Y ∧
      Y < Chebyshev.theta ((Q + 1 : ℕ) : ℝ) ∧
      Y - Chebyshev.theta (Q : ℝ) < log ((Q + 1 : ℕ) : ℝ) ∧
      ∀ n : ℕ, Y < Chebyshev.theta (n : ℝ) → Q + 1 ≤ n := by
  have htheta : Tendsto Chebyshev.theta atTop atTop := by
    have hh := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
    have ht := hh.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) tendsto_id
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact div_mul_cancel₀ _ ht.ne'
  have hex : ∃ n : ℕ, Y < Chebyshev.theta (n : ℝ) :=
    ((htheta.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop Y).exists
  let n0 := Nat.find hex
  have hn0 : Y < Chebyshev.theta (n0 : ℝ) := Nat.find_spec hex
  have hn3 : 3 ≤ n0 := by
    by_contra! hsmall
    have hn2 : (n0 : ℝ) ≤ 2 := by exact_mod_cast (show n0 ≤ 2 by omega)
    linarith [Chebyshev.theta_mono hn2]
  let Q := n0 - 1
  have hQ : 2 ≤ Q := by dsimp [Q]; omega
  have hsucc : Q + 1 = n0 := by dsimp [Q]; omega
  have hθQ : Chebyshev.theta (Q : ℝ) ≤ Y := by
    exact le_of_not_gt (Nat.find_min hex (by dsimp [Q]; omega : Q < n0))
  have hstep := theta_step_bound hQ
  refine ⟨Q, hQ, hθQ, by simpa only [hsucc] using hn0, ?_, ?_⟩
  · rw [hsucc] at hstep ⊢
    linarith
  · intro n hn
    rw [hsucc]
    exact Nat.find_min' hex hn

/- This auxiliary inequality is only logarithmic shell arithmetic, not a new
   PNT transfer theorem. Its consumers are localization and the rate estimate. -/
theorem log_shell {X : ℝ} (hX : 4 < X) :
    0 < log (X / 2) ∧ log X / 2 ≤ log (X / 2) ∧ log (2 * X) ≤ 2 * log X := by
  have hX0 : 0 < X := by linarith
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog4 : 2 * log (2 : ℝ) ≤ log X := by
    calc
      _ = log ((2 : ℝ) ^ 2) := (Real.log_pow (2 : ℝ) 2).symm
      _ = log (4 : ℝ) := by norm_num
      _ ≤ _ := log_le_log (by norm_num) hX.le
  simp only [Real.log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne']
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/- Eventually choose the concrete crossing Q, core L and actual k. All witnesses
   here depend on X alone; no original m or original mu has been chosen. -/
structure Budget where
  Q : ℕ
  k : ℕ
  h : ℝ
  δ : ℝ
  r : ℝ

def Budget.spec (X : ℝ) (b : Budget) : Prop :=
  let Q := b.Q
  let k := b.k
  let h := b.h
  let δ := b.δ
  let r := b.r

  2 ≤ k ∧ k = higherCore (strictInteger (referencePrice X)) * prefixInteger Q ∧
  h = log (higherCore (strictInteger (referencePrice X)) : ℝ) ∧
  0 ≤ h ∧ h ≤ 2 * sqrt X ∧
  (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X) ∧
  0 ≤ δ ∧ δ < log (2 * X) ∧ δ ≤ sqrt X ∧
  log (k : ℝ) + δ = X ∧ k.primeFactors = Nat.primesLE Q ∧
  r ∈ Set.Icc (X / 2) (2 * X) ∧ 0 < X - r ∧ X - r < 1 ∧
  firstLayerPrice r = referencePrice X ∧
  (∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →
    (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p))

theorem canonical_budget_eventually : ∀ᶠ X : ℝ in atTop,
    ∃ b : Budget, b.spec X := by
  have hlogsmall (n : ℕ) : Tendsto (fun X : ℝ => log X ^ n / sqrt X) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop n (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun X : ℝ => sqrt X / X) atTop (𝓝 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have htheta := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  have htlo : Tendsto (fun X : ℝ => X / 2 + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hthi : Tendsto (fun X : ℝ => 3 * X / 2) atTop atTop :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).atTop_div_const (by norm_num)
  have hloRatio : Tendsto (fun X : ℝ => (X / 2 + 1) / X) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ))).add
      (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun X : ℝ => 1 / X) atTop (𝓝 0))
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    field_simp
    <;> ring
  have hlo : Tendsto (fun X : ℝ => Chebyshev.theta (X / 2 + 1) / X)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hh := (htheta.comp htlo).mul hloRatio
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    change (Chebyshev.theta (X / 2 + 1) / (X / 2 + 1)) *
      ((X / 2 + 1) / X) = Chebyshev.theta (X / 2 + 1) / X
    exact div_mul_div_cancel₀ (by linarith : X / 2 + 1 ≠ 0)
  have hhi : Tendsto (fun X : ℝ => Chebyshev.theta (3 * X / 2) / X)
      atTop (𝓝 (3 / 2 : ℝ)) := by
    have hh := (htheta.comp hthi).mul_const (3 / 2 : ℝ)
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    change (Chebyshev.theta (3 * X / 2) / (3 * X / 2)) * (3 / 2) =
      Chebyshev.theta (3 * X / 2) / X
    have he : (3 / 2 : ℝ) = (3 * X / 2) / X := by field_simp <;> ring
    rw [he, div_mul_div_cancel₀ (by positivity : 3 * X / 2 ≠ 0)]
  have hθ2 : Tendsto (fun X : ℝ => Chebyshev.theta 2 / X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hslack : Tendsto (fun X : ℝ => log (2 * X) / sqrt X) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
      : Tendsto (fun X : ℝ => log 2 / sqrt X) atTop (𝓝 0)).add (hlogsmall 1)
    simp only [zero_add, pow_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX.ne', add_div]
  filter_upwards [canonical_core_bounds, eventually_gt_atTop (13 : ℝ),
    hlo.eventually (eventually_lt_nhds (by norm_num : (1 / 2 : ℝ) < 3 / 4)),
    hhi.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) < 3 / 2)),
    hsqrt.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    hθ2.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hslack.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with X hcore hX hlo hhi hs hθ2 hslack
  let N := strictInteger (referencePrice X)
  let h := log (higherCore N : ℝ)
  obtain ⟨hh0, hhbound, hsupport⟩ := hcore
  change 0 ≤ h at hh0
  change h ≤ 2 * sqrt X at hhbound
  have hX0 : 0 < X := by linarith
  have hsbound : 2 * sqrt X < X / 4 := by
    have hh := (div_lt_iff₀ hX0).mp hs
    linarith
  have hlo' : Chebyshev.theta (X / 2 + 1) ≤ X - 2 * sqrt X := by
    have hh := (div_lt_iff₀ hX0).mp hlo
    linarith
  have hhi' : X < Chebyshev.theta (3 * X / 2) := by
    simpa only [one_mul] using (lt_div_iff₀ hX0).mp hhi
  have hY2 : Chebyshev.theta (2 : ℝ) ≤ X - h := by
    have hh := (div_lt_iff₀ hX0).mp hθ2
    linarith
  obtain ⟨Q, hQ2, hQlo, hQhi, hδjump, hminimal⟩ := theta_crossing hY2
  have hQshellLow : X / 2 ≤ (Q : ℝ) := by
    by_contra! hsmall
    have hnlo : ((Q + 1 : ℕ) : ℝ) ≤ X / 2 + 1 := by push_cast; linarith
    have hh := Chebyshev.theta_mono hnlo
    linarith
  have hcrossUpper : X - h < Chebyshev.theta (⌈3 * X / 2⌉₊ : ℝ) := by
    have hh := Chebyshev.theta_mono (Nat.le_ceil (3 * X / 2))
    linarith
  have hnatUpper := hminimal _ hcrossUpper
  have hceil : (⌈3 * X / 2⌉₊ : ℝ) ≤ 2 * X := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 3 * X / 2 by positivity)
    linarith
  have hsuccUpper : ((Q + 1 : ℕ) : ℝ) ≤ 2 * X :=
    (by exact_mod_cast hnatUpper : ((Q + 1 : ℕ) : ℝ) ≤ ⌈3 * X / 2⌉₊).trans hceil
  have hQshell : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X) :=
    ⟨hQshellLow, by push_cast at hsuccUpper; linarith⟩
  let δ := X - h - Chebyshev.theta (Q : ℝ)
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hQlo
  have hδlog : δ < log (2 * X) := hδjump.trans_le
    (log_le_log (by exact_mod_cast (show 0 < Q + 1 by omega)) hsuccUpper)
  have hδsqrt : δ ≤ sqrt X := hδlog.le.trans
    (by simpa only [one_mul] using ((div_lt_iff₀ (sqrt_pos.mpr hX0)).mp hslack).le)
  have hsupportQ (p : ℕ) (hp : p.Prime) (hv : 2 ≤ N.factorization p) : p ≤ Q := by
    have hh := hsupport p hp hv
    exact_mod_cast (hh.trans (by linarith : 2 * sqrt X ≤ (Q : ℝ)))
  let k := higherCore N * prefixInteger Q
  obtain ⟨hk2, hkpref, hklog, hkhigher⟩ := prefix_budget_integer hQ2 hsupportQ
  obtain ⟨r, hr11, hXr, hrX, hroot, _⟩ := half_shift_cutoff (by linarith : 12 < X)
  refine ⟨⟨Q, k, h, δ, r⟩, hk2, rfl, rfl, hh0, hhbound, hQshell,
    hδ0, hδlog, hδsqrt, ?_, hkpref, ?_, hXr, by linarith, ?_, ?_⟩
  · change log (k : ℝ) + (X - h - Chebyshev.theta (Q : ℝ)) = X
    rw [hklog]
    dsimp only [h]
    ring
  · constructor <;> linarith
  · simpa only [D5.S3.Arith.Robin.ActualTwoPriceDefect.price, referencePrice] using hroot
  · intro p hp j hj
    rw [hkhigher p hp j hj, strictInteger_counts (price_pos (by linarith))]

private def budget (X : ℝ) : Budget := by
  classical
  exact if hb : ∃ b : Budget, b.spec X then Classical.choose hb else ⟨0, 0, 0, 0, 0⟩

private theorem budget_spec : ∀ᶠ X : ℝ in atTop, (budget X).spec X := by
  filter_upwards [canonical_budget_eventually] with X hX
  simpa only [budget, dif_pos hX] using Classical.choose_spec hX

/- The family theorem is applied to the ORIGINAL records. This consumed helper
   consumes the original record_prime_escape through the exposure patch. -/
theorem original_record_bounds {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ x, 2 ≤ m x) (hmu : ∀ x, 0 < mu x)
    (hrecord : ∀ x k, 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x))
    (hX : Tendsto (fun x => log (m x : ℝ)) l atTop) : ∀ᶠ x in l,
    let X := log (m x : ℝ)
    let P := largestPrime (m x)
    (P : ℝ) ∈ Set.Icc (X / 2) (2 * X) ∧
      0 ≤ X - Chebyshev.theta (P : ℝ) ∧
      X - Chebyshev.theta (P : ℝ) ≤ 4 * sqrt X := by
  have hP := record_prime_escape m mu hm hmu hrecord hX
  have hmass := record_mass_limits m mu hm hmu hrecord hP
  have hclock : Tendsto (fun x => log (m x : ℝ) / (largestPrime (m x) : ℝ))
      l (𝓝 1) := hmass.2.2.1
  filter_upwards [hX.eventually_gt_atTop 13, hP.eventually_gt_atTop 0,
    hclock.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hclock.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)),
    hmass.1.eventually (eventually_lt_nhds
      (show sqrt (2 : ℝ) < 2 by nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]))]
      with x hX13 hP0 hlow hhigh hmassSmall
  let X := log (m x : ℝ)
  let P := largestPrime (m x)
  have hPlo : X / 2 ≤ (P : ℝ) := by
    have hh := (div_lt_iff₀ hP0).mp hhigh
    change X < 2 * (P : ℝ) at hh
    linarith
  have hPhi : (P : ℝ) ≤ 2 * X := by
    have hh := (lt_div_iff₀ hP0).mp hlow
    change (1 / 2 : ℝ) * P < X at hh
    linarith
  have hpref := (price_record_prime_structure (hm x) (hmu x) (hrecord x)).2
  have hcore := higher_core_log (by have := hm x; omega : 0 < m x) hpref
  have hH0 : 0 ≤ X - Chebyshev.theta (P : ℝ) := by
    rw [← hcore]
    exact log_nonneg (by exact_mod_cast
      (show 1 ≤ higherCore (m x) by have := higher_core_pos (m x); omega))
  have hH : X - Chebyshev.theta (P : ℝ) ≤ 2 * sqrt (P : ℝ) :=
    ((div_lt_iff₀ (sqrt_pos.mpr hP0)).mp hmassSmall).le
  have hsP : sqrt (P : ℝ) ≤ 2 * sqrt X := by
    have hX0 : 0 ≤ X := by dsimp [X]; linarith
    nlinarith [sq_sqrt hP0.le, sq_sqrt hX0, sqrt_nonneg (P : ℝ), sqrt_nonneg X]
  exact ⟨⟨hPlo, hPhi⟩, hH0, hH.trans (by linarith)⟩

/- A direct same-reference application, not an assumed energy bound.
   E is just the sum of the two endpoint errors, not a new analytic premise. -/
private theorem actual_budget_envelope {X mu : ℝ} {m : ℕ}
    (hX : 13 < X) (hm : 2 ≤ m) (hmu : 0 < mu)
    (hrecord : ∀ k : ℕ, 0 < k → k < m →
      goldenResourceObjective mu k < goldenResourceObjective mu m)
    (hclock : X = log (m : ℝ)) (b : Budget) (hb : b.spec X)
    (hP : (largestPrime m : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (hH0 : 0 ≤ X - Chebyshev.theta (largestPrime m : ℝ))
    (hH : X - Chebyshev.theta (largestPrime m : ℝ) ≤ 4 * sqrt X) :
    let R := actualDefect X m - completeFirstLayerLoss X m
    let E := |Chebyshev.theta (largestPrime m : ℝ) - (largestPrime m : ℝ)| +
      |Chebyshev.theta (b.Q : ℝ) - (b.Q : ℝ)|
    0 ≤ R ∧ R ≤ 300 / (X * log X) + 60 * E / (X * sqrt X * log X) + 2 / X := by
  obtain ⟨hk2, _hkdef, _hdef, hh0, hh, hQ, hδ0, hδlog, hδs, hbudget,
    hkpref, hr, hXr, hrX, hroot, hhigher⟩ := hb
  let P := largestPrime m
  let H := X - Chebyshev.theta (P : ℝ)
  let eP := Chebyshev.theta (P : ℝ) - (P : ℝ)
  let eQ := Chebyshev.theta (b.Q : ℝ) - (b.Q : ℝ)
  let E := |eP| + |eQ|
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < log X := log_pos (by linarith)
  have hs0 : 0 < sqrt X := sqrt_pos.mpr hX0
  have hs1 : 1 ≤ sqrt X := by nlinarith [sq_sqrt hX0.le, sqrt_nonneg X]
  have hshell := log_shell (by linarith : 4 < X)
  have hlogHalf : 0 < log (X / 2) := hshell.1
  have hpref := (price_record_prime_structure hm hmu hrecord).2
  have hfinite := actual_record_prefix_budget_residual (by linarith : 4 < X)
    hm hk2 hmu hrecord hclock hpref hkpref hP hQ hr hroot hδ0 hbudget hhigher
  have hθQ : Chebyshev.theta (b.Q : ℝ) = X - b.h - b.δ := by
    rw [show log (b.k : ℝ) = b.h + Chebyshev.theta (b.Q : ℝ) from by
      rw [_hkdef, Nat.cast_mul,
        Real.log_mul
          (by exact_mod_cast (higher_core_pos (strictInteger (referencePrice X))).ne')
          (by exact_mod_cast (prefix_integer_pos b.Q).ne'),
        prefix_integer_log, ← _hdef]] at hbudget
    linarith
  have heP : (P : ℝ) - b.r = (X - b.r) - H - eP := by dsimp [H, eP]; ring
  have heQ : (b.Q : ℝ) - b.r = (X - b.r) - (b.h + b.δ) - eQ := by
    dsimp [eQ]
    linarith
  have hH' : H ≤ 4 * sqrt X := hH
  have habsXr : |X - b.r| ≤ 1 := by rw [abs_of_pos hXr]; exact hrX.le
  have habs_sub (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b
  have hVP : |(P : ℝ) - b.r| ≤ 5 * sqrt X + E := by
    rw [heP]
    have hhabs : |H| = H := abs_of_nonneg hH0
    have htri := (habs_sub ((X - b.r) - H) eP).trans
      (add_le_add (habs_sub (X - b.r) H) (le_refl _))
    rw [hhabs] at htri
    dsimp [E]
    nlinarith [abs_nonneg eQ]
  have hVQ : |(b.Q : ℝ) - b.r| ≤ 5 * sqrt X + E := by
    rw [heQ]
    have hhabs : |b.h + b.δ| = b.h + b.δ := abs_of_nonneg (add_nonneg hh0 hδ0)
    have htri := (habs_sub ((X - b.r) - (b.h + b.δ)) eQ).trans
      (add_le_add (habs_sub (X - b.r) (b.h + b.δ)) (le_refl _))
    rw [hhabs] at htri
    dsimp [E]
    nlinarith [abs_nonneg eP]
  have hV : max (|(P : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) ≤ 5 * sqrt X + E :=
    max_le hVP hVQ
  have hW : |Chebyshev.theta (P : ℝ) - Chebyshev.theta (b.Q : ℝ)| ≤ 5 * sqrt X := by
    apply abs_le.mpr
    rw [hθQ]
    constructor <;> linarith
  have hE : 0 ≤ E := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmain : 6 * max (|(P : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
      |Chebyshev.theta (P : ℝ) - Chebyshev.theta (b.Q : ℝ)| /
        (X ^ 2 * log (X / 2)) ≤
      300 / (X * log X) + 60 * E / (X * sqrt X * log X) := by
    calc
      _ ≤ 6 * (5 * sqrt X + E) * (5 * sqrt X) / (X ^ 2 * log (X / 2)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num)) hW
          (abs_nonneg _) (by positivity)
      _ ≤ 6 * (5 * sqrt X + E) * (5 * sqrt X) / (X ^ 2 * (log X / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hshell.2.1 (by positivity))
      _ = _ := by
        have halgebra (s L e : ℝ) (hs : s ≠ 0) (hL : L ≠ 0) :
            6 * (5 * s + e) * (5 * s) / ((s ^ 2) ^ 2 * (L / 2)) =
              300 / (s ^ 2 * L) + 60 * e / (s ^ 2 * s * L) := by
          field_simp
          <;> ring
        simpa only [sq_sqrt hX0.le] using halgebra (sqrt X) (log X) E hs0.ne' hlogX.ne'
  have hslack : b.δ / (X * log X) ≤ 2 / X := by
    calc
      _ ≤ (2 * log X) / (X * log X) :=
        div_le_div_of_nonneg_right (hδlog.le.trans hshell.2.2) (by positivity)
      _ = _ := by field_simp
  exact ⟨hfinite.1, hfinite.2.trans (add_le_add hmain hslack)⟩

/- Directly consume the all-real PNT at the endpoint t (eventually either P or
   Q). This helper has no independent analytic assumptions and no public API. -/
private theorem weighted_endpoint_error {α : Type*} {l : Filter α}
    {X t : α → ℝ} (hX : Tendsto X l atTop)
    (htube : ∀ᶠ x in l, t x ∈ Set.Icc (X x / 2) (2 * X x)) (n : ℕ) :
    Tendsto (fun x => |Chebyshev.theta (t x) - t x| * log (X x) ^ n / X x)
      l (𝓝 0) := by
  have ht : Tendsto t l atTop := tendsto_atTop_mono' l
    (htube.mono fun x hx => hx.1) (hX.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have he := ((theta_error_log_power n).tendsto_div_nhds_zero.comp ht).abs
  simp only [abs_zero] at he
  have hu := he.const_mul ((2 : ℝ) ^ (n + 1))
  simp only [mul_zero] at hu
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [hX.eventually_gt_atTop 4] with x hx
    exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (log_pos (by linarith)).le _))
      (by linarith)
  · filter_upwards [hX.eventually_gt_atTop 4, htube] with x hx htx
    have hx0 : 0 < X x := by linarith
    have ht1 : 1 < t x := by linarith [htx.1]
    have ht0 : 0 < t x := by linarith
    have hlogt : 0 < log (t x) := log_pos ht1
    have hlt : log (X x) ≤ 2 * log (t x) := by
      have hh := (log_shell hx).2.1.trans (log_le_log (by linarith) htx.1)
      linarith
    have hlpow : log (X x) ^ n ≤ (2 : ℝ) ^ n * log (t x) ^ n := by
      simpa only [mul_pow] using pow_le_pow_left₀ (log_pos (by linarith : 1 < X x)).le hlt n
    have htxdiv : t x / X x ≤ 2 := (div_le_iff₀ hx0).mpr htx.2
    calc
      _ ≤ |Chebyshev.theta (t x) - t x| * ((2 : ℝ) ^ n * log (t x) ^ n) / X x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlpow (abs_nonneg _)) hx0.le
      _ = ((2 : ℝ) ^ n * (|Chebyshev.theta (t x) - t x| * log (t x) ^ n / t x)) *
          (t x / X x) := by field_simp <;> ring
      _ ≤ ((2 : ℝ) ^ n * (|Chebyshev.theta (t x) - t x| * log (t x) ^ n / t x)) * 2 :=
        mul_le_mul_of_nonneg_left htxdiv (by positivity)
      _ = (2 : ℝ) ^ (n + 1) *
          |(Chebyshev.theta (t x) - t x) / (t x / log (t x) ^ n)| := by
        rw [abs_div, abs_of_pos (div_pos ht0 (pow_pos (log_pos ht1) _)), pow_succ]
        field_simp [(log_pos ht1).ne', ht0.ne']
        <;> ring

private theorem record_family_natural_rate {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ x, 2 ≤ m x) (hmu : ∀ x, 0 < mu x)
    (hrecord : ∀ x k, 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x))
    (hX : Tendsto (fun x => log (m x : ℝ)) l atTop) (n : ℕ) :
    Tendsto (fun x =>
      let X := log (m x : ℝ)
      sqrt X * log X ^ (n + 1) * (actualDefect X (m x) - completeFirstLayerLoss X (m x)))
      l (𝓝 0) ∧
    ∀ᶠ x in l, 0 ≤ actualDefect (log (m x : ℝ)) (m x) -
      completeFirstLayerLoss (log (m x : ℝ)) (m x) := by
  let X : α → ℝ := fun x => log (m x : ℝ)
  let P : α → ℝ := fun x => largestPrime (m x)
  let Q : α → ℝ := fun x => (budget (X x)).Q
  let R : α → ℝ := fun x => actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)
  have hB : ∀ᶠ x in l, (budget (X x)).spec (X x) := hX.eventually budget_spec
  have hrecords := original_record_bounds m mu hm hmu hrecord hX
  have hPtube : ∀ᶠ x in l, P x ∈ Set.Icc (X x / 2) (2 * X x) :=
    hrecords.mono fun _ hx => hx.1
  have hQtube : ∀ᶠ x in l, Q x ∈ Set.Icc (X x / 2) (2 * X x) := by
    filter_upwards [hB] with x hx
    rcases hx with ⟨_, _, _, _, _, hQ, _⟩
    exact hQ
  have hEP := weighted_endpoint_error hX hPtube n
  have hEQ := weighted_endpoint_error hX hQtube n
  have hsmall (j : ℕ) : Tendsto (fun x => log (X x) ^ j / sqrt (X x)) l (𝓝 0) := by
    have hh := (isLittleO_log_rpow_rpow_atTop j
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp hX
    simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow, Function.comp_def, X] using hh
  have hupper := (((hsmall n).const_mul 300).add
    ((hEP.add hEQ).const_mul 60)).add ((hsmall (n + 1)).const_mul 2)
  simp only [mul_zero, zero_add] at hupper
  have hfinite : ∀ᶠ x in l,
      0 ≤ R x ∧
      sqrt (X x) * log (X x) ^ (n + 1) * R x ≤
        300 * (log (X x) ^ n / sqrt (X x)) +
        60 * (|Chebyshev.theta (P x) - P x| * log (X x) ^ n / X x +
          |Chebyshev.theta (Q x) - Q x| * log (X x) ^ n / X x) +
        2 * (log (X x) ^ (n + 1) / sqrt (X x)) := by
    filter_upwards [hB, hrecords, hX.eventually_gt_atTop 13] with x hb hrec hx
    have henv := actual_budget_envelope hx (hm x) (hmu x) (hrecord x)
      rfl (budget (X x)) hb hrec.1 hrec.2.1 hrec.2.2
    have hx0 : 0 < X x := by linarith
    have hl0 : 0 < log (X x) := log_pos (by linarith)
    have hs0 : 0 < sqrt (X x) := sqrt_pos.mpr hx0
    have hscale : 0 ≤ sqrt (X x) * log (X x) ^ (n + 1) := by positivity
    refine ⟨henv.1, (mul_le_mul_of_nonneg_left henv.2 hscale).trans_eq ?_⟩
    change sqrt (X x) * log (X x) ^ (n + 1) *
      (300 / (X x * log (X x)) +
        60 * (|Chebyshev.theta (P x) - P x| + |Chebyshev.theta (Q x) - Q x|) /
          (X x * sqrt (X x) * log (X x)) + 2 / X x) = _
    have halgebra (s L e f : ℝ) (hs : s ≠ 0) (hL : L ≠ 0) :
        s * L ^ (n + 1) *
          (300 / (s ^ 2 * L) + 60 * (e + f) / (s ^ 2 * s * L) + 2 / s ^ 2) =
          300 * (L ^ n / s) + 60 * (e * L ^ n / s ^ 2 + f * L ^ n / s ^ 2) +
          2 * (L ^ (n + 1) / s) := by
      rw [pow_succ]
      field_simp
      <;> ring
    simpa only [sq_sqrt hx0.le] using halgebra (sqrt (X x)) (log (X x))
      |Chebyshev.theta (P x) - P x| |Chebyshev.theta (Q x) - Q x| hs0.ne' hl0.ne'
  refine ⟨?_, hfinite.mono fun _ hx => hx.1⟩
  apply squeeze_zero' ?_ (hfinite.mono fun _ hx => hx.2) hupper
  filter_upwards [hfinite, hX.eventually_gt_atTop 13] with x hx hlarge
  have hlog : 0 ≤ log (X x) := (log_pos (by linarith : 1 < X x)).le
  exact mul_nonneg (mul_nonneg (sqrt_nonneg _) (pow_nonneg hlog _)) hx.1

/-- UNCOMPILED_UNACCEPTED candidate. The threshold precedes EVERY original
    integer and arbitrary original positive price. The record is literal and
    strict against all positive predecessors; both signs of complete losses
    and the original all-layer integer are retained. No RH premise occurs. -/
theorem actual_record_all_real_log_residual :
    ∀ a : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 1 < X0 ∧
        ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
          (∀ k : ℕ, 0 < k → k < m →
            goldenResourceObjective mu k < goldenResourceObjective mu m) →
          X0 ≤ log (m : ℝ) →
          let X := log (m : ℝ)
          0 ≤ sqrt X * Real.rpow (log X) a *
            (actualDefect X m - completeFirstLayerLoss X m) ∧
          sqrt X * Real.rpow (log X) a *
            (actualDefect X m - completeFirstLayerLoss X m) < ε := by
  intro a ε hε
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt a
  have han : a ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧
    ∀ k : ℕ, 0 < k → k < v.1 →
      goldenResourceObjective v.2 k < goldenResourceObjective v.2 v.1}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let X : S → ℝ := fun x => log (m x : ℝ)
  let l : Filter S := comap X atTop
  have hX : Tendsto X l atTop := tendsto_comap
  have hm (x : S) : 2 ≤ m x := x.2.1
  have hmu (x : S) : 0 < mu x := x.2.2.1
  have hrecord (x : S) (k : ℕ) : 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x) := x.2.2.2 k
  have hrate := record_family_natural_rate m mu hm hmu hrecord hX n
  have hsmall := (Metric.tendsto_nhds.mp hrate.1) ε hε
  have hall : ∀ᶠ x in l,
      0 ≤ sqrt (X x) * Real.rpow (log (X x)) a *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) ∧
      sqrt (X x) * Real.rpow (log (X x)) a *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) < ε := by
    filter_upwards [hX.eventually_gt_atTop 13, hrate.2, hsmall] with x hx hR hsmallx
    have hx0 : 0 < X x := by linarith
    have hl1 : 1 ≤ log (X x) := ((Real.lt_log_iff_exp_lt hx0).mpr
      (Real.exp_one_lt_three.trans (by linarith))).le
    have hweight : Real.rpow (log (X x)) a ≤ log (X x) ^ (n + 1) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hl1 han
    have hdom : sqrt (X x) * Real.rpow (log (X x)) a *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) ≤
      sqrt (X x) * log (X x) ^ (n + 1) *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hweight (sqrt_nonneg _)) hR
    have hnsmall : sqrt (X x) * log (X x) ^ (n + 1) *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) < ε :=
      (le_abs_self _).trans_lt (by
        simpa only [Real.dist_eq, sub_zero, X, m] using hsmallx)
    exact ⟨mul_nonneg (mul_nonneg (sqrt_nonneg _)
      (Real.rpow_nonneg (by linarith) _)) hR, hdom.trans_lt hnsmall⟩
  -- One threshold in the own-log clock, selected before the record pair.
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max B 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn price hprice hrec hlarge
  let x : S := ⟨(n, price), hn, hprice, hrec⟩
  have hx := hB (log (n : ℝ)) ((le_max_left B 2).trans hlarge) x rfl
  simpa only [X, m] using hx

#print axioms actual_record_all_real_log_residual

end D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
