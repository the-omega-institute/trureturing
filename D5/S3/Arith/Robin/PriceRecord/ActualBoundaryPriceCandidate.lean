/-
UNCOMPILED RESEARCH SOURCE. No Lean/Lake/build command has been run on this file.
N0 native parser/elaborator/kernel and accepted-axiom checks remain OPEN.
Base: 72017a80c3b3ba1e443d7e5dc8baa62851506fe9
Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679

Apply the unchanged exposure-72017.patch before importing this candidate.
It only removes `private` from two existing fixed-layer scale lemmas.

One proposed proof path closes the full source telescope M1--M4: direct count
first pools with radius C*P^(21/40), original actual high-layer geometry and
signed comparisons, then the original cost normalization with A=C. Only the
cost expression is enlarged to radius 2*C*K*(2P)^(21/40); no pool or width
assumption for that enlarged radius is introduced. The maximum-gap premise
is retained unused in the exact original final endpoint. Both analytic BHP
suppliers remain UNVERIFIED; source completion is not formal completion.

The same arbitrary positive-mu full record and ALL strict positive predecessors
are retained, with fixed j>=2 before constants and threshold. This packet is
for the NEXT substantive native step after current denominator delivery, not
independent admission/publication of helpers or a formal/RH/official success.
-/

import D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
import D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceCandidate

open Finset Filter Real
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
  (layerPrime valuation_below_layer_prime valuation_above_layer_prime
   signed_exchange_certificate)
open D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
  (record_ratio_limit coarse_scale_limits)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
  (powerSum powerSumDerivative beta logarithmicSlope powerSum_hasDerivAt
   powerSum_pos gain_pos beta_pos beta_nat beta_le_inv_pow_log)

/-- Full recordhood includes EVERY positive smaller integer, with no support cap. -/
def FullRecord (m : ℕ) (mu : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → n < m →
    goldenResourceObjective mu n < goldenResourceObjective mu m

def bhpExponent : ℝ := 21 / 40
def priceExponent (j : ℕ) : ℝ := 19 / (40 * (j : ℝ))
def comparisonCount (j : ℕ) (P : ℝ) : ℕ := ⌈P ^ priceExponent j⌉₊

/-- Literal real closed interval of actual natural primes. -/
def primesIn (a b : ℝ) : Finset ℕ :=
  (range (⌊b⌋₊ + 1)).filter (fun p => p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b)

/-- UNVERIFIED analytic supplier: consecutive-prime maximum gap, separately typed.
The intervening-prime clause says q is the next prime after p. -/
def BHPMaximumGap : Prop :=
  ∃ A X : ℝ, 0 < A ∧ 2 ≤ X ∧
    ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      (∀ r : ℕ, r.Prime → p < r → q ≤ r) → X ≤ (p : ℝ) →
      (q : ℝ) - p ≤ A * (p : ℝ) ^ bhpExponent

/-- UNVERIFIED analytic supplier: BOTH closed short intervals contain many primes.
This is NOT deduced from BHPMaximumGap.  Removing a prime endpoint later costs 1. -/
def BHPShortIntervalCount : Prop :=
  ∃ C c X : ℝ, 0 < C ∧ 0 < c ∧ 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    c * x ^ bhpExponent / log x ≤
        ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
    c * x ^ bhpExponent / log x ≤
        ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ)

/-- Exact requested localization telescope.  j is fixed BEFORE constants and
threshold; m and its arbitrary positive price follow them.  No e or B occurs. -/
def BoundaryPriceLocalization : Prop :=
  ∀ j : ℕ, 2 ≤ j → ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
    ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      T ≤ (largestPrime m : ℝ) →
      |beta j (layerPrime m j : ℝ) - beta 1 (largestPrime m : ℝ)| ≤
        C * beta 1 (largestPrime m : ℝ) *
          (largestPrime m : ℝ) ^ (-priceExponent j)

/-- The exact goal proposition; its source-level proof is at the end of this file.
Native verification of that proof and its new dependencies is still OPEN. -/
def BHPBoundaryPriceClaim : Prop :=
  BHPMaximumGap → BHPShortIntervalCount → BoundaryPriceLocalization

/- Analytic variation.  These lemmas are consumed by the legal comparison path.
The old `beta_nat` reconciles this real beta exactly with goldenLayerMarginal. -/

private theorem log_two_half : (1 / 2 : ℝ) < log 2 := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
  norm_num at h ⊢
  linarith

private theorem weighted_sum_upper {j : ℕ} {x : ℝ}
    (hx : 0 ≤ x) : x * powerSumDerivative j x ≤ (j : ℝ) * powerSum j x := by
  unfold powerSumDerivative powerSum
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro k hk
  have hkj : ((k + 1 : ℕ) : ℝ) ≤ j := by
    exact_mod_cast (show k + 1 ≤ j from Nat.le_of_lt_succ (by
      have := mem_range.mp hk
      omega))
  calc
    x * (((k : ℝ) + 1) * x ^ k) = ((k + 1 : ℕ) : ℝ) * x ^ (k + 1) := by
      push_cast
      rw [pow_succ]
      ring
    _ ≤ (j : ℝ) * x ^ (k + 1) :=
      mul_le_mul_of_nonneg_right hkj (pow_nonneg hx _)

private theorem slope_bounds {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ logarithmicSlope j x ∧ logarithmicSlope j x ≤ (j : ℝ) + 2 := by
  have hx0 : 0 < x := by linarith
  have hs := powerSum_pos hx0 hj
  have hg := gain_pos hx0 hj
  have hd : 0 ≤ powerSumDerivative j x := by
    unfold powerSumDerivative
    exact sum_nonneg (fun k _ => mul_nonneg (by positivity) (pow_nonneg hx0.le _))
  let A := x * powerSumDerivative j x / powerSum j x
  let B := (1 / powerSum j x) /
    ((1 + 1 / powerSum j x) * HigherLayerLogSlope.gain j x)
  have hA0 : 0 ≤ A := div_nonneg (mul_nonneg hx0.le hd) hs.le
  have hAj : A ≤ (j : ℝ) := (div_le_iff₀ hs).mpr (weighted_sum_upper hx0.le)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBlow : 1 / powerSum j x ≤
      (1 + 1 / powerSum j x) * HigherLayerLogSlope.gain j x := by
    have h := Real.one_sub_inv_le_log_of_pos
      (by positivity : 0 < 1 + 1 / powerSum j x)
    have he : 1 - (1 + 1 / powerSum j x)⁻¹ =
        (1 / powerSum j x) / (1 + 1 / powerSum j x) := by
      field_simp [hs.ne', (show powerSum j x + 1 ≠ 0 by positivity)]
      ring
    rw [he] at h
    have hh := (div_le_iff₀ (by positivity : 0 < 1 + 1 / powerSum j x)).mp h
    simpa only [HigherLayerLogSlope.gain, mul_comm] using hh
  have hB1 : B ≤ 1 := (div_le_one (by positivity)).mpr hBlow
  have hl : (1 / 2 : ℝ) < log x :=
    log_two_half.trans_le (Real.log_le_log (by norm_num) hx)
  have hli : 0 ≤ 1 / log x := by positivity
  have hli2 : 1 / log x ≤ 2 := (div_le_iff₀ (by linarith : 0 < log x)).mpr (by linarith)
  have hAB : A * B ≤ (j : ℝ) :=
    (mul_le_mul_of_nonneg_left hB1 hA0).trans (by simpa using hAj)
  change 0 ≤ A * B + 1 / log x ∧ A * B + 1 / log x ≤ (j : ℝ) + 2
  exact ⟨add_nonneg (mul_nonneg hA0 hB0) hli, by linarith⟩

private theorem beta_hasDerivAt {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (beta j) (-logarithmicSlope j x * beta j x / x) x := by
  have hx0 : 0 < x := by linarith
  have hs := powerSum_pos hx0 hj
  have hg := gain_pos hx0 hj
  have hl := Real.log_pos (by linarith : 1 < x)
  have hG := ((hasDerivAt_const x (1 : ℝ)).add
    ((hasDerivAt_const x (1 : ℝ)).div (powerSum_hasDerivAt j x) hs.ne')).log
      (by positivity : 1 + 1 / powerSum j x ≠ 0)
  convert hG.div (Real.hasDerivAt_log hx0.ne') hl.ne' using 1
  · rfl
  · simp only [Pi.add_apply, Pi.div_apply, zero_mul, one_mul, zero_sub, zero_add]
    unfold logarithmicSlope beta HigherLayerLogSlope.gain
    field_simp [hx0.ne', hs.ne', hg.ne', hl.ne',
      (show 1 + 1 / powerSum j x ≠ 0 by positivity)]
    <;> ring

/-- An explicit local Lipschitz constant, not an assumed marginal-price band. -/
def priceLip (j : ℕ) (a : ℝ) : ℝ :=
  (((j : ℝ) + 2) * (1 / (a ^ j * log a))) / a

private theorem priceLip_nonneg (j : ℕ) {a : ℝ} (ha : 2 ≤ a) :
    0 ≤ priceLip j a := by
  have ha0 : 0 < a := by linarith
  have hl := Real.log_pos (by linarith : 1 < a)
  unfold priceLip
  positivity

private theorem derivative_bound {j : ℕ} (hj : 1 ≤ j) {a x : ℝ}
    (ha : 2 ≤ a) (hax : a ≤ x) :
    | -logarithmicSlope j x * beta j x / x | ≤ priceLip j a := by
  have hx : 2 ≤ x := ha.trans hax
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have hla := Real.log_pos (by linarith : 1 < a)
  have hlx := Real.log_pos (by linarith : 1 < x)
  obtain ⟨hS0, hS⟩ := slope_bounds hj hx
  have hb := beta_pos hx hj
  have hp : a ^ j ≤ x ^ j := pow_le_pow_left₀ ha0.le hax j
  have hl : log a ≤ log x := Real.log_le_log ha0 hax
  have hden : a ^ j * log a ≤ x ^ j * log x :=
    mul_le_mul hp hl hla.le (pow_pos hx0 j).le
  have hbeta : beta j x ≤ 1 / (a ^ j * log a) :=
    (beta_le_inv_pow_log hx hj).trans
      (one_div_le_one_div_of_le (mul_pos (pow_pos ha0 j) hla) hden)
  have hnum : logarithmicSlope j x * beta j x ≤
      ((j : ℝ) + 2) * (1 / (a ^ j * log a)) :=
    mul_le_mul hS hbeta hb.le (by positivity)
  have habs : | -logarithmicSlope j x * beta j x / x | =
      logarithmicSlope j x * beta j x / x := by
    rw [neg_mul, neg_div, abs_neg, abs_of_nonneg (by positivity)]
  rw [habs]
  exact (div_le_div_of_nonneg_right hnum hx0.le).trans
    (div_le_div_of_nonneg_left (by positivity) ha0 hax)

theorem price_variation {j : ℕ} (hj : 1 ≤ j) {a x y : ℝ}
    (ha : 2 ≤ a) (hx : a ≤ x) (hy : a ≤ y) :
    |beta j y - beta j x| ≤ priceLip j a * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := beta j) (f' := fun t => -logarithmicSlope j t * beta j t / t)
    (C := priceLip j a)
    (fun t ht => (beta_hasDerivAt hj (ha.trans ht)).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using derivative_bound hj ha ht)
    (convex_Ici a) hx hy
  simpa only [Real.norm_eq_abs] using h

/- Strict mass crossing: equality is never mistaken for a strict predecessor.
These are subset constructors; no new integer/product legality proof is made. -/

private theorem subset_just_above {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α → ℝ) {t H : ℝ} (ht : 0 ≤ t) (hH : ∀ a ∈ S, f a ≤ H)
    (htotal : t < ∑ a ∈ S, f a) :
    ∃ D ⊆ S, t < ∑ a ∈ D, f a ∧ (∑ a ∈ D, f a) ≤ t + H := by
  revert hH htotal
  induction S using Finset.induction_on with
  | empty =>
    intro hH htotal
    simp only [sum_empty] at htotal
    linarith
  | @insert a S ha ih =>
    intro hH htotal
    by_cases hs : t < ∑ b ∈ S, f b
    · obtain ⟨D, hDS, hlo, hup⟩ := ih
        (fun b hb => hH b (mem_insert_of_mem hb)) hs
      exact ⟨D, hDS.trans (subset_insert _ _), hlo, hup⟩
    · refine ⟨insert a S, subset_rfl, htotal, ?_⟩
      rw [sum_insert ha]
      have := hH a (mem_insert_self _ _)
      linarith

private theorem subset_just_below {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α → ℝ) {t H : ℝ} (ht : 0 < t) (hH : ∀ a ∈ S, f a ≤ H)
    (htotal : t ≤ ∑ a ∈ S, f a) :
    ∃ U ⊆ S, (∑ a ∈ U, f a) < t ∧ t ≤ (∑ a ∈ U, f a) + H := by
  revert hH htotal
  induction S using Finset.induction_on with
  | empty =>
    intro hH htotal
    simp only [sum_empty] at htotal
    linarith
  | @insert a S ha ih =>
    intro hH htotal
    by_cases hs : t ≤ ∑ b ∈ S, f b
    · obtain ⟨U, hUS, hlo, hup⟩ := ih
        (fun b hb => hH b (mem_insert_of_mem hb)) hs
      exact ⟨U, hUS.trans (subset_insert _ _), hlo, hup⟩
    · refine ⟨S, subset_insert _ _, lt_of_not_ge hs, ?_⟩
      rw [sum_insert ha] at htotal
      have := hH a (mem_insert_self _ _)
      linarith

def logMass (S : Finset ℕ) : ℝ := ∑ p ∈ S, log (p : ℝ)

private theorem log_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    log ((∏ p ∈ S, p : ℕ) : ℝ) = logMass S := by
  rw [Nat.cast_prod]
  exact Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).ne_zero)

private theorem product_lt_of_mass_lt {D U : Finset ℕ}
    (hD : ∀ p ∈ D, p.Prime) (hU : ∀ p ∈ U, p.Prime)
    (hmass : logMass U < logMass D) : (∏ p ∈ U, p) < ∏ p ∈ D, p := by
  have hd : (0 : ℝ) < ((∏ p ∈ D, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hD p hp).pos)
  have hu : (0 : ℝ) < ((∏ p ∈ U, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hU p hp).pos)
  have h := (Real.log_lt_log_iff hu hd).mp
    (by simpa only [log_product D hD, log_product U hU] using hmass)
  exact_mod_cast h

private theorem sum_price_lower (S : Finset ℕ) {b : ℝ} (r : ℕ → ℝ)
    (h : ∀ p ∈ S, b ≤ r p) : b * logMass S ≤ ∑ p ∈ S, r p * log p := by
  rw [logMass, mul_sum]
  exact sum_le_sum (fun p hp =>
    mul_le_mul_of_nonneg_right (h p hp) (log_natCast_nonneg p))

private theorem sum_price_upper (S : Finset ℕ) {b : ℝ} (r : ℕ → ℝ)
    (h : ∀ p ∈ S, r p ≤ b) : (∑ p ∈ S, r p * log p) ≤ b * logMass S := by
  rw [logMass, mul_sum]
  exact sum_le_sum (fun p hp =>
    mul_le_mul_of_nonneg_right (h p hp) (log_natCast_nonneg p))

/- A finite signed comparison, retaining every logarithmic mass and price cost.
The certificate below is the existing legal n=(m/productD)*productU proof. -/
private theorem exchange_mass_bound {m : ℕ} {mu lambda h : ℝ}
    (hm : 0 < m) (hrecord : FullRecord m mu)
    (D U : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hU : ∀ p ∈ U, p.Prime)
    (hDvd : ∀ p ∈ D, p ∣ m) (hdis : Disjoint D U)
    (hbalance : logMass U < logMass D)
    (hupper : (∑ p ∈ D, goldenLayerMarginal p (m.factorization p) * log p) ≤
      lambda * logMass D)
    (hlower : h * logMass U ≤
      ∑ p ∈ U, goldenLayerMarginal p (m.factorization p + 1) * log p) :
    h * logMass U < lambda * logMass D - mu * (logMass D - logMass U) := by
  have hc := (signed_exchange_certificate mu hm hrecord D U hD hU hDvd hdis
    (product_lt_of_mass_lt hD hU hbalance)).2.2
  rw [log_product D hD, log_product U hU] at hc
  linarith

/- Uniform coarse geometry is supplied by the EXISTING fixed-layer law.
The two exposed lemmas have their original unchanged proofs. -/
theorem uniform_coarse_geometry (j : ℕ) (hj : 2 ≤ j) :
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      4 ≤ (largestPrime m : ℝ) ∧ 4 ≤ (layerPrime m j : ℝ) ∧
      (layerPrime m j : ℝ) ≤ (largestPrime m : ℝ) / 8 ∧
      (layerPrime m 2 : ℝ) < (largestPrime m : ℝ) / 2 ∧
      log (largestPrime m : ℝ) / (4 * (j : ℝ)) ≤ log ((layerPrime m j : ℝ) / 2) := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let P : S → ℝ := fun x => largestPrime (m x)
  let Q : S → ℝ := fun x => layerPrime (m x) j
  let Q2 : S → ℝ := fun x => layerPrime (m x) 2
  let l : Filter S := comap P atTop
  have hP : Tendsto P l atTop := tendsto_comap
  have hR := record_ratio_limit m mu (fun x => x.2.1) (fun x => x.2.2.1)
    (fun x => x.2.2.2) j hj hP
  obtain ⟨hQ, hlog, hrel⟩ := coarse_scale_limits P Q j hj (fun _ => Nat.cast_nonneg _) hP hR
  have hR2 := record_ratio_limit m mu (fun x => x.2.1) (fun x => x.2.2.1)
    (fun x => x.2.2.2) 2 (by norm_num) hP
  have hrel2 := (coarse_scale_limits P Q2 2 (by norm_num)
    (fun _ => Nat.cast_nonneg _) hP hR2).2.2
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hhalf : 1 / (2 * (j : ℝ)) < (j : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt hj0 (by linarith)
  have he : ∀ᶠ x in l, 4 ≤ P x ∧ 4 ≤ Q x ∧ Q x ≤ P x / 8 ∧ Q2 x < P x / 2 ∧
      log (P x) / (4 * (j : ℝ)) ≤ log (Q x / 2) := by
    filter_upwards [hP.eventually_ge_atTop 4, hQ.eventually_ge_atTop 4,
      hrel.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
      hrel2.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hlog.eventually (eventually_gt_nhds hhalf),
      (Real.tendsto_log_atTop.comp hP).eventually_ge_atTop (4 * (j : ℝ) * log 2)]
      with x hp hq hqp hq2p hl hL
    have hp0 : 0 < P x := by linarith
    have hLp : 0 < log (P x) := Real.log_pos (by linarith)
    have hqp' := (div_lt_iff₀ hp0).mp hqp
    have hq2p' := (div_lt_iff₀ hp0).mp hq2p
    have hl' := (lt_div_iff₀ hLp).mp hl
    refine ⟨hp, hq, by linarith, by linarith, ?_⟩
    rw [Real.log_div (by linarith : Q x ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (j : ℝ))).mpr
    have hl'' : log (P x) / 2 < log (Q x) * (j : ℝ) := by
      have heq : 1 / (2 * (j : ℝ)) * log (P x) = (log (P x) / 2) / (j : ℝ) := by ring
      rw [heq] at hl'
      exact (div_lt_iff₀ hj0).mp hl'
    nlinarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp he)
  refine ⟨max T 4, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn nu hnu hrec hlarge
  let x : S := ⟨(n, nu), hn, hnu, hrec⟩
  exact hT (largestPrime n : ℝ) ((le_max_left T 4).trans hlarge) x rfl

private theorem mass_between (S : Finset ℕ) {a b : ℝ} (ha : 0 < a)
    (hS : ∀ p ∈ S, a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (S.card : ℝ) * log a ≤ logMass S ∧ logMass S ≤ (S.card : ℝ) * log b := by
  constructor
  · calc
      _ = ∑ _p ∈ S, log a := by simp
      _ ≤ _ := sum_le_sum (fun p hp => Real.log_le_log ha (hS p hp).1)
  · calc
      _ ≤ ∑ _p ∈ S, log b := by
        apply sum_le_sum
        intro p hp
        exact Real.log_le_log (ha.trans_le (hS p hp).1) (hS p hp).2
      _ = _ := by simp

/- Only scalar bookkeeping; consumed immediately by the actual-record theorem.
F is the removed first mass, G is the inserted first mass, M/N are the two
higher-layer masses.  H bounds BOTH strict overshoots. -/
private theorem two_cost_bound {mu lambda h ej e1 H A M N F G : ℝ}
    (hmu : 0 < mu) (hlambda : 0 ≤ lambda) (hej : 0 ≤ ej) (he1 : 0 ≤ e1)
    (hH : 0 ≤ H) (hA : 0 < A) (hAM : A ≤ M) (hAN : A ≤ N)
    (hMF : M < F) (hFM : F ≤ M + H)
    (hGN : G < N) (hNG : N ≤ G + H)
    (hplus : (h - ej) * M < (lambda + e1) * F - mu * (F - M))
    (hminus : (lambda - e1) * G < (h + ej) * N - mu * (N - G)) :
    |h - lambda| ≤ ej + e1 + (lambda + e1) * H / A := by
  let R := (lambda + e1) * H / A
  have hR : 0 ≤ R := div_nonneg (mul_nonneg (by linarith) hH) hA.le
  have hRA : R * A = (lambda + e1) * H := div_mul_cancel₀ _ hA.ne'
  have hRM := mul_le_mul_of_nonneg_left hAM hR
  have hRN := mul_le_mul_of_nonneg_left hAN hR
  have hF := mul_le_mul_of_nonneg_left hFM (show 0 ≤ lambda + e1 by linarith)
  have hG := mul_le_mul_of_nonneg_left hGN.le he1
  have hgap := mul_le_mul_of_nonneg_left (show N - G ≤ H by linarith) hlambda
  have hmuF := mul_nonneg hmu.le (show 0 ≤ F - M by linarith)
  have hmuN := mul_nonneg hmu.le (show 0 ≤ N - G by linarith)
  have hlow : - (ej + e1 + R) ≤ h - lambda := by
    have hh : (lambda - h) * N ≤ (ej + e1 + R) * N := by
      nlinarith [mul_nonneg he1 hH]
    have := (mul_le_mul_right (hA.trans_le hAN)).mp hh
    linarith
  have hupp : h - lambda ≤ ej + e1 + R := by
    have hh : (h - lambda) * M ≤ (ej + e1 + R) * M := by nlinarith
    exact (mul_le_mul_right (hA.trans_le hAM)).mp hh
  exact abs_le.mpr ⟨hlow, hupp⟩

/-- Substantive finite actual-record restriction.  Its coordinate pools are NOT
assumed localized in PRICE: the analytic bound above computes all price errors.

The natural count is exactly ceil(P^(19/(40*j))).  The two first-layer subsets
are constructed with strict mass inequalities, including equality cases of the
unselected full pools.  The signed certificate supplies the two legal integers.
No theta power estimate, canonical inventory, variable layer, e, B, or bank
claim enters this statement.  The final BHP-only assembly below constructs all
four coordinate pools uniformly and normalizes this literal RHS.
-/
private theorem actual_boundary_price_from_pools (j : ℕ) (hj : 2 ≤ j) :
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      let P : ℝ := largestPrime m
      let Q : ℝ := layerPrime m j
      let K : ℕ := comparisonCount j P
      ∀ w v : ℝ, 0 ≤ w → w ≤ Q / 2 → 0 ≤ v → v ≤ P / 2 →
      ∀ Lo Hi FirstLo FirstHi : Finset ℕ,
      Lo.card = K → Hi.card = K → FirstLo.card = K → FirstHi.card = K →
      (∀ p ∈ Lo, p.Prime ∧ Q - w ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧
        layerPrime m (j + 1) < p) →
      (∀ p ∈ Hi, p.Prime ∧ Q < (p : ℝ) ∧ (p : ℝ) ≤ Q + w ∧
        p ≤ layerPrime m (j - 1)) →
      (∀ p ∈ FirstLo, p.Prime ∧ P - v ≤ (p : ℝ) ∧ (p : ℝ) ≤ P) →
      (∀ p ∈ FirstHi, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ P + v) →
      |beta j Q - beta 1 P| ≤
        priceLip j (Q / 2) * w + priceLip 1 (P / 2) * v +
          (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) := by
  obtain ⟨T, hT, hgeom⟩ := uniform_coarse_geometry j hj
  refine ⟨T, hT, ?_⟩
  intro m hm mu hmu hrecord hlarge
  dsimp only
  let P : ℝ := largestPrime m
  let Q : ℝ := layerPrime m j
  let K : ℕ := comparisonCount j P
  obtain ⟨hP4, hQ4, hQP, hQ2P, hlogQ⟩ := hgeom m hm mu hmu hrecord hlarge
  change 4 ≤ P at hP4
  change 4 ≤ Q at hQ4
  change Q ≤ P / 8 at hQP
  change (layerPrime m 2 : ℝ) < P / 2 at hQ2P
  change log P / (4 * (j : ℝ)) ≤ log (Q / 2) at hlogQ
  intro w v hw hwQ hv hvP Lo Hi FirstLo FirstHi hLoc hHic hFLc hFUc hLo hHi hFL hFU
  have hm0 : 0 < m := by omega
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hLP : 0 < log P := Real.log_pos (by linarith)
  have hj1 : 1 ≤ j := by omega
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hKnat : 0 < K := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hP0 _)
  have hK : 0 < (K : ℝ) := by exact_mod_cast hKnat
  have haP : 2 ≤ P / 2 := by linarith
  have haQ : 2 ≤ Q / 2 := by linarith
  obtain ⟨hanti, hsupport⟩ := price_record_prime_structure hm hmu hrecord
  let lambda := beta 1 P
  let h := beta j Q
  let ej := priceLip j (Q / 2) * w
  let e1 := priceLip 1 (P / 2) * v
  let H := 2 * log P
  let A := (K : ℝ) * (log P / (4 * (j : ℝ)))
  have hlam : 0 < lambda := beta_pos (by linarith) (by norm_num)
  have hej : 0 ≤ ej := mul_nonneg (priceLip_nonneg j haQ) hw
  have he1 : 0 ≤ e1 := mul_nonneg (priceLip_nonneg 1 haP) hv
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hLoBox : ∀ p ∈ Lo, Q / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Q := by
    intro p hp
    have hh := hLo p hp
    constructor <;> linarith [hh.2.1, hh.2.2.1]
  have hHiBox : ∀ p ∈ Hi, Q / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Q := by
    intro p hp
    have hh := hHi p hp
    constructor <;> linarith [hh.2.1, hh.2.2.1]
  have hFLBox : ∀ p ∈ FirstLo, P / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
    intro p hp
    have hh := hFL p hp
    constructor <;> linarith [hh.2.1, hh.2.2]
  have hFUBox : ∀ p ∈ FirstHi, P / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
    intro p hp
    have hh := hFU p hp
    constructor <;> linarith [hh.2.1, hh.2.2]
  have hLoMass := mass_between Lo (by linarith : 0 < Q / 2) hLoBox
  have hHiMass := mass_between Hi (by linarith : 0 < Q / 2) hHiBox
  have hFLMass := mass_between FirstLo (by linarith : 0 < P / 2) hFLBox
  have hFUMass := mass_between FirstHi (by linarith : 0 < P / 2) hFUBox
  rw [hLoc] at hLoMass
  rw [hHic] at hHiMass
  rw [hFLc] at hFLMass
  rw [hFUc] at hFUMass
  have hAM : A ≤ logMass Hi :=
    (mul_le_mul_of_nonneg_left hlogQ hK.le).trans hHiMass.1
  have hAN : A ≤ logMass Lo :=
    (mul_le_mul_of_nonneg_left hlogQ hK.le).trans hLoMass.1
  have hlogsep : log (2 * Q) < log (P / 2) :=
    Real.log_lt_log (by positivity) (by linarith)
  have hcapacityHi : logMass Hi < logMass FirstLo :=
    hHiMass.2.trans_lt ((mul_lt_mul_of_pos_left hlogsep hK).trans_le hFLMass.1)
  have hcapacityLo : logMass Lo < logMass FirstHi :=
    hLoMass.2.trans_lt ((mul_lt_mul_of_pos_left hlogsep hK).trans_le hFUMass.1)
  have hfirstlog : ∀ p : ℕ, (p : ℝ) ≤ 2 * P → log (p : ℝ) ≤ H := by
    intro p hp
    by_cases hz : p = 0
    · subst p
      simpa [H] using hH
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    have hh := Real.log_le_log hp0 hp
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne'] at hh
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ P)
    dsimp [H]
    linarith
  obtain ⟨D, hDFL, hMD, hDM⟩ := subset_just_above FirstLo (fun p => log (p : ℝ))
    (t := logMass Hi) (H := H) (hA.le.trans hAM)
    (fun p hp => hfirstlog p (hFLBox p hp).2) hcapacityHi
  obtain ⟨U, hUFU, hUN, hNU⟩ := subset_just_below FirstHi (fun p => log (p : ℝ))
    (t := logMass Lo) (H := H) (hA.trans_le hAN)
    (fun p hp => hfirstlog p (hFUBox p hp).2) hcapacityLo.le
  change logMass Hi < logMass D at hMD
  change logMass D ≤ logMass Hi + H at hDM
  change logMass U < logMass Lo at hUN
  change logMass Lo ≤ logMass U + H at hNU
  have hLoVal : ∀ p ∈ Lo, m.factorization p = j := by
    intro p hp
    have hh := hLo p hp
    have hlo := valuation_below_layer_prime hh.1 hanti
      (by exact_mod_cast hh.2.2.1 : p ≤ layerPrime m j)
    have hup := valuation_above_layer_prime hm0 (by omega : 1 ≤ j + 1) hh.1 hh.2.2.2
    omega
  have hHiVal : ∀ p ∈ Hi, m.factorization p + 1 = j := by
    intro p hp
    have hh := hHi p hp
    have hlo := valuation_below_layer_prime hh.1 hanti hh.2.2.2
    have hup := valuation_above_layer_prime hm0 hj1 hh.1
      (by exact_mod_cast hh.2.1 : layerPrime m j < p)
    omega
  have hFLVal : ∀ p ∈ FirstLo, m.factorization p = 1 := by
    intro p hp
    have hh := hFL p hp
    have hmem : p ∈ m.primeFactors := by
      rw [hsupport]
      exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hh.2.2, hh.1⟩
    have hlo := hh.1.factorization_pos_of_dvd hm0.ne' (Nat.dvd_of_mem_primeFactors hmem)
    have hup := valuation_above_layer_prime hm0 (by norm_num : 1 ≤ 2) hh.1
      (by exact_mod_cast (hQ2P.trans_le (hFLBox p hp).1))
    omega
  have hFUVal : ∀ p ∈ FirstHi, m.factorization p = 0 := by
    intro p hp
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hmem : p ∈ m.primeFactors := (hFU p hp).1.mem_primeFactors hd hm0.ne'
    rw [hsupport] at hmem
    have hle : (p : ℝ) ≤ P := by exact_mod_cast (Nat.mem_primesLE.mp hmem).1
    linarith [(hFU p hp).2.1]
  have hHigherPrice (S : Finset ℕ) (hS : ∀ p ∈ S,
      p.Prime ∧ Q - w ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q + w) :
      ∀ p ∈ S, |beta j (p : ℝ) - h| ≤ ej := by
    intro p hp
    have hpQ : Q / 2 ≤ (p : ℝ) := by linarith [(hS p hp).2.1]
    have hpdist : |(p : ℝ) - Q| ≤ w := abs_le.mpr ⟨by linarith [(hS p hp).2.1],
      by linarith [(hS p hp).2.2]⟩
    exact (price_variation hj1 haQ (by linarith : Q / 2 ≤ Q) hpQ).trans
      (mul_le_mul_of_nonneg_left hpdist (priceLip_nonneg j haQ))
  have hLoPrice := hHigherPrice Lo (fun p hp => ⟨(hLo p hp).1,
    (hLo p hp).2.1, by linarith [(hLo p hp).2.2.1]⟩)
  have hHiPrice := hHigherPrice Hi (fun p hp => ⟨(hHi p hp).1,
    by linarith [(hHi p hp).2.1], (hHi p hp).2.2.1⟩)
  have hFirstPrice (S : Finset ℕ) (hS : ∀ p ∈ S,
      P - v ≤ (p : ℝ) ∧ (p : ℝ) ≤ P + v) :
      ∀ p ∈ S, |beta 1 (p : ℝ) - lambda| ≤ e1 := by
    intro p hp
    have hpP : P / 2 ≤ (p : ℝ) := by linarith [(hS p hp).1]
    have hpdist : |(p : ℝ) - P| ≤ v := abs_le.mpr ⟨by linarith [(hS p hp).1],
      by linarith [(hS p hp).2]⟩
    exact (price_variation (by norm_num : 1 ≤ 1) haP (by linarith : P / 2 ≤ P) hpP).trans
      (mul_le_mul_of_nonneg_left hpdist (priceLip_nonneg 1 haP))
  have hFLPrice := hFirstPrice FirstLo (fun p hp => ⟨(hFL p hp).2.1,
    by linarith [(hFL p hp).2.2]⟩)
  have hFUPrice := hFirstPrice FirstHi (fun p hp => ⟨by linarith [(hFU p hp).2.1],
    (hFU p hp).2.2⟩)
  have hDprime : ∀ p ∈ D, p.Prime := fun p hp => (hFL p (hDFL hp)).1
  have hUprime : ∀ p ∈ U, p.Prime := fun p hp => (hFU p (hUFU hp)).1
  have hLoprime : ∀ p ∈ Lo, p.Prime := fun p hp => (hLo p hp).1
  have hHiprime : ∀ p ∈ Hi, p.Prime := fun p hp => (hHi p hp).1
  have hDdvd : ∀ p ∈ D, p ∣ m := by
    intro p hp
    apply ((hDprime p hp).dvd_iff_one_le_factorization hm0.ne').mpr
    simpa only [hFLVal p (hDFL hp)] using (le_refl (1 : ℕ))
  have hLodvd : ∀ p ∈ Lo, p ∣ m := by
    intro p hp
    apply ((hLoprime p hp).dvd_iff_one_le_factorization hm0.ne').mpr
    rw [hLoVal p hp]
    exact hj1
  have hdisPlus : Disjoint D Hi := by
    apply disjoint_left.mpr
    intro p hpD hpHi
    have hlo := (hFLBox p (hDFL hpD)).1
    have hhi := (hHiBox p hpHi).2
    linarith
  have hdisMinus : Disjoint Lo U := by
    apply disjoint_left.mpr
    intro p hpLo hpU
    have hlo := (hFUBox p (hUFU hpU)).1
    have hhi := (hLoBox p hpLo).2
    linarith
  have hplus : (h - ej) * logMass Hi <
      (lambda + e1) * logMass D - mu * (logMass D - logMass Hi) := by
    apply exchange_mass_bound hm0 hrecord D Hi hDprime hHiprime hDdvd hdisPlus hMD
    · apply sum_price_upper D (fun p => goldenLayerMarginal p (m.factorization p))
      intro p hp
      rw [hFLVal p (hDFL hp), ← beta_nat (hDprime p hp) (by norm_num : 1 ≤ 1)]
      have hh := (abs_le.mp (hFLPrice p (hDFL hp))).2
      linarith
    · apply sum_price_lower Hi (fun p => goldenLayerMarginal p (m.factorization p + 1))
      intro p hp
      rw [hHiVal p hp, ← beta_nat (hHiprime p hp) hj1]
      have hh := (abs_le.mp (hHiPrice p hp)).1
      linarith
  have hminus : (lambda - e1) * logMass U <
      (h + ej) * logMass Lo - mu * (logMass Lo - logMass U) := by
    apply exchange_mass_bound hm0 hrecord Lo U hLoprime hUprime hLodvd hdisMinus hUN
    · apply sum_price_upper Lo (fun p => goldenLayerMarginal p (m.factorization p))
      intro p hp
      rw [hLoVal p hp, ← beta_nat (hLoprime p hp) hj1]
      have hh := (abs_le.mp (hLoPrice p hp)).2
      linarith
    · apply sum_price_lower U (fun p => goldenLayerMarginal p (m.factorization p + 1))
      intro p hp
      rw [hFUVal p (hUFU hp)]
      norm_num only [zero_add]
      rw [← beta_nat (hUprime p hp) (by norm_num : 1 ≤ 1)]
      have hh := (abs_le.mp (hFUPrice p (hUFU hp))).1
      linarith
  have hband := two_cost_bound hmu hlam.le hej he1 hH hA hAM hAN
    hMD hDM hUN hNU hplus hminus
  have hnormalize : (lambda + e1) * H / A =
      (8 * (j : ℝ) / (K : ℝ)) * (lambda + e1) := by
    dsimp [H, A]
    field_simp [hK.ne', hLP.ne', hj0.ne']
    <;> ring
  rw [hnormalize] at hband
  exact hband

theorem counted_higher_pools {N K : ℕ} {C c X : ℝ}
    (hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤ ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤ ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ))
    (hXN : X ≤ (N : ℝ))
    (hcapacity : (K : ℝ) + 1 ≤ c * (N : ℝ) ^ bhpExponent / log N) :
    ∃ Lo Hi : Finset ℕ, Lo.card = K ∧ Hi.card = K ∧
      (∀ p ∈ Lo, p.Prime ∧ (N : ℝ) - C * (N : ℝ) ^ bhpExponent ≤ p ∧ (p : ℝ) ≤ N) ∧
      (∀ p ∈ Hi, p.Prime ∧ (N : ℝ) < p ∧ (p : ℝ) ≤ (N : ℝ) + C * (N : ℝ) ^ bhpExponent) := by
  classical
  let S := primesIn ((N : ℝ) - C * (N : ℝ) ^ bhpExponent) N
  let V := primesIn N ((N : ℝ) + C * (N : ℝ) ^ bhpExponent)
  have hS : K ≤ S.card := by
    have hh := hcapacity.trans (hcount N hXN).1
    have hh' : (K : ℝ) ≤ S.card := by dsimp [S]; linarith
    exact_mod_cast hh'
  have hV : K + 1 ≤ V.card := by
    have hh := hcapacity.trans (hcount N hXN).2
    exact_mod_cast hh
  have hVe : K ≤ (V.erase N).card := by
    have hh : V.card - 1 ≤ (V.erase N).card := pred_card_le_card_erase
    omega
  obtain ⟨Lo, hLoS, hLoc⟩ := exists_subset_card_eq hS
  obtain ⟨Hi, hHiV, hHic⟩ := exists_subset_card_eq hVe
  refine ⟨Lo, Hi, hLoc, hHic, ?_, ?_⟩
  · intro p hp
    exact (mem_filter.mp (hLoS hp)).2
  · intro p hp
    have he := mem_erase.mp (hHiV hp)
    have hh := (mem_filter.mp he.2).2
    refine ⟨hh.1, ?_, hh.2.2⟩
    have hne : (p : ℝ) ≠ N := by exact_mod_cast he.1
    exact lt_of_le_of_ne hh.2.1 (Ne.symm hne)

/-- The short-interval COUNT supplier is genuinely consumed: both higher pools
are selected here, the upper endpoint prime is removed at a literal cost of one,
and the old actual-layer lemmas give the exact exponents inside the comparison.

This is an intermediate result.  The scalar capacity, adjacent-cutoff separation,
small widths and first-prime pools are explicit intermediate premises here.
None of those is a price-localization hypothesis.  BoundaryPriceLocalization
follows only in the final BHP-only source assembly below.
-/
private theorem actual_boundary_price_from_count_and_first_pools (j : ℕ) (hj : 2 ≤ j) :
    ∃ T : ℝ, 0 < T ∧ ∀ C c X : ℝ, 0 < C → 0 < c → 2 ≤ X →
      (∀ x : ℝ, X ≤ x →
        c * x ^ bhpExponent / log x ≤ ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
        c * x ^ bhpExponent / log x ≤ ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ)) →
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      T ≤ (largestPrime m : ℝ) →
      let P : ℝ := largestPrime m
      let Q : ℝ := layerPrime m j
      let K : ℕ := comparisonCount j P
      let w : ℝ := C * Q ^ bhpExponent
      X ≤ Q → (K : ℝ) + 1 ≤ c * Q ^ bhpExponent / log Q →
      w ≤ Q / 2 → (layerPrime m (j + 1) : ℝ) < Q - w →
      Q + w ≤ (layerPrime m (j - 1) : ℝ) →
      ∀ v : ℝ, 0 ≤ v → v ≤ P / 2 → ∀ FirstLo FirstHi : Finset ℕ,
      FirstLo.card = K → FirstHi.card = K →
      (∀ p ∈ FirstLo, p.Prime ∧ P - v ≤ (p : ℝ) ∧ (p : ℝ) ≤ P) →
      (∀ p ∈ FirstHi, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ P + v) →
      |beta j Q - beta 1 P| ≤
        priceLip j (Q / 2) * w + priceLip 1 (P / 2) * v +
          (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) := by
  obtain ⟨T, hT, hfinite⟩ := actual_boundary_price_from_pools j hj
  refine ⟨T, hT, ?_⟩
  intro C c X hC hc hX hcount m hm mu hmu hrecord hlarge
  dsimp only
  intro hXQ hcapacity hwidth hbelow habove v hv hvP FirstLo FirstHi hFLc hFUc hFL hFU
  obtain ⟨Lo, Hi, hLoc, hHic, hLo, hHi⟩ := counted_higher_pools hcount hXQ hcapacity
  have hw : 0 ≤ C * (layerPrime m j : ℝ) ^ bhpExponent :=
    mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply hfinite m hm mu hmu hrecord hlarge _ v hw hwidth hv hvP
    Lo Hi FirstLo FirstHi hLoc hHic hFLc hFUc
  · intro p hp
    have hh := hLo p hp
    refine ⟨hh.1, hh.2.1, hh.2.2, ?_⟩
    exact_mod_cast (hbelow.trans_le hh.2.1)
  · intro p hp
    have hh := hHi p hp
    refine ⟨hh.1, hh.2.1, hh.2.2, ?_⟩
    exact_mod_cast (hh.2.2.trans habove)
  · exact hFL
  · exact hFU

/- Direct count route at the first boundary.  These are the only first-pool
constructors retained.  The same two-sided count is used at P here and at the
actual higher boundary Q in `actual_boundary_price_from_count_and_first_pools`.
All numerical thresholds precede the original full record and its price. -/
private theorem priceExponent_pos {j : ℕ} (hj : 2 ≤ j) : 0 < priceExponent j := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  unfold priceExponent
  positivity

private theorem priceExponent_le {j : ℕ} (hj : 2 ≤ j) : priceExponent j ≤ 19 / 80 := by
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  unfold priceExponent
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 40 * j) (by norm_num)).mpr
  nlinarith

private theorem count_bounds {j : ℕ} (hj : 2 ≤ j) {P : ℝ} (hP : 1 ≤ P) :
    P ^ priceExponent j ≤ (comparisonCount j P : ℝ) ∧
      (comparisonCount j P : ℝ) ≤ 2 * P ^ priceExponent j := by
  have hp : 0 ≤ P ^ priceExponent j := Real.rpow_nonneg (by linarith) _
  have hp1 : 1 ≤ P ^ priceExponent j := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hP
      (priceExponent_pos hj).le
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one hp).le.trans (by linarith)⟩

/-- Consumed numerical helper. The logarithmic capacity follows directly from
the PINNED `_root_.isLittleO_log_rpow_atTop`, with positive exponent theta-gamma.
The radius bound uses the PINNED `tendsto_rpow_neg_atTop` at 19/40. -/
private theorem uniform_first_count_capacity_and_radius (j : ℕ) (hj : 2 ≤ j)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ P : ℝ, T ≤ P →
      4 ≤ P ∧ X ≤ P ∧
      0 ≤ C * P ^ bhpExponent ∧ C * P ^ bhpExponent ≤ P / 2 ∧
      (comparisonCount j P : ℝ) + 1 ≤ c * P ^ bhpExponent / log P := by
  have hgamma := priceExponent_pos hj
  have hdiff : 0 < bhpExponent - priceExponent j := by
    have hle := priceExponent_le hj
    norm_num [bhpExponent] at *
    linarith
  have hlog : Tendsto (fun P : ℝ => log P / P ^ (bhpExponent - priceExponent j))
      atTop (𝓝 0) :=
    (_root_.isLittleO_log_rpow_atTop hdiff).tendsto_div_nhds_zero
  have hsmall : Tendsto (fun P : ℝ => C * P ^ (-(19 / 40 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 19 / 40)).const_mul C
  have hevent : ∀ᶠ P : ℝ in atTop,
      4 ≤ P ∧ X ≤ P ∧
      0 ≤ C * P ^ bhpExponent ∧ C * P ^ bhpExponent ≤ P / 2 ∧
      (comparisonCount j P : ℝ) + 1 ≤ c * P ^ bhpExponent / log P := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop X,
      hlog.eventually (eventually_lt_nhds (show (0 : ℝ) < c / 3 by positivity)),
      hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with P hP hXP htail hrad
    have hP0 : 0 < P := by linarith
    have hlogP : 0 < log P := Real.log_pos (by linarith : 1 < P)
    have hpow0 : 0 < P ^ priceExponent j := Real.rpow_pos_of_pos hP0 _
    have hpow1 : 1 ≤ P ^ priceExponent j := by
      calc
        1 = P ^ (0 : ℝ) := (Real.rpow_zero P).symm
        _ ≤ P ^ priceExponent j :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hgamma.le
    have hceil : (comparisonCount j P : ℝ) < P ^ priceExponent j + 1 := by
      exact Nat.ceil_lt_add_one hpow0.le
    have hK : (comparisonCount j P : ℝ) + 1 ≤ 3 * P ^ priceExponent j := by
      linarith
    have htail' : log P ≤ (c / 3) * P ^ (bhpExponent - priceExponent j) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hP0 _)).mp htail.le
    have hproduct : P ^ priceExponent j * P ^ (bhpExponent - priceExponent j) =
        P ^ bhpExponent := by
      rw [← Real.rpow_add hP0]
      congr 1
      ring
    have hcapacity : 3 * P ^ priceExponent j ≤ c * P ^ bhpExponent / log P := by
      apply (le_div_iff₀ hlogP).mpr
      calc
        3 * P ^ priceExponent j * log P = 3 * (P ^ priceExponent j * log P) := by ring
        _ ≤ 3 * (P ^ priceExponent j *
            ((c / 3) * P ^ (bhpExponent - priceExponent j))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htail' hpow0.le) (by norm_num)
        _ = c * (P ^ priceExponent j * P ^ (bhpExponent - priceExponent j)) := by ring
        _ = c * P ^ bhpExponent := by rw [hproduct]
    have hradius : C * P ^ bhpExponent / P ≤ (1 / 2 : ℝ) := by
      have he : bhpExponent - 1 = -(19 / 40 : ℝ) := by norm_num [bhpExponent]
      rw [mul_div_assoc, ← Real.rpow_sub_one hP0.ne', he]
      exact hrad.le
    exact ⟨hP, hXP, mul_nonneg hC.le (Real.rpow_nonneg hP0.le _),
      by linarith [(div_le_iff₀ hP0).mp hradius], hK.trans hcapacity⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨max 4 T, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left _ _), ?_⟩
  intro P hP
  exact hT P ((le_max_right _ _).trans hP)

/-- Reusable, consumed count-to-first-pools helper. `hcount` is exactly the
witness telescope of the EXISTING `BHPShortIntervalCount`, at every real x.
It is used at x=P. The existing subset-card proof `counted_higher_pools`
erases P from the upper CLOSED interval, paying at most one prime. No
primality assumption on the natural centre P is needed, so this also applies
to the actual prime `largestPrime m`. Constants precede P, m and mu. -/
theorem uniform_counted_first_pools (j : ℕ) (hj : 2 ≤ j)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤
        ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤
        ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ)) :
    ∃ T : ℝ, 0 < T ∧ ∀ P : ℕ, T ≤ (P : ℝ) →
      4 ≤ (P : ℝ) ∧
      0 ≤ C * (P : ℝ) ^ bhpExponent ∧
      C * (P : ℝ) ^ bhpExponent ≤ (P : ℝ) / 2 ∧
      ∃ FirstLo FirstHi : Finset ℕ,
        FirstLo.card = comparisonCount j P ∧ FirstHi.card = comparisonCount j P ∧
        (∀ p ∈ FirstLo, p.Prime ∧
          (P : ℝ) - C * (P : ℝ) ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ P) ∧
        (∀ p ∈ FirstHi, p.Prime ∧
          (P : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (P : ℝ) + C * (P : ℝ) ^ bhpExponent) := by
  obtain ⟨T, hT, hscalar⟩ := uniform_first_count_capacity_and_radius j hj C c X hC hc
  refine ⟨T, hT, ?_⟩
  intro P hP
  obtain ⟨hP4, hXP, hv, hvP, hcapacity⟩ := hscalar P hP
  obtain ⟨FirstLo, FirstHi, hLo, hHi, hLoP, hHiP⟩ :=
    counted_higher_pools hcount hXP hcapacity
  exact ⟨hP4, hv, hvP, FirstLo, FirstHi, hLo, hHi, hLoP, hHiP⟩

private theorem largestPrime_prime {m : ℕ} (hm : 2 ≤ m) : (largestPrime m).Prime := by
  classical
  obtain ⟨p, hp, he⟩ := exists_mem_eq_sup m.primeFactors
    (Nat.nonempty_primeFactors.mpr (by omega)) id
  have hP : largestPrime m = p := he
  rw [hP]
  exact Nat.prime_of_mem_primeFactors hp

private theorem layerPrime_one {m : ℕ} (hm : 2 ≤ m) :
    layerPrime m 1 = largestPrime m := by
  classical
  have hf : m.primeFactors.filter (fun p => 1 ≤ m.factorization p) = m.primeFactors := by
    apply filter_eq_self.mpr
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd (by omega)
      (Nat.dvd_of_mem_primeFactors hp)
  unfold layerPrime
  rw [hf]
  exact max_eq_right (largestPrime_prime hm).one_lt.le

/- The following three analytic lemmas use only the frozen fixed-layer ratio.
Their filters need not be nontrivial: uniform thresholds are recovered on the
space of ALL records, not along a selected family of records. -/
private theorem layer_scale_limit {α : Type*} {l : Filter α}
    (P Q : α → ℝ) (j : ℕ) (hj : 2 ≤ j) (hQ : ∀ x, 0 ≤ Q x)
    (hP : Tendsto P l atTop)
    (hR : Tendsto (fun x => Q x ^ j / P x) l (𝓝 (j : ℝ))) :
    Tendsto (fun x => Q x / P x ^ ((j : ℝ)⁻¹))
      l (𝓝 ((j : ℝ) ^ ((j : ℝ)⁻¹))) := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hh := hR.rpow_const (p := (j : ℝ)⁻¹) (Or.inl hj0.ne')
  apply hh.congr'
  filter_upwards [hP.eventually_gt_atTop 0] with x hx
  rw [Real.div_rpow (pow_nonneg (hQ x) _) hx.le]
  rw [Real.pow_rpow_inv_natCast (hQ x) (by omega : j ≠ 0)]

private theorem separated_scale_limit {α : Type*} {l : Filter α}
    (P U V : α → ℝ) {a b c d : ℝ} (hab : a < b) (hd : d ≠ 0)
    (hP : Tendsto P l atTop)
    (hU : Tendsto (fun x => U x / P x ^ a) l (𝓝 c))
    (hV : Tendsto (fun x => V x / P x ^ b) l (𝓝 d)) :
    Tendsto (fun x => U x / V x) l (𝓝 0) := by
  have hz : Tendsto (fun x => P x ^ (a - b)) l (𝓝 0) := by
    have he : -(b - a) = a - b := by ring
    simpa only [Function.comp_def, he] using
      (_root_.tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp hP
  have hh := (hU.div hV hd).mul hz
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hP.eventually_gt_atTop 0, hV.eventually_ne hd] with x hx hv
  have hv0 : V x ≠ 0 := by
    intro he
    apply hv
    simp [he]
  rw [Real.rpow_sub hx]
  field_simp [hv0, (Real.rpow_pos_of_pos hx a).ne', (Real.rpow_pos_of_pos hx b).ne']
  <;> ring

private theorem count_capacity_limit {α : Type*} {l : Filter α}
    (P Q : α → ℝ) (j : ℕ) (hj : 2 ≤ j) (hQnonneg : ∀ x, 0 ≤ Q x)
    (hP : Tendsto P l atTop)
    (hR : Tendsto (fun x => Q x ^ j / P x) l (𝓝 (j : ℝ))) :
    Tendsto (fun x => P x ^ priceExponent j * log (Q x) / Q x ^ bhpExponent)
      l (𝓝 0) := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  let a : ℝ := (j : ℝ)⁻¹
  let d : ℝ := a * bhpExponent - priceExponent j
  have hd : 0 < d := by
    have he : d = 1 / (20 * (j : ℝ)) := by
      dsimp [d, a, bhpExponent, priceExponent]
      rw [inv_eq_one_div]
      field_simp [hj0.ne'] <;> ring
    rw [he]
    positivity
  have hscale := layer_scale_limit P Q j hj hQnonneg hP hR
  have hlog := (coarse_scale_limits P Q j hj hQnonneg hP hR).2.1
  have hQ := (coarse_scale_limits P Q j hj hQnonneg hP hR).1
  have hc : (j : ℝ) ^ ((j : ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hj0 _).ne'
  have hc' : ((j : ℝ) ^ ((j : ℝ)⁻¹)) ^ bhpExponent ≠ 0 :=
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hj0 _) _).ne'
  have hz := (_root_.isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero.comp hP
  have hh := (hlog.div (hscale.rpow_const (Or.inl hc)) hc').mul hz
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hP.eventually_gt_atTop 1, hQ.eventually_gt_atTop 1] with x hp hq
  have hp0 : 0 < P x := by linarith
  have hq0 : 0 < Q x := by linarith
  have hpA := Real.rpow_pos_of_pos hp0 a
  have hpD := Real.rpow_pos_of_pos hp0 d
  have hqB := Real.rpow_pos_of_pos hq0 bhpExponent
  have he : (P x ^ a) ^ bhpExponent = P x ^ d * P x ^ priceExponent j := by
    rw [← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
    dsimp [d]
    congr 1 <;> ring
  dsimp [Function.comp_def]
  change (log (Q x) / log (P x)) /
    ((Q x / P x ^ a) ^ bhpExponent) * (log (P x) / P x ^ d) = _
  rw [Real.div_rpow hq0.le hpA.le, he]
  field_simp [hpA.ne', hpD.ne', hqB.ne',
    (Real.rpow_pos_of_pos hp0 (priceExponent j)).ne', (Real.log_pos hp).ne']
  <;> ring

private theorem higher_width_limit {α : Type*} {l : Filter α}
    (Q : α → ℝ) (hQ : Tendsto Q l atTop) (C : ℝ) :
    Tendsto (fun x => C * Q x ^ bhpExponent / Q x) l (𝓝 0) := by
  have hh := ((_root_.tendsto_rpow_neg_atTop
    (by norm_num [bhpExponent] : 0 < 1 - bhpExponent)).comp hQ).const_mul C
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hQ.eventually_gt_atTop 0] with x hx
  have he : -(1 - bhpExponent) = bhpExponent - 1 := by ring
  rw [he, Real.rpow_sub hx, Real.rpow_one]
  ring

/-- M2: actual higher-layer capacity and both adjacent support separations,
uniformly over all original full records.  The j=2 upper support is identified
with the SAME integer's largest prime, by `layerPrime_one` above. -/
theorem uniform_higher_geometry (j : ℕ) (hj : 2 ≤ j)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      let P : ℝ := largestPrime m
      let Q : ℝ := layerPrime m j
      let K : ℕ := comparisonCount j P
      let w : ℝ := C * Q ^ bhpExponent
      X ≤ Q ∧ (K : ℝ) + 1 ≤ c * Q ^ bhpExponent / log Q ∧
        w ≤ Q / 2 ∧ (layerPrime m (j + 1) : ℝ) < Q - w ∧
        Q + w ≤ (layerPrime m (j - 1) : ℝ) ∧ P ≤ Q ^ j := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let P : S → ℝ := fun x => largestPrime (m x)
  let Q : S → ℝ := fun x => layerPrime (m x) j
  let U : S → ℝ := fun x => layerPrime (m x) (j + 1)
  let V : S → ℝ := fun x => layerPrime (m x) (j - 1)
  let l : Filter S := comap P atTop
  have hP : Tendsto P l atTop := tendsto_comap
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hR := record_ratio_limit m mu (fun x => x.2.1) (fun x => x.2.2.1)
    (fun x => x.2.2.2) j hj hP
  have hRU := record_ratio_limit m mu (fun x => x.2.1) (fun x => x.2.2.1)
    (fun x => x.2.2.2) (j + 1) (by omega) hP
  have hQnonneg : ∀ x, 0 ≤ Q x := fun _ => Nat.cast_nonneg _
  have hQ := (coarse_scale_limits P Q j hj hQnonneg hP hR).1
  have hscaleQ := layer_scale_limit P Q j hj hQnonneg hP hR
  have hscaleU := layer_scale_limit P U (j + 1) (by omega)
    (fun _ => Nat.cast_nonneg _) hP hRU
  have hsepU : Tendsto (fun x => U x / Q x) l (𝓝 0) := by
    apply separated_scale_limit P U Q
      (by simpa only [one_div] using
        one_div_lt_one_div_of_lt hj0 (show (j : ℝ) < (j + 1 : ℕ) by push_cast; linarith))
      (Real.rpow_pos_of_pos hj0 _).ne' hP hscaleU hscaleQ
  have hsepV : Tendsto (fun x => Q x / V x) l (𝓝 0) := by
    by_cases he : j = 2
    · subst j
      have hv : V = P := by
        funext x
        exact_mod_cast layerPrime_one x.2.1
      rw [hv]
      exact (coarse_scale_limits P Q 2 (by norm_num) hQnonneg hP hR).2.2
    · have hjm : 2 ≤ j - 1 := by omega
      have hjm0 : 0 < ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < j - 1 by omega)
      have hRV := record_ratio_limit m mu (fun x => x.2.1) (fun x => x.2.2.1)
        (fun x => x.2.2.2) (j - 1) hjm hP
      have hscaleV := layer_scale_limit P V (j - 1) hjm
        (fun _ => Nat.cast_nonneg _) hP hRV
      apply separated_scale_limit P Q V
        (by simpa only [one_div] using one_div_lt_one_div_of_lt hjm0
          (show ((j - 1 : ℕ) : ℝ) < j by exact_mod_cast (show j - 1 < j by omega)))
        (Real.rpow_pos_of_pos hjm0 _).ne' hP hscaleQ hscaleV
  have hwidth := higher_width_limit Q hQ C
  have hcapacity := count_capacity_limit P Q j hj hQnonneg hP hR
  have hbelow : Tendsto (fun x => (U x + C * Q x ^ bhpExponent) / Q x) l (𝓝 0) := by
    simpa only [add_div, add_zero] using hsepU.add hwidth
  have habove : Tendsto (fun x => (Q x + C * Q x ^ bhpExponent) / V x) l (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add hwidth).mul hsepV
    simp only [add_zero, mul_zero] at hh
    apply hh.congr'
    filter_upwards [hQ.eventually_gt_atTop 0] with x hx
    by_cases hv : V x = 0
    · simp [hv]
    · field_simp [hx.ne', hv] <;> ring
  have he : ∀ᶠ x in l,
      X ≤ Q x ∧ ((comparisonCount j (P x) : ℝ) + 1 ≤
        c * Q x ^ bhpExponent / log (Q x)) ∧
      C * Q x ^ bhpExponent ≤ Q x / 2 ∧
      U x < Q x - C * Q x ^ bhpExponent ∧
      Q x + C * Q x ^ bhpExponent ≤ V x ∧ P x ≤ Q x ^ j := by
    filter_upwards [hQ.eventually_ge_atTop X, hQ.eventually_gt_atTop 1,
      hP.eventually_ge_atTop 1,
      hwidth.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hcapacity.eventually (eventually_lt_nhds (show (0 : ℝ) < c / 3 by positivity)),
      hbelow.eventually (eventually_lt_nhds zero_lt_one),
      habove.eventually (eventually_lt_nhds zero_lt_one),
      hR.eventually (eventually_gt_nhds hj1)] with x hx hq hp hw hcapa hlo hup hratio
    have hq0 : 0 < Q x := by linarith
    have hp0 : 0 < P x := by linarith
    have hlq : 0 < log (Q x) := Real.log_pos hq
    have hpB : 0 < Q x ^ bhpExponent := Real.rpow_pos_of_pos hq0 _
    have hcount := (count_bounds hj hp).2
    have hpγ1 : 1 ≤ P x ^ priceExponent j := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hp (priceExponent_pos hj).le
    have hcap' := (div_lt_iff₀ hpB).mp hcapa
    have hfirst : (comparisonCount j (P x) : ℝ) + 1 ≤
        c * Q x ^ bhpExponent / log (Q x) := by
      apply (le_div_iff₀ hlq).mpr
      have hK3 : (comparisonCount j (P x) : ℝ) + 1 ≤ 3 * P x ^ priceExponent j := by
        linarith
      have hh := mul_le_mul_of_nonneg_right hK3 hlq.le
      nlinarith
    have hv0 : 0 < V x := by
      have : 1 ≤ layerPrime (m x) (j - 1) := le_max_left _ _
      dsimp [V]
      exact_mod_cast (show 0 < layerPrime (m x) (j - 1) by omega)
    have hw' := (div_lt_iff₀ hq0).mp hw
    have hlo' := (div_lt_iff₀ hq0).mp hlo
    have hup' := (div_lt_iff₀ hv0).mp hup
    have hr' := (lt_div_iff₀ hp0).mp hratio
    exact ⟨hx, hfirst, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp he)
  refine ⟨max T 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro n hn nu hnu hrec hlarge
  let x : S := ⟨(n, nu), hn, hnu, hrec⟩
  exact hT (largestPrime n : ℝ) ((le_max_left T 1).trans hlarge) x rfl

/- Explicit normalization: no boundary-price estimate occurs in these premises.
Only Q^j >= P and the already supplied coarse logarithmic scale are used. -/
theorem first_beta_lower {P : ℝ} (hP : 2 ≤ P) :
    1 / (P * log P) ≤ 2 * beta 1 P := by
  have hp0 : 0 < P := by linarith
  have hlp : 0 < log P := Real.log_pos (by linarith)
  have hh := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / P by positivity)
  have he : 1 - (1 + 1 / P)⁻¹ = 1 / (P + 1) := by
    field_simp [hp0.ne', (show P + 1 ≠ 0 by positivity)] <;> ring
  rw [he] at hh
  have hsmall : 1 / (2 * P) ≤ 1 / (P + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hgain : 1 / (2 * P) ≤ HigherLayerLogSlope.gain 1 P := by
    simpa [HigherLayerLogSlope.gain, powerSum] using hsmall.trans hh
  have h := div_le_div_of_nonneg_right hgain hlp.le
  change 1 / (2 * P) / log P ≤ beta 1 P at h
  have he' : 1 / (P * log P) = 2 * (1 / (2 * P) / log P) := by
    field_simp [hp0.ne', hlp.ne'] <;> ring
  rw [he']
  linarith

theorem priceLip_half_bound (j : ℕ) {P Q D : ℝ}
    (hP : 1 < P) (hQ : 4 ≤ Q) (hD : 0 < D)
    (hlog : log P / D ≤ log (Q / 2)) :
    priceLip j (Q / 2) ≤
      (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * D) / (Q ^ (j + 1) * log P) := by
  have hq0 : 0 < Q := by linarith
  have hLQ : 0 < log (Q / 2) := Real.log_pos (by linarith)
  have hLP : 0 < log P := Real.log_pos hP
  have he : priceLip j (Q / 2) =
      (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1)) / (Q ^ (j + 1) * log (Q / 2)) := by
    unfold priceLip
    rw [div_pow, pow_succ Q, pow_succ (2 : ℝ)]
    field_simp [hq0.ne', hLQ.ne'] <;> ring
  rw [he]
  calc
    _ ≤ (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1)) /
        (Q ^ (j + 1) * (log P / D)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hlog (pow_nonneg hq0.le _)
    _ = _ := by field_simp [hD.ne', hLP.ne', hq0.ne'] <;> ring

private def higherCostConstant (j : ℕ) : ℝ :=
  ((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))

private def firstCostConstant (A : ℝ) : ℝ := 192 * A * (2 : ℝ) ^ bhpExponent

private def totalCostConstant (j : ℕ) (A C : ℝ) : ℝ :=
  2 * C * higherCostConstant j + firstCostConstant A +
    8 * (j : ℝ) * (1 + firstCostConstant A)

/-- M3, a scalar bound on the literal cost expression, with the exact ceil count.
In particular no localization, pools, normalized error premise, or asymptotic
claim at a growing layer is an input to this normalization. -/
private theorem normalized_cost_bound (j : ℕ) (hj : 2 ≤ j)
    {A C P Q : ℝ} (hA : 0 < A) (hC : 0 < C) (hP : 4 ≤ P) (hQ : 4 ≤ Q)
    (hPQ : P ≤ Q ^ j) (hlog : log P / (4 * (j : ℝ)) ≤ log (Q / 2)) :
    let K := comparisonCount j P
    let w := C * Q ^ bhpExponent
    let v := 2 * A * (K : ℝ) * (2 * P) ^ bhpExponent
    priceLip j (Q / 2) * w + priceLip 1 (P / 2) * v +
      (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) ≤
        totalCostConstant j A C * beta 1 P * P ^ (-priceExponent j) := by
  dsimp only
  let K := comparisonCount j P
  let t := P ^ (-priceExponent j)
  let lambda := beta 1 P
  let Bj := higherCostConstant j
  let E := firstCostConstant A
  let v := 2 * A * (K : ℝ) * (2 * P) ^ bhpExponent
  have hp0 : 0 < P := by linarith
  have hq0 : 0 < Q := by linarith
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hLP : 0 < log P := Real.log_pos (by linarith)
  have hγ := priceExponent_pos hj
  have ht0 : 0 < t := Real.rpow_pos_of_pos hp0 _
  have ht1 : t ≤ 1 := by
    dsimp [t]
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ P by linarith)
      (show -priceExponent j ≤ 0 by linarith)
  have hlam : 0 < lambda := beta_pos (by linarith) (by norm_num)
  have hBj : 0 ≤ Bj := by dsimp [Bj, higherCostConstant]; positivity
  have hE : 0 ≤ E := by dsimp [E, firstCostConstant]; positivity
  have hbase : 1 / (P * log P) ≤ 2 * lambda := first_beta_lower (by linarith)
  have hQexp : Q ^ (bhpExponent - 1) ≤ t := by
    have hh := Real.rpow_le_rpow_of_nonpos hp0 hPQ (neg_nonpos.mpr hγ.le)
    have he : (Q ^ j) ^ (-priceExponent j) = Q ^ (bhpExponent - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
      congr 1
      dsimp [priceExponent, bhpExponent]
      field_simp [hj0.ne'] <;> ring
    rwa [he] at hh
  have hQpow : Q ^ bhpExponent = Q ^ (bhpExponent - 1) * Q := by
    calc
      _ = Q ^ ((bhpExponent - 1) + 1) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add hq0, Real.rpow_one]
  have hhigh : priceLip j (Q / 2) * (C * Q ^ bhpExponent) ≤
      (2 * C * Bj) * lambda * t := by
    have hLip := priceLip_half_bound j (by linarith : 1 < P) hQ
      (by positivity : 0 < 4 * (j : ℝ)) hlog
    change priceLip j (Q / 2) ≤ Bj / (Q ^ (j + 1) * log P) at hLip
    calc
      _ ≤ Bj / (Q ^ (j + 1) * log P) * (C * Q ^ bhpExponent) := by
        exact mul_le_mul_of_nonneg_right hLip (by positivity)
      _ = (C * Bj) * (1 / (Q ^ j * log P)) * Q ^ (bhpExponent - 1) := by
        rw [hQpow, pow_succ]
        field_simp [hq0.ne', hLP.ne'] <;> ring
      _ ≤ (C * Bj) * (1 / (P * log P)) * t := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hBj)
          exact one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_right hPQ hLP.le)
        · exact hQexp
        · positivity
        · positivity
      _ ≤ (C * Bj) * (2 * lambda) * t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbase (mul_nonneg hC.le hBj)) ht0.le
      _ = _ := by ring
  have hlogP : log P / 2 ≤ log (P / 2) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hP
    have he : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [he] at hh
    rw [Real.log_div hp0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  have hLip1 : priceLip 1 (P / 2) ≤ 24 / (P ^ 2 * log P) := by
    have hh := priceLip_half_bound 1 (by linarith : 1 < P) hP
      (by norm_num : (0 : ℝ) < 2) hlogP
    norm_num at hh
    exact hh
  have hv : v ≤ (4 * A * (2 : ℝ) ^ bhpExponent) * P ^ (priceExponent j + bhpExponent) := by
    calc
      _ ≤ 2 * A * (2 * P ^ priceExponent j) * (2 * P) ^ bhpExponent := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (count_bounds hj (by linarith)).2 (by positivity))
          (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp0.le,
          Real.rpow_add hp0]
        ring
  have hPexp : P ^ (priceExponent j + bhpExponent - 1) ≤ t := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have := priceExponent_le hj
    change priceExponent j + (21 / 40 : ℝ) - 1 ≤ -priceExponent j
    linarith
  have hPpow : P ^ (priceExponent j + bhpExponent) =
      P ^ (priceExponent j + bhpExponent - 1) * P := by
    calc
      _ = P ^ ((priceExponent j + bhpExponent - 1) + 1) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add hp0, Real.rpow_one]
  have hfirst : priceLip 1 (P / 2) * v ≤ E * lambda * t := by
    calc
      _ ≤ (24 / (P ^ 2 * log P)) *
          ((4 * A * (2 : ℝ) ^ bhpExponent) * P ^ (priceExponent j + bhpExponent)) := by
        apply mul_le_mul hLip1 hv
        · dsimp [v]; positivity
        · positivity
      _ = (96 * A * (2 : ℝ) ^ bhpExponent) * (1 / (P * log P)) *
          P ^ (priceExponent j + bhpExponent - 1) := by
        rw [hPpow]
        field_simp [hp0.ne', hLP.ne'] <;> ring
      _ ≤ (96 * A * (2 : ℝ) ^ bhpExponent) * (2 * lambda) * t := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hbase (by positivity)
        · exact hPexp
        · positivity
        · positivity
      _ = E * lambda * t := by dsimp [E, firstCostConstant]; ring
  have hK0 : 0 < (K : ℝ) := by
    have hh : 0 < K := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hp0 _)
    exact_mod_cast hh
  have hKinv : 1 / (K : ℝ) ≤ t := by
    have hh := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hp0 _)
      (count_bounds hj (by linarith)).1
    simpa [t, Real.rpow_neg hp0.le, one_div] using hh
  have hfirst' : priceLip 1 (P / 2) * v ≤ E * lambda := by
    exact hfirst.trans (mul_le_of_le_one_right (mul_nonneg hE hlam.le) ht1)
  have h8 : 8 * (j : ℝ) / (K : ℝ) ≤ 8 * (j : ℝ) * t := by
    simpa only [div_eq_mul_inv, one_div] using
      mul_le_mul_of_nonneg_left hKinv (show 0 ≤ 8 * (j : ℝ) by positivity)
  have hover : (8 * (j : ℝ) / (K : ℝ)) * (lambda + priceLip 1 (P / 2) * v) ≤
      (8 * (j : ℝ) * (1 + E)) * lambda * t := by
    have hsum : lambda + priceLip 1 (P / 2) * v ≤ lambda * (1 + E) := by
      nlinarith
    calc
      _ ≤ (8 * (j : ℝ) * t) * (lambda * (1 + E)) := by
        apply mul_le_mul h8 hsum
        · have hv0 : 0 ≤ v := by dsimp [v]; positivity
          have := mul_nonneg (priceLip_nonneg 1 (by linarith : 2 ≤ P / 2)) hv0
          linarith
        · positivity
      _ = _ := by ring
  change priceLip j (Q / 2) * (C * Q ^ bhpExponent) + priceLip 1 (P / 2) * v +
    (8 * (j : ℝ) / (K : ℝ)) * (lambda + priceLip 1 (P / 2) * v) ≤
      totalCostConstant j A C * lambda * t
  have he : totalCostConstant j A C * lambda * t =
      (2 * C * Bj) * lambda * t + E * lambda * t +
        (8 * (j : ℝ) * (1 + E)) * lambda * t := by
    dsimp [totalCostConstant, Bj, E]
    ring
  rw [he]
  linarith

/-- M4: the full original endpoint, using only the count supplier in its proof.
The maximum-gap premise remains in `BHPBoundaryPriceClaim` with its exact
original meaning. j is fixed before the uniform constant and threshold;
mu remains the original arbitrary positive record price throughout.

UNCOMPILED: proposed Lean proof terms, with N0 native verification OPEN. -/
theorem bhp_boundary_price_localization : BHPBoundaryPriceClaim := by
  intro _hmaximum hcounted
  obtain ⟨C, c, Xc, hC, hc, hXc, hcount⟩ := hcounted
  intro j hj
  obtain ⟨Tf, hTf, hfinite⟩ := actual_boundary_price_from_count_and_first_pools j hj
  obtain ⟨Tg, hTg, hgeometry⟩ := uniform_higher_geometry j hj C c Xc hC hc
  obtain ⟨Tp, hTp, hpools⟩ := uniform_counted_first_pools j hj C c Xc hC hc hcount
  obtain ⟨Tc, hTc, hcoarse⟩ := uniform_coarse_geometry j hj
  let T := max (max Tf Tg) (max Tp Tc)
  have hconstant : 0 < totalCostConstant j C C := by
    have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    dsimp [totalCostConstant, higherCostConstant, firstCostConstant]
    positivity
  refine ⟨totalCostConstant j C C, T, hconstant, ?_, ?_⟩
  · exact hTf.trans_le ((le_max_left Tf Tg).trans (le_max_left _ _))
  intro m hm mu hmu hrecord hlarge
  have hf : Tf ≤ (largestPrime m : ℝ) :=
    ((le_max_left Tf Tg).trans (le_max_left _ _)).trans hlarge
  have hg : Tg ≤ (largestPrime m : ℝ) :=
    ((le_max_right Tf Tg).trans (le_max_left _ _)).trans hlarge
  have hp : Tp ≤ (largestPrime m : ℝ) :=
    ((le_max_left Tp Tc).trans (le_max_right _ _)).trans hlarge
  have ht : Tc ≤ (largestPrime m : ℝ) :=
    ((le_max_right Tp Tc).trans (le_max_right _ _)).trans hlarge
  obtain ⟨hXQ, hcapacity, hwidth, hbelow, habove, hpower⟩ :=
    hgeometry m hm mu hmu hrecord hg
  obtain ⟨_hP4first, hv, hvP, FirstLo, FirstHi, hFLc, hFUc, hFL, hFU⟩ :=
    hpools (largestPrime m) hp
  obtain ⟨hP4, hQ4, _hQP, _hQ2P, hlog⟩ := hcoarse m hm mu hmu hrecord ht
  let P : ℝ := largestPrime m
  let Q : ℝ := layerPrime m j
  let K : ℕ := comparisonCount j P
  let v : ℝ := C * P ^ bhpExponent
  let V : ℝ := 2 * C * (K : ℝ) * (2 * P) ^ bhpExponent
  have hbound : |beta j Q - beta 1 P| ≤
      priceLip j (Q / 2) * (C * Q ^ bhpExponent) + priceLip 1 (P / 2) * v +
        (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) :=
    hfinite C c Xc hC hc hXc hcount m hm mu hmu hrecord hf
      hXQ hcapacity hwidth hbelow habove v hv hvP
      FirstLo FirstHi hFLc hFUc hFL hFU
  have hP0 : 0 < P := by change 0 < (largestPrime m : ℝ); linarith
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    have hKpos : 0 < K := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hP0 _)
    exact_mod_cast (show 1 ≤ K by omega)
  have hvV : v ≤ V := by
    have hpow : P ^ bhpExponent ≤ (2 * P) ^ bhpExponent :=
      Real.rpow_le_rpow hP0.le (by linarith) (by norm_num [bhpExponent])
    calc
      v ≤ C * (2 * P) ^ bhpExponent := mul_le_mul_of_nonneg_left hpow hC.le
      _ ≤ (2 * C * (K : ℝ)) * (2 * P) ^ bhpExponent := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        nlinarith
      _ = V := rfl
  have herror : priceLip 1 (P / 2) * v ≤ priceLip 1 (P / 2) * V :=
    mul_le_mul_of_nonneg_left hvV (priceLip_nonneg 1 (by
      change 2 ≤ (largestPrime m : ℝ) / 2
      linarith))
  have hcost :
      priceLip j (Q / 2) * (C * Q ^ bhpExponent) + priceLip 1 (P / 2) * v +
        (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * v) ≤
      totalCostConstant j C C * beta 1 P * P ^ (-priceExponent j) := by
    calc
      _ ≤ priceLip j (Q / 2) * (C * Q ^ bhpExponent) + priceLip 1 (P / 2) * V +
          (8 * (j : ℝ) / (K : ℝ)) * (beta 1 P + priceLip 1 (P / 2) * V) :=
        add_le_add (add_le_add_left herror _)
          (mul_le_mul_of_nonneg_left (add_le_add_left herror _) (by positivity))
      _ ≤ _ := normalized_cost_bound j hj hC hC hP4 hQ4 hpower hlog
  exact hbound.trans hcost

end D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceCandidate
