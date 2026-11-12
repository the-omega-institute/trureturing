/- GID: D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceGeometry
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Actual prime exchange geometry and local price estimates. -/
/- proof_shape: content
admission_basis: escape-witness
escape_witness: actual_boundary_price_from_pools: legal original-record exchanges constrain the two actual layer prices.
utility: none. These are unbounded conditional estimates, asymptotic laws and
finite-set identities for arbitrary inputs, not bounded enumeration, a checker,
a numerical reduction or a certified instance. Auxiliary bind-only statements
are consumed in the subsequent actual-record construction. -/
import D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
import D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Actual-record arithmetic: ActualBoundaryPriceGeometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization

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

/-- Boundary-price localization under the two independent analytic suppliers. -/
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
    change -logarithmicSlope j x * beta j x / x =
      (-(powerSumDerivative j x) / powerSum j x ^ 2 /
        (1 + 1 / powerSum j x) * log x - HigherLayerLogSlope.gain j x * x⁻¹) /
          log x ^ 2
    unfold logarithmicSlope beta
    field_simp [hx0.ne', hs.ne', hg.ne', hl.ne',
      (show 1 + 1 / powerSum j x ≠ 0 by positivity)]
    <;> ring

/-- An explicit local Lipschitz constant, not an assumed marginal-price band. -/
def priceLip (j : ℕ) (a : ℝ) : ℝ :=
  (((j : ℝ) + 2) * (1 / (a ^ j * log a))) / a

theorem priceLip_nonneg (j : ℕ) {a : ℝ} (ha : 2 ≤ a) :
    0 ≤ priceLip j a := by
  have ha0 : 0 < a := by linarith
  have hl := Real.log_pos (by linarith : 1 < a)
  unfold priceLip
  positivity

private theorem derivative_bound {j : ℕ} (hj : 1 ≤ j) {a x : ℝ}
    (ha : 2 ≤ a) (hax : a ≤ x) :
    |(-logarithmicSlope j x * beta j x / x)| ≤ priceLip j a := by
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
  have habs : |(-logarithmicSlope j x * beta j x / x)| =
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
    change 4 * (j : ℝ) * log 2 ≤ log (P x) at hL
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
    have := le_of_mul_le_mul_right hh (hA.trans_le hAN)
    linarith
  have hupp : h - lambda ≤ ej + e1 + R := by
    have hh : (h - lambda) * M ≤ (ej + e1 + R) * M := by nlinarith
    exact le_of_mul_le_mul_right hh (hA.trans_le hAM)
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
theorem actual_boundary_price_from_pools (j : ℕ) (hj : 2 ≤ j) :
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
    have hle : (p : ℝ) ≤ P := by
      change (p : ℝ) ≤ (largestPrime m : ℝ)
      exact_mod_cast (Nat.mem_primesLE.mp hmem).1
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

end D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
