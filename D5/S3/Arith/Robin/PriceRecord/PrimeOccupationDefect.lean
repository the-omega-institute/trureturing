/- GID: D5/S3/Arith/Robin/PriceRecord/PrimeOccupationDefect
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PrimeOccupationDefect
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Bounded-mass theta-weighted occupation defect for arbitrary finite prime selections. -/

import D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
The uniform theorem controls arbitrary finite prime selections.
Every private lemma is consumed on its proof path.

Generality I: the reference is the actual natural primes, with the fixed
reciprocal-square cost, cutoff sqrt(2)*sqrt(z), scale sqrt(z)*log(z), literal
threshold price and closed profile below. I-bearing inputs are
OriginalEndpointFirstLayerBand's theta difference identity, PrimeSquareTail's
uniform prime-square tail, and QuantitativePrimeAbel's prime intervals and
square sums. The theorem does not quantify over other reference sequences,
layer powers or cutoff constants; such extensions require their own estimates
and profile derivation. Uniformity over all permitted H and X is unchanged.

Two endpoint prices give an exact finite dual. Its two slopes converge to
the same number. The bounded *total* theta mass pays their discrepancy;
no restriction on the locations of the selected primes is imposed.
A finite open subcover of the scalar mass interval makes the bound uniform.
This is the finite-grid argument in an equivalent compact-cover form; it
uses compactness of [0,M], never compactness of prime selections/inventories.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect

open Finset Filter
open scoped Topology Chebyshev
open D5.S3.Arith.Robin.EulerLayerRootCorrection
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval squareSum)

/-- The literal square-layer threshold. -/
def cutoff (z : ℝ) : ℝ := Real.sqrt 2 * Real.sqrt z

def scale (z : ℝ) : ℝ := Real.sqrt z * Real.log z

private def priceAt (x : ℝ) : ℝ := 1 / (x ^ 2 * Real.log x)

/-- The price is evaluated at the literal threshold, without replacing its log. -/
def price (z : ℝ) : ℝ := 1 / (cutoff z ^ 2 * Real.log (cutoff z))

def thetaMass (S : Finset ℕ) : ℝ := ∑ p ∈ S, Real.log p

def mismatchMass (H X : Finset ℕ) : ℝ := thetaMass H + thetaMass X

def mismatchCost (z : ℝ) (H X : Finset ℕ) : ℝ :=
  (∑ p ∈ H, ((1 : ℝ) / (p : ℝ) ^ 2 - price z * Real.log p)) +
  ∑ p ∈ X, (price z * Real.log p - (1 : ℝ) / (p : ℝ) ^ 2)

/-- This is the closed profile, rather than a scalar minimum-inventory profile. -/
def profile (b : ℝ) : ℝ :=
  Real.sqrt ((Real.sqrt (1 + b ^ 2) + 3) ^ 3 /
    (Real.sqrt (1 + b ^ 2) + 1)) - 4 * Real.sqrt 2

private theorem mass_nonneg (S : Finset ℕ) : 0 ≤ thetaMass S :=
  sum_nonneg (fun p _ => Real.log_natCast_nonneg p)

private theorem interval_add (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (f : ℕ → ℝ) :
    (∑ p ∈ primeInterval a b, f p) + (∑ p ∈ primeInterval b c, f p) =
      ∑ p ∈ primeInterval a c, f p := by
  classical
  have hu : primeInterval a b ∪ primeInterval b c = primeInterval a c := by
    ext p
    simp only [primeInterval, mem_union, mem_filter, mem_Ioc]
    have h1 := Nat.floor_mono hab
    have h2 := Nat.floor_mono hbc
    by_cases hp : p.Prime <;> simp_all only [hp, and_true, and_false, or_false, false_or]
      <;> omega
  have hd : Disjoint (primeInterval a b) (primeInterval b c) := by
    apply disjoint_left.mpr
    intro p hp hq
    simp only [primeInterval, mem_filter, mem_Ioc] at hp hq
    omega
  rw [← sum_union hd, hu]

private theorem interval_theta (a b : ℝ) (hab : a ≤ b) :
    thetaMass (primeInterval a b) = θ b - θ a := by
  classical
  have hsets : primeInterval a b = Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊ := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_Ioc.mp hpI
      exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hb, hprime⟩,
        fun h => (not_le_of_gt ha) (Nat.mem_primesLE.mp h).1⟩
    · intro hp
      obtain ⟨hpb, hpa⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hb, hprime⟩ := Nat.mem_primesLE.mp hpb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨?_, hb⟩, hprime⟩
      by_contra hn
      exact hpa (Nat.mem_primesLE.mpr ⟨not_lt.mp hn, hprime⟩)
  rw [thetaMass, hsets]
  exact (D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.theta_sub_eq_prime_band_sum hab).symm

private theorem mem_interval {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) :
    p ∈ primeInterval a b ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  simp only [primeInterval, mem_filter, mem_Ioc]
  rw [Nat.floor_lt ha, Nat.le_floor_iff hb]
  tauto

private theorem prime_price_compare {x u : ℝ} (hx : 1 < x) (hu : 1 < u)
    (hxu : x ≤ u) :
    priceAt u * Real.log x ≤ 1 / x ^ 2 ∧
      1 / u ^ 2 ≤ priceAt x * Real.log u := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < u := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hs : x ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hx0.le hxu 2
  have hl : Real.log x ≤ Real.log u := Real.log_le_log hx0 hxu
  have hm : x ^ 2 * Real.log x ≤ u ^ 2 * Real.log u :=
    mul_le_mul hs hl hlx.le (sq_nonneg u)
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hx0)).mpr
    calc
      priceAt u * Real.log x * x ^ 2 =
          (x ^ 2 * Real.log x) / (u ^ 2 * Real.log u) := by dsimp [priceAt]; ring
      _ ≤ 1 := (div_le_one (mul_pos (sq_pos_of_pos hu0) hlu)).mpr hm
  · apply (div_le_iff₀ (sq_pos_of_pos hu0)).mpr
    calc
      1 ≤ (u ^ 2 * Real.log u) / (x ^ 2 * Real.log x) :=
        (one_le_div (mul_pos (sq_pos_of_pos hx0) hlx)).mpr hm
      _ = priceAt x * Real.log u * u ^ 2 := by dsimp [priceAt]; ring

/-- Select all positive gains, while all omitted gains have the opposite sign.
This finite-sum helper is consumed by the endpoint dual. -/
private theorem select_bound (S I : Finset ℕ) (f : ℕ → ℝ)
    (houtside : ∀ p ∈ S, p ∉ I → f p ≤ 0)
    (hinside : ∀ p ∈ I, 0 ≤ f p) :
    (∑ p ∈ S, f p) ≤ ∑ p ∈ I, f p := by
  classical
  calc
    _ ≤ ∑ p ∈ S ∩ I, f p :=
      sum_le_sum_of_subset_of_nonpos inter_subset_left (by
        intro p hp hpi
        exact houtside p hp (by simpa only [mem_inter, hp, true_and] using hpi))
    _ ≤ ∑ p ∈ I, f p :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p hp _ => hinside p hp)

private def beta (c z : ℝ) : ℝ :=
  Real.sqrt z * scale z * priceAt (c * Real.sqrt z)

private def intercept (A C z : ℝ) : ℝ :=
  scale z * (priceAt (A * Real.sqrt z) *
      thetaMass (primeInterval (A * Real.sqrt z) (cutoff z)) -
    squareSum (A * Real.sqrt z) (cutoff z) +
    squareSum (cutoff z) (C * Real.sqrt z) -
    priceAt (C * Real.sqrt z) *
      thetaMass (primeInterval (cutoff z) (C * Real.sqrt z)))

/-- Exact dual with two actual finite-z slopes. All selected primes occur in
its left side, including primes beyond either comparison interval. -/
private theorem finite_endpoint_dual {z A C : ℝ} (hz : 2 ≤ z)
    (ha : 1 < A * Real.sqrt z) (hAr : A ≤ Real.sqrt 2)
    (hrC : Real.sqrt 2 ≤ C) (hCz : C * Real.sqrt z ≤ z)
    (H X : Finset ℕ)
    (hH : ∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ cutoff z)
    (hX : ∀ p ∈ X, p.Prime ∧ cutoff z < (p : ℝ) ∧ (p : ℝ) ≤ z) :
    (beta A z - beta (Real.sqrt 2) z) * (thetaMass H / Real.sqrt z) +
      (beta (Real.sqrt 2) z - beta C z) * (thetaMass X / Real.sqrt z) -
        intercept A C z ≤ scale z * mismatchCost z H X := by
  classical
  have hz0 : 0 < z := by linarith
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz0
  have hD : 0 ≤ scale z := mul_nonneg hs.le (Real.log_nonneg (by linarith))
  have hay : A * Real.sqrt z ≤ cutoff z := mul_le_mul_of_nonneg_right hAr hs.le
  have hyc : cutoff z ≤ C * Real.sqrt z := mul_le_mul_of_nonneg_right hrC hs.le
  have hy : 1 < cutoff z := ha.trans_le hay
  have hc : 1 < C * Real.sqrt z := hy.trans_le hyc
  let IH := primeInterval (A * Real.sqrt z) (cutoff z)
  let IX := primeInterval (cutoff z) (C * Real.sqrt z)
  let fH : ℕ → ℝ := fun p => priceAt (A * Real.sqrt z) * Real.log p - 1 / (p : ℝ) ^ 2
  let fX : ℕ → ℝ := fun p => 1 / (p : ℝ) ^ 2 - priceAt (C * Real.sqrt z) * Real.log p
  have hlow := select_bound H IH fH (by
    intro p hp hpi
    obtain ⟨hpp, hpy⟩ := hH p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hpa : (p : ℝ) ≤ A * Real.sqrt z := by
      by_contra h
      exact hpi ((mem_interval (by linarith : 0 ≤ A * Real.sqrt z)
        (by linarith : 0 ≤ cutoff z) p).mpr ⟨hpp, lt_of_not_ge h, hpy⟩)
    exact sub_nonpos.mpr (prime_price_compare hp1 ha hpa).1) (by
    intro p hp
    obtain ⟨hpp, hap, _⟩ :=
      (mem_interval (by linarith : 0 ≤ A * Real.sqrt z)
        (by linarith : 0 ≤ cutoff z) p).mp hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    exact sub_nonneg.mpr (prime_price_compare ha hp1 hap.le).2)
  have hhigh := select_bound X IX fX (by
    intro p hp hpi
    obtain ⟨hpp, hyp, hpz⟩ := hX p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hcp : C * Real.sqrt z ≤ (p : ℝ) := by
      by_contra h
      exact hpi ((mem_interval (by linarith : 0 ≤ cutoff z)
        (by linarith : 0 ≤ C * Real.sqrt z) p).mpr
          ⟨hpp, hyp, (lt_of_not_ge h).le⟩)
    exact sub_nonpos.mpr (prime_price_compare hc hp1 hcp).2) (by
    intro p hp
    obtain ⟨hpp, _, hpc⟩ :=
      (mem_interval (by linarith : 0 ≤ cutoff z)
        (by linarith : 0 ≤ C * Real.sqrt z) p).mp hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    exact sub_nonneg.mpr (prime_price_compare hp1 hc hpc).1)
  have hsums := mul_le_mul_of_nonneg_left (add_le_add hlow hhigh) hD
  dsimp [fH, fX, IH, IX] at hsums
  simp only [sum_sub_distrib, ← mul_sum] at hsums
  have hcancel (d m : ℝ) :
      (Real.sqrt z * scale z * d) * (m / Real.sqrt z) = scale z * d * m := by
    field_simp [hs.ne']
    <;> ring
  dsimp only [mismatchCost]
  simp only [show price z = priceAt (cutoff z) from rfl]
  simp only [sub_mul, beta, hcancel]
  dsimp [intercept, thetaMass, squareSum] at *
  dsimp only [cutoff] at *
  simp only [sum_sub_distrib, ← mul_sum]
  nlinarith only [hsums]

/-- Reuse the existing real-cutoff prime-square theorem; no new PNT/Abel proof. -/
private theorem normalized_tail_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun z : ℝ => (c * Real.sqrt z) * Real.log (c * Real.sqrt z) *
      squareSum (c * Real.sqrt z) z) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK, Y, hY, htail⟩ := PrimeSquareTail.prime_square_tail_uniform ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((Real.tendsto_sqrt_atTop.eventually
      (eventually_ge_atTop (max (Y / c) (K * c)))).and
        (eventually_gt_atTop (0 : ℝ)))
  refine ⟨T, ?_⟩
  intro z hz
  obtain ⟨hroot, hz0⟩ := hT z hz
  have hYc : Y ≤ c * Real.sqrt z := by
    have h := (le_max_left (Y / c) (K * c)).trans hroot
    nlinarith only [(div_le_iff₀ hc).mp h]
  have hKc : K * (c * Real.sqrt z) ≤ z := by
    have h := mul_le_mul_of_nonneg_right
      ((le_max_right (Y / c) (K * c)).trans hroot) (Real.sqrt_nonneg z)
    nlinarith only [h, Real.sq_sqrt hz0.le]
  simpa only [Real.dist_eq, squareSum, primeInterval] using
    htail (c * Real.sqrt z) z hYc hKc

private theorem scaled_tail_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun z : ℝ => scale z * squareSum (c * Real.sqrt z) z)
      atTop (𝓝 (2 / c)) := by
  have hratio := (tendsto_const_nhds (x := (1 : ℝ))).div
    ((log_sqrt_scale hc).const_mul c) (by positivity : c * (1 / 2 : ℝ) ≠ 0)
  have hh := (normalized_tail_limit hc).mul hratio
  norm_num only [one_mul] at hh
  have hlim : 1 / (c * (1 / 2 : ℝ)) = 2 / c := by ring
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_sqrt_atTop.const_mul_atTop hc).eventually
      (eventually_gt_atTop (1 : ℝ))] with z hz hcz
  have hs : Real.sqrt z ≠ 0 := (Real.sqrt_pos.mpr (by linarith : 0 < z)).ne'
  have hl : Real.log z ≠ 0 := (Real.log_pos hz).ne'
  have hcl : Real.log (c * Real.sqrt z) ≠ 0 := (Real.log_pos hcz).ne'
  dsimp [scale]
  field_simp [hc.ne', hs, hl, hcl]
  <;> ring

private theorem beta_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (beta c) atTop (𝓝 (2 / c ^ 2)) := by
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).div
    ((log_sqrt_scale hc).const_mul (c ^ 2))
      (by positivity : c ^ 2 * (1 / 2 : ℝ) ≠ 0)
  have hlim : 1 / (c ^ 2 * (1 / 2 : ℝ)) = 2 / c ^ 2 := by ring
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_sqrt_atTop.const_mul_atTop hc).eventually
      (eventually_gt_atTop (1 : ℝ))] with z hz hcz
  have hz0 : 0 < z := by linarith
  have hs := Real.sq_sqrt hz0.le
  have hsn : Real.sqrt z ≠ 0 := (Real.sqrt_pos.mpr hz0).ne'
  have hnum : Real.sqrt z * (Real.sqrt z * Real.log z) = z * Real.log z := by
    rw [← mul_assoc, ← pow_two, hs]
  dsimp [beta, scale, priceAt]
  rw [hnum, mul_pow, hs]
  <;> field_simp [hc.ne', hz0.ne', (Real.log_pos hz).ne', (Real.log_pos hcz).ne']
  <;> ring

private theorem scaled_interval_limit {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    Tendsto (fun z : ℝ => scale z * squareSum (a * Real.sqrt z) (c * Real.sqrt z))
      atTop (𝓝 (2 / a - 2 / c)) := by
  have hc : 0 < c := ha.trans_le hac
  have hh := (scaled_tail_limit ha).sub (scaled_tail_limit hc)
  apply hh.congr'
  filter_upwards [Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop c),
    eventually_ge_atTop (0 : ℝ)] with z hroot hz
  have hcz : c * Real.sqrt z ≤ z := by
    nlinarith [mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg z), Real.sq_sqrt hz]
  have heq := interval_add (a * Real.sqrt z) (c * Real.sqrt z) z
    (mul_le_mul_of_nonneg_right hac (Real.sqrt_nonneg z)) hcz
    (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)
  dsimp [squareSum] at *
  rw [← heq]
  ring

private theorem intercept_limit {A C : ℝ} (hA : 0 < A)
    (hAr : A ≤ Real.sqrt 2) (hrC : Real.sqrt 2 ≤ C) :
    Tendsto (intercept A C) atTop
      (𝓝 ((2 / A ^ 2) * (Real.sqrt 2 - A) - (2 / A - 2 / Real.sqrt 2) +
        (2 / Real.sqrt 2 - 2 / C) - (2 / C ^ 2) * (C - Real.sqrt 2))) := by
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hC : 0 < C := hr.trans_le hrC
  have hthetaA := (theta_sqrt_scale hr).sub (theta_sqrt_scale hA)
  have hthetaC := (theta_sqrt_scale hC).sub (theta_sqrt_scale hr)
  have hh := (((beta_limit hA).mul hthetaA).sub (scaled_interval_limit hA hAr)).add
    ((scaled_interval_limit hr hrC).sub ((beta_limit hC).mul hthetaC))
  have hlim :
      (2 / A ^ 2) * (Real.sqrt 2 - A) - (2 / A - 2 / Real.sqrt 2) +
        ((2 / Real.sqrt 2 - 2 / C) - (2 / C ^ 2) * (C - Real.sqrt 2)) =
      (2 / A ^ 2) * (Real.sqrt 2 - A) - (2 / A - 2 / Real.sqrt 2) +
        (2 / Real.sqrt 2 - 2 / C) - (2 / C ^ 2) * (C - Real.sqrt 2) := by ring
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  have hs : Real.sqrt z ≠ 0 := (Real.sqrt_pos.mpr hz).ne'
  rw [← sub_div, ← sub_div]
  rw [← interval_theta _ _ (mul_le_mul_of_nonneg_right hAr (Real.sqrt_nonneg z)),
    ← interval_theta _ _ (mul_le_mul_of_nonneg_right hrC (Real.sqrt_nonneg z))]
  dsimp [intercept, beta, cutoff]
  field_simp [hs]
  <;> ring

/-- Closed algebraic optimizer. This is not an existence assumption about
prime selections, minimizers or exponent inventories. -/
private theorem profile_endpoints {b : ℝ} (hb : 0 ≤ b) :
    ∃ A C τ : ℝ, 0 < A ∧ A ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ C ∧
      0 ≤ τ ∧ τ < 1 ∧ C - A = b ∧
      2 / A ^ 2 - 1 = τ ∧ 1 - 2 / C ^ 2 = τ ∧
      A + C + 2 / A + 2 / C - 4 * Real.sqrt 2 = profile b := by
  let s := Real.sqrt (1 + b ^ 2)
  let P := 1 + s
  let T := Real.sqrt (b ^ 2 + 4 * P)
  let A := (T - b) / 2
  let C := (T + b) / 2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by nlinarith [sq_nonneg b]
  have hP : 0 < P := by dsimp [P]; linarith
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hT2 : T ^ 2 = b ^ 2 + 4 * P := Real.sq_sqrt (by positivity)
  have hTb : b < T := by nlinarith
  have hA : 0 < A := by dsimp [A]; linarith
  have hC : 0 < C := by dsimp [C]; linarith
  have hAC : A * C = P := by dsimp [A, C]; nlinarith only [hT2]
  have hdiff : C - A = b := by dsimp [A, C]; ring
  have hsum : A + C = T := by dsimp [A, C]; ring
  have hP2 : P ^ 2 = b ^ 2 + 2 * P := by dsimp [P]; nlinarith only [hs2]
  have hsq : A ^ 2 + C ^ 2 = A ^ 2 * C ^ 2 := by
    calc
      A ^ 2 + C ^ 2 = (C - A) ^ 2 + 2 * (A * C) := by ring
      _ = b ^ 2 + 2 * P := by rw [hdiff, hAC]
      _ = P ^ 2 := hP2.symm
      _ = (A * C) ^ 2 := by rw [hAC]
      _ = A ^ 2 * C ^ 2 := by ring
  have hinv : 1 / A ^ 2 + 1 / C ^ 2 = 1 := by
    field_simp [hA.ne', hC.ne']
    nlinarith only [hsq]
  have hac : A ≤ C := by linarith only [hdiff, hb]
  have hsqac : A ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hA.le hac 2
  have hinvac : 1 / C ^ 2 ≤ 1 / A ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hA) hsqac
  have hA2 : A ^ 2 ≤ 2 := by
    have hi : (1 / 2 : ℝ) ≤ 1 / A ^ 2 := by linarith only [hinv, hinvac]
    have := (le_div_iff₀ (sq_pos_of_pos hA)).mp hi
    linarith
  have hC2 : 2 ≤ C ^ 2 := by
    have hi : 1 / C ^ 2 ≤ (1 / 2 : ℝ) := by linarith only [hinv, hinvac]
    have := (div_le_iff₀ (sq_pos_of_pos hC)).mp hi
    linarith
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hAr : A ≤ Real.sqrt 2 := by nlinarith only [hA2, hr0, hr2, hA]
  have hrC : Real.sqrt 2 ≤ C := by nlinarith only [hC2, hr0, hr2, hC]
  let τ := 2 / A ^ 2 - 1
  have hτ0 : 0 ≤ τ := by
    dsimp [τ]
    have hi : (1 : ℝ) ≤ 2 / A ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hA)).mpr (by nlinarith only [hA2])
    linarith only [hi]
  have hinv2 : 2 / A ^ 2 + 2 / C ^ 2 = 2 := by
    linear_combination 2 * hinv
  have hτ1 : τ < 1 := by
    have hi : 0 < 2 / C ^ 2 := by positivity
    dsimp [τ]
    linarith only [hinv2, hi]
  have hτC : 1 - 2 / C ^ 2 = τ := by dsimp [τ]; linarith only [hinv2]
  have hTP : T ^ 2 = P * (P + 2) := by nlinarith only [hP2, hT2]
  have hroot : Real.sqrt ((s + 3) ^ 3 / (s + 1)) = T * (P + 2) / P := by
    have hR0 : 0 ≤ (s + 3) ^ 3 / (s + 1) := by positivity
    have hR2 := Real.sq_sqrt hR0
    have hRpos := Real.sqrt_nonneg ((s + 3) ^ 3 / (s + 1))
    have heq : (T * (P + 2) / P) ^ 2 = (s + 3) ^ 3 / (s + 1) := by
      calc
        _ = T ^ 2 * (P + 2) ^ 2 / P ^ 2 := by ring
        _ = (P * (P + 2)) * (P + 2) ^ 2 / P ^ 2 := by rw [hTP]
        _ = (P + 2) ^ 3 / P := by field_simp [hP.ne'] <;> ring
        _ = _ := by dsimp [P]; ring
    have hpos : 0 ≤ T * (P + 2) / P := by positivity
    nlinarith only [hR2, heq, hRpos, hpos]
  have hG : A + C + 2 / A + 2 / C = T * (P + 2) / P := by
    rw [← hsum, ← hAC]
    field_simp [hA.ne', hC.ne']
    <;> ring
  refine ⟨A, C, τ, hA, hAr, hrC, hτ0, hτ1, hdiff, rfl, hτC, ?_⟩
  dsimp [profile]
  rw [hG, ← hroot]

private theorem profile_continuous : Continuous profile := by
  have hs : Continuous (fun b : ℝ => Real.sqrt (1 + b ^ 2)) :=
    (continuous_const.add (continuous_id.pow 2)).sqrt
  exact (((hs.add continuous_const).pow 3).div (hs.add continuous_const)
    (fun b => ne_of_gt (add_pos_of_nonneg_of_pos
      (Real.sqrt_nonneg (1 + b ^ 2)) zero_lt_one))).sqrt.sub continuous_const

/-- One fixed dual line, uniform over all prime selections of bounded mass.
The slopes retain the finite alpha_z correction until their limits are taken. -/
private theorem eventual_supporting_line {M b A C τ η : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (hA : 0 < A)
    (hAr : A ≤ Real.sqrt 2) (hrC : Real.sqrt 2 ≤ C)
    (hdiff : C - A = b) (hτA : 2 / A ^ 2 - 1 = τ)
    (hτC : 1 - 2 / C ^ 2 = τ)
    (hG : A + C + 2 / A + 2 / C - 4 * Real.sqrt 2 = profile b) :
    ∀ᶠ z : ℝ in atTop, ∀ H X : Finset ℕ,
      (∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ cutoff z) →
      (∀ p ∈ X, p.Prime ∧ cutoff z < (p : ℝ) ∧ (p : ℝ) ≤ z) →
      mismatchMass H X ≤ M * Real.sqrt z →
      profile b + τ * (mismatchMass H X / Real.sqrt z - b) ≤
        scale z * mismatchCost z H X + η := by
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hC : 0 < C := hr.trans_le hrC
  have hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hμH : Tendsto (fun z => beta A z - beta (Real.sqrt 2) z) atTop (𝓝 τ) := by
    simpa only [hr2, div_self (by norm_num : (2 : ℝ) ≠ 0), hτA] using
      (beta_limit hA).sub (beta_limit hr)
  have hμX : Tendsto (fun z => beta (Real.sqrt 2) z - beta C z) atTop (𝓝 τ) := by
    simpa only [hr2, div_self (by norm_num : (2 : ℝ) ≠ 0), hτC] using
      (beta_limit hr).sub (beta_limit hC)
  let I := τ * b - profile b
  have hIeq :
      (2 / A ^ 2) * (Real.sqrt 2 - A) - (2 / A - 2 / Real.sqrt 2) +
        (2 / Real.sqrt 2 - 2 / C) - (2 / C ^ 2) * (C - Real.sqrt 2) =
          τ * b - profile b := by
    have hrinv : 2 / Real.sqrt 2 = Real.sqrt 2 := by
      apply (div_eq_iff hr.ne').mpr
      nlinarith only [hr2]
    have haid : 2 / A ^ 2 = τ + 1 := by linarith only [hτA]
    have hcid : 2 / C ^ 2 = 1 - τ := by linarith only [hτC]
    rw [haid, hcid, hrinv, ← hG, ← hdiff]
    ring
  have hI : Tendsto (intercept A C) atTop (𝓝 I) := by
    simpa only [hIeq] using intercept_limit hA hAr hrC
  let err := fun z => (M + 1) *
    (|beta A z - beta (Real.sqrt 2) z - τ| +
      |beta (Real.sqrt 2) z - beta C z - τ|) + |intercept A C z - I|
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, add_zero, mul_zero] using
      (((hμH.sub_const τ).abs.add (hμX.sub_const τ).abs).const_mul (M + 1)).add
        (hI.sub_const I).abs
  have he := herr.eventually_lt_const hη
  have ha := (Real.tendsto_sqrt_atTop.const_mul_atTop hA).eventually
    (eventually_gt_atTop (1 : ℝ))
  have hc := Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop C)
  filter_upwards [he, ha, hc, eventually_ge_atTop (2 : ℝ)] with z he ha hc hz
  intro H X hH hX hmass
  have hz0 : 0 < z := by linarith
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz0
  have hcz : C * Real.sqrt z ≤ z := by
    nlinarith [mul_le_mul_of_nonneg_right hc hs.le, Real.sq_sqrt hz0.le]
  have hdual := finite_endpoint_dual hz ha hAr hrC hcz H X hH hX
  let u := thetaMass H / Real.sqrt z
  let v := thetaMass X / Real.sqrt z
  have hu : 0 ≤ u := div_nonneg (mass_nonneg H) hs.le
  have hv : 0 ≤ v := div_nonneg (mass_nonneg X) hs.le
  have huv : u + v ≤ M := by
    rw [← add_div]
    exact (div_le_iff₀ hs).mpr hmass
  have huM : u ≤ M + 1 := by linarith
  have hvM : v ≤ M + 1 := by linarith
  have h1 : (τ - (beta A z - beta (Real.sqrt 2) z)) * u ≤
      |beta A z - beta (Real.sqrt 2) z - τ| * (M + 1) := by
    calc
      _ ≤ |beta A z - beta (Real.sqrt 2) z - τ| * u :=
        mul_le_mul_of_nonneg_right (by
          have hh := neg_le_abs (beta A z - beta (Real.sqrt 2) z - τ)
          linarith only [hh]) hu
      _ ≤ _ := mul_le_mul_of_nonneg_left huM (abs_nonneg _)
  have h2 : (τ - (beta (Real.sqrt 2) z - beta C z)) * v ≤
      |beta (Real.sqrt 2) z - beta C z - τ| * (M + 1) := by
    calc
      _ ≤ |beta (Real.sqrt 2) z - beta C z - τ| * v :=
        mul_le_mul_of_nonneg_right (by
          have hh := neg_le_abs (beta (Real.sqrt 2) z - beta C z - τ)
          linarith only [hh]) hv
      _ ≤ _ := mul_le_mul_of_nonneg_left hvM (abs_nonneg _)
  have h3 := le_abs_self (intercept A C z - I)
  dsimp [err] at he
  dsimp [u, v] at h1 h2
  dsimp [I] at h3
  dsimp [mismatchMass]
  rw [add_div]
  nlinarith only [hdual, h1, h2, h3, he]

/-- For every bounded total theta mismatch and every positive tolerance, one
threshold works for all real z and all finite hole/excess sets. The cutoffs,
weights and logarithms are literal. No record, optimizer, tightness, exponent
bound, RH or target-bound premise is present. -/
theorem uniform_prime_occupation_defect (M : ℝ) (hM : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z : ℝ, Z ≤ z → ∀ H X : Finset ℕ,
      (∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ Real.sqrt 2 * Real.sqrt z) →
      (∀ p ∈ X, p.Prime ∧ Real.sqrt 2 * Real.sqrt z < (p : ℝ) ∧ (p : ℝ) ≤ z) →
      (∑ p ∈ H, Real.log p) + (∑ p ∈ X, Real.log p) ≤ M * Real.sqrt z →
      profile (((∑ p ∈ H, Real.log p) + (∑ p ∈ X, Real.log p)) / Real.sqrt z) ≤
        (Real.sqrt z * Real.log z) *
          ((∑ p ∈ H, ((1 : ℝ) / (p : ℝ) ^ 2 -
              (1 / ((Real.sqrt 2 * Real.sqrt z) ^ 2 *
                Real.log (Real.sqrt 2 * Real.sqrt z))) * Real.log p)) +
            ∑ p ∈ X, ((1 / ((Real.sqrt 2 * Real.sqrt z) ^ 2 *
                Real.log (Real.sqrt 2 * Real.sqrt z))) * Real.log p -
              (1 : ℝ) / (p : ℝ) ^ 2)) + ε := by
  classical
  let Q := Set.Icc (0 : ℝ) M
  have hend (b : Q) := profile_endpoints b.property.1
  choose A C τ hA hAr hrC hτ0 hτ1 hdiff hτA hτC hG using hend
  let U : Q → Set ℝ := fun b =>
    {x | profile x < profile b + τ b * (x - b) + ε / 2}
  have hopen (b : Q) : IsOpen (U b) := by
    change IsOpen {x : ℝ | profile x < profile b + τ b * (x - b) + ε / 2}
    exact isOpen_lt profile_continuous (by fun_prop)
  have hcover : Q ⊆ ⋃ b : Q, U b := by
    intro b hb
    apply Set.mem_iUnion.mpr
    refine ⟨⟨b, hb⟩, ?_⟩
    change profile b < profile b + τ ⟨b, hb⟩ * (b - b) + ε / 2
    simp only [sub_self, mul_zero, add_zero]
    linarith
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover U hopen hcover
  have hlines : ∀ᶠ z : ℝ in atTop, ∀ b ∈ F, ∀ H X : Finset ℕ,
      (∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ cutoff z) →
      (∀ p ∈ X, p.Prime ∧ cutoff z < (p : ℝ) ∧ (p : ℝ) ≤ z) →
      mismatchMass H X ≤ M * Real.sqrt z →
      profile b + τ b * (mismatchMass H X / Real.sqrt z - b) ≤
        scale z * mismatchCost z H X + ε / 2 := by
    apply (eventually_all_finset F).mpr
    intro b hb
    exact eventual_supporting_line hM (by linarith) (hA b) (hAr b) (hrC b)
      (hdiff b) (hτA b) (hτC b) (hG b)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hlines
  refine ⟨max T 2, le_max_right _ _, ?_⟩
  intro z hz H X hH hX hm
  have hz2 : 2 ≤ z := (le_max_right T 2).trans hz
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr (by linarith)
  have hb : mismatchMass H X / Real.sqrt z ∈ Q := by
    refine ⟨div_nonneg (add_nonneg (mass_nonneg H) (mass_nonneg X)) hs.le, ?_⟩
    exact (div_le_iff₀ hs).mpr hm
  obtain ⟨b, hbF, hbU⟩ := Set.mem_iUnion₂.mp (hF hb)
  have hline := hT z ((le_max_left T 2).trans hz) b hbF H X hH hX hm
  change profile (mismatchMass H X / Real.sqrt z) <
    profile b + τ b * (mismatchMass H X / Real.sqrt z - b) + ε / 2 at hbU
  change profile (mismatchMass H X / Real.sqrt z) ≤
    scale z * mismatchCost z H X + ε
  linarith only [hbU, hline]

end D5.S3.Arith.Robin.PriceRecord.PrimeOccupationDefect
