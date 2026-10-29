/- GID: D5/S3/Arith/Robin/OriginalEndpointPrimeTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalEndpointPrimeTail
   mirror-E: none(waiver:general-analytic-results-no-numerical-evidence-artifact)
   anchors: []
   utility: none
   digest: Sharp all-price original endpoint tails with a same-integer square-root bound and exact Robin margin decomposition. -/

/-
The actual strict and maximal optimizers are retained at every positive
price. Local included/omitted marginal inequalities give sharp tail prices;
the adaptive support split gives the same-integer 7/(2 sqrt u) bound. The
exact margin decomposition retains every active prime and positive layer,
including simultaneous activation ties. Logarithm bounds are imported from
their existing owner. No final endpoint sign or RH conclusion is assumed
or proved by this supplier. The additional first-layer paper calculation in
the Scribe is explanatory mathematics and is not a separate Lean result.
-/
import D5.S3.Arith.Robin.ActualGlobalBracketing
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
import D5.S3.Arith.GoldenResourceObjectiveFactorization
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Weil.Mertens.Third
import D5.S3.Weil.GronwallLowerEnvelope
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Weil.GronwallLowerEnvelope

private noncomputable def truncationTail (y : Real) : Real :=
  -Real.log (1 - y)

private noncomputable def nextMarginal (p y : Real) : Real :=
  Real.log ((1 - y / p) / (1 - y))

private noncomputable def lastMarginal (p y : Real) : Real :=
  Real.log ((1 - y) / (1 - p * y))

private theorem one_sub_pos
    {p y : Real} (hp : 1 < p) (hy : 0 <= y) (hpy : p * y < 1) :
    0 < 1 - y := by
  have h : y <= p * y := by
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hp)) hy]
  linarith

private theorem price_den_pos
    {p z : Real} (hp : 1 < p) (hz : 1 < z) :
    0 < p * z - 1 := by
  nlinarith [mul_pos (sub_pos.mpr hp) (sub_pos.mpr hz)]

/-- Convert the actual logarithmic marginal bracket to rational inequalities. -/
private theorem ratio_bracket_of_log_bracket
    {p y c : Real} (hp : 1 < p) (hy : 0 <= y) (hpy : p * y < 1)
    (hnext : nextMarginal p y <= c) (hlast : c <= lastMarginal p y) :
    (1 - y / p) / (1 - y) <= Real.exp c /\
      Real.exp c <= (1 - y) / (1 - p * y) := by
  have hp0 : 0 < p := by linarith
  have h1 : 0 < 1 - y := one_sub_pos hp hy hpy
  have hsmall : y / p < 1 := by
    apply (div_lt_iff₀ hp0).2
    nlinarith
  have hn : 0 < (1 - y / p) / (1 - y) :=
    div_pos (by linarith) h1
  have hl : 0 < (1 - y) / (1 - p * y) :=
    div_pos h1 (by linarith)
  constructor
  · have h := Real.exp_le_exp.mpr hnext
    simpa only [nextMarginal, Real.exp_log hn] using h
  · have h := Real.exp_le_exp.mpr hlast
    simpa only [lastMarginal, Real.exp_log hl] using h

/-- The first omitted layer gives the sharp upper bound on p^(-(a+1)). -/
private theorem omitted_fraction_bound
    {p y z : Real} (hp : 1 < p) (hz : 1 < z)
    (hy : 0 <= y) (hpy : p * y < 1)
    (hnext : (1 - y / p) / (1 - y) <= z) :
    y <= p * (z - 1) / (p * z - 1) := by
  have hp0 : 0 < p := by linarith
  have h1 : 0 < 1 - y := one_sub_pos hp hy hpy
  have hden : 0 < p * z - 1 := price_den_pos hp hz
  have h := (div_le_iff₀ h1).mp hnext
  have hm := mul_le_mul_of_nonneg_left h (le_of_lt hp0)
  have hc : p * (y / p) = y := by
    field_simp [ne_of_gt hp0] <;> ring
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The last selected layer gives the sharp lower bound on p^(-(a+1)). -/
private theorem included_fraction_bound
    {p y z : Real} (hp : 1 < p) (hz : 1 < z)
    (hy : 0 <= y) (hpy : p * y < 1)
    (hlast : z <= (1 - y) / (1 - p * y)) :
    (z - 1) / (p * z - 1) <= y := by
  have hden : 0 < p * z - 1 := price_den_pos hp hz
  have h := (le_div_iff₀ (show 0 < 1 - p * y by linarith)).mp hlast
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Exact local tail upper bound; this consumes the omitted marginal inequality. -/
private theorem tail_upper_of_omitted
    {p y z : Real} (hp : 1 < p) (hz : 1 < z)
    (hy : 0 <= y) (hpy : p * y < 1)
    (hnext : (1 - y / p) / (1 - y) <= z) :
    truncationTail y <= Real.log ((p * z - 1) / (p - 1)) := by
  have h1 : 0 < 1 - y := one_sub_pos hp hy hpy
  have hden : 0 < p * z - 1 := price_den_pos hp hz
  have hf := omitted_fraction_bound hp hz hy hpy hnext
  have hf' := (le_div_iff₀ hden).mp hf
  have hr : 1 / (1 - y) <= (p * z - 1) / (p - 1) := by
    apply (div_le_div_iff₀ h1 (sub_pos.mpr hp)).2
    nlinarith
  calc
    truncationTail y = Real.log (1 / (1 - y)) := by
      simp [truncationTail, Real.log_div]
    _ <= Real.log ((p * z - 1) / (p - 1)) :=
      Real.log_le_log (div_pos zero_lt_one h1) hr

/-- Sharp local sandwich; simultaneous activation ties satisfy both endpoints. -/
private theorem sharp_tail_sandwich
    {p y z : Real} (hp : 1 < p) (hz : 1 < z)
    (hy : 0 <= y) (hpy : p * y < 1)
    (hnext : (1 - y / p) / (1 - y) <= z)
    (hlast : z <= (1 - y) / (1 - p * y)) :
    Real.log ((p * z - 1) / ((p - 1) * z)) <= truncationTail y /\
      truncationTail y <= Real.log ((p * z - 1) / (p - 1)) := by
  have h1 : 0 < 1 - y := one_sub_pos hp hy hpy
  have hden : 0 < p * z - 1 := price_den_pos hp hz
  have hz0 : 0 < z := by linarith
  have hf := included_fraction_bound hp hz hy hpy hlast
  have hf' := (div_le_iff₀ hden).mp hf
  constructor
  · have hr : (p * z - 1) / ((p - 1) * z) <= 1 / (1 - y) := by
      apply (div_le_div_iff₀ (mul_pos (sub_pos.mpr hp) hz0) h1).2
      nlinarith
    calc
      Real.log ((p * z - 1) / ((p - 1) * z))
          <= Real.log (1 / (1 - y)) :=
        Real.log_le_log (div_pos hden (mul_pos (sub_pos.mpr hp) hz0)) hr
      _ = truncationTail y := by
        simp [truncationTail, Real.log_div]
  · exact tail_upper_of_omitted hp hz hy hpy hnext

/-- A quantitative bound, beyond an Euler-product rewriting. -/
private theorem tail_linear_of_omitted
    {p y z : Real} (hp : 1 < p) (hz : 1 < z)
    (hy : 0 <= y) (hpy : p * y < 1)
    (hnext : (1 - y / p) / (1 - y) <= z) :
    truncationTail y <= p / (p - 1) * (z - 1) := by
  have hden : 0 < p * z - 1 := price_den_pos hp hz
  calc
    truncationTail y <= Real.log ((p * z - 1) / (p - 1)) :=
      tail_upper_of_omitted hp hz hy hpy hnext
    _ <= (p * z - 1) / (p - 1) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hden (sub_pos.mpr hp))
    _ = p / (p - 1) * (z - 1) := by
      field_simp [ne_of_gt (sub_pos.mpr hp)]
      <;> ring

/-- The SAME integer's Euler-product truncation term. -/
def layerTail (N p : ℕ) : ℝ :=
  -Real.log (1 - (p : ℝ)⁻¹ ^ (N.factorization p + 1))

def tail (N : ℕ) : ℝ := ∑ p ∈ N.primeFactors, layerTail N p

def eulerMass (N : ℕ) : ℝ :=
  ∑ p ∈ N.primeFactors, -Real.log (1 - (p : ℝ)⁻¹)

def lowerPrice (q : ℝ) (p : ℕ) : ℝ :=
  Real.log (((p : ℝ) * Real.exp (q * Real.log p) - 1) /
    (((p : ℝ) - 1) * Real.exp (q * Real.log p)))

def upperPrice (q : ℝ) (p : ℕ) : ℝ :=
  Real.log (((p : ℝ) * Real.exp (q * Real.log p) - 1) / ((p : ℝ) - 1))

/-- `0` is only the empty-support convention. -/
def largestPrime (N : ℕ) : ℕ := N.primeFactors.sup id

/-! The general finite Euler/log-sigma calculation is shared by both the
optimizer endpoint and the support-conditioned finite correction below. -/
private theorem log_sigma_div_eq_eulerMass_sub_tail {N : ℕ} (hN : 0 < N) :
    Real.log ((ArithmeticFunction.sigma 1 N : ℝ) / N) = eulerMass N - tail N := by
  have hf := golden_resource_objective_factorization 0 (show 1 ≤ N by omega)
  rw [golden_resource_sigma_identity 0 (show 1 ≤ N by omega)] at hf
  simp only [zero_mul, sub_zero] at hf
  rw [hf, eulerMass, tail, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hpp.pos)
  have hi1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by exact_mod_cast hpp.pos)).mpr (by exact_mod_cast hpp.one_lt)
  have hnum : 0 < 1 - (p : ℝ)⁻¹ ^ (N.factorization p + 1) :=
    sub_pos.mpr (pow_lt_one₀ hi0.le hi1 (by
      have hz : 1 ≤ N.factorization p :=
        hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
      omega))
  have hden : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr hi1
  simp only [goldenPrimeLocalObjective, zero_mul, sub_zero, layerTail]
  rw [Real.log_div hnum.ne' hden.ne']
  ring

/-- Local original-source application, preserving strict/weak ties.
This helper is consumed by endpoint_local and the cutoff-price calculation. -/
private theorem endpoint_bracket {q : ℝ} (hq : 0 < q) {N p : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hp : p.Prime) (ha : 1 ≤ N.factorization p) :
    goldenLayerMarginal p (N.factorization p + 1) ≤ q ∧
      q ≤ goldenLayerMarginal p (N.factorization p) ∧
      q ≤ goldenLayerMarginal p 1 := by
  rcases hN with rfl | rfl
  · refine ⟨?_, ((strict_layer_iff hq hp ha).mp le_rfl).le,
      ((strict_layer_iff hq hp (by omega)).mp ha).le⟩
    apply le_of_not_gt
    intro h
    have := (strict_layer_iff hq hp (by omega)).mpr h
    omega
  · refine ⟨?_, (weak_layer_iff hq hp ha).mp le_rfl,
      (weak_layer_iff hq hp (by omega)).mp ha⟩
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    have := (weak_layer_iff hq hp (by omega)).mpr h
    omega

/-- Quantitative last-selected/first-omitted supply for the real endpoints.
The last component reuses an existing logarithm estimate, rather than
reproving a library-matching log remainder theorem. -/
theorem endpoint_local {q : ℝ} (hq : 0 < q) {N p : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hp : p.Prime) (ha : 1 ≤ N.factorization p) :
    0 ≤ layerTail N p ∧ lowerPrice q p ≤ layerTail N p ∧
      layerTail N p ≤ upperPrice q p ∧
      layerTail N p ≤ (p : ℝ) / ((p : ℝ) - 1) *
        (Real.exp (q * Real.log p) - 1) ∧
      layerTail N p ≤ (5 / 4 : ℝ) / (p : ℝ) ^ 2 := by
  let a := N.factorization p
  let v : ℝ := (p : ℝ)⁻¹
  let y : ℝ := v ^ (a + 1)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hv0 : 0 < v := inv_pos.mpr hp0
  have hv1 : v < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hy0 : 0 ≤ y := (pow_pos hv0 _).le
  have hpa : (p : ℝ) * y = v ^ a := by
    dsimp [y, v]
    rw [pow_succ]
    field_simp [hp0.ne']
  have hpy : (p : ℝ) * y < 1 := by
    rw [hpa]
    exact pow_lt_one₀ hv0.le hv1 (by dsimp [a]; omega)
  have hynext : y / (p : ℝ) = v ^ (a + 1 + 1) := by
    simp [y, v, pow_succ, div_eq_mul_inv]
  have hmatch_next : nextMarginal p y =
      goldenLayerMarginal p (a + 1) * Real.log p := by
    unfold nextMarginal goldenLayerMarginal
    rw [div_mul_cancel₀ _ hlog.ne', hynext]
  have hmatch_last : lastMarginal p y =
      goldenLayerMarginal p a * Real.log p := by
    unfold lastMarginal goldenLayerMarginal
    rw [div_mul_cancel₀ _ hlog.ne', hpa]
  have hb := endpoint_bracket hq hN hp ha
  have hnext : nextMarginal p y ≤ q * Real.log p := by
    rw [hmatch_next]
    exact mul_le_mul_of_nonneg_right hb.1 hlog.le
  have hlast : q * Real.log p ≤ lastMarginal p y := by
    rw [hmatch_last]
    exact mul_le_mul_of_nonneg_right hb.2.1 hlog.le
  have hz : 1 < Real.exp (q * Real.log p) :=
    Real.one_lt_exp_iff.mpr (mul_pos hq hlog)
  have hr := ratio_bracket_of_log_bracket hp1 hy0 hpy hnext hlast
  have hs := sharp_tail_sandwich hp1 hz hy0 hpy hr.1 hr.2
  have hlin := tail_linear_of_omitted hp1 hz hy0 hpy hr.1
  have hy2 : y ≤ 1 / (p : ℝ)^2 := by
    have h := pow_le_pow_of_le_one hv0.le hv1.le (show 2 ≤ a + 1 by dsimp [a]; omega)
    simpa [y, v, inv_pow, one_div] using h
  have hy4 : y ≤ 1 / 4 := by
    have hpp : (4 : ℝ) ≤ (p : ℝ)^2 := by nlinarith
    exact hy2.trans ((div_le_div_iff₀ (pow_pos hp0 _) (by norm_num)).2 (by linarith))
  have hlarge : truncationTail y ≤ (5 / 4 : ℝ) / (p : ℝ)^2 := by
    have h := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le hy0
      (show y ≤ 1 / 2 by linarith)
    have hySq : y^2 ≤ y / 4 := by nlinarith
    calc
      truncationTail y ≤ y + y^2 := h
      _ ≤ (5 / 4 : ℝ) * y := by linarith
      _ ≤ (5 / 4 : ℝ) * (1 / (p : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hy2 (by norm_num)
      _ = (5 / 4 : ℝ) / (p : ℝ)^2 := by ring
  have hnonneg : 0 ≤ truncationTail y := by
    have hylt : y < 1 := by linarith
    have h := Real.log_le_log (show 0 < 1 - y by linarith)
      (show 1 - y ≤ 1 by linarith)
    dsimp only [truncationTail]
    exact neg_nonneg.mpr (by simpa only [Real.log_one] using h)
  change 0 ≤ truncationTail y ∧ _
  exact ⟨hnonneg, hs.1, hs.2, hlin, hlarge⟩

/-- Price control on small primes is the new endpoint-specific step.
The source integer is not replaced by an lcm or a common height cutoff. -/
private theorem endpoint_small {q : ℝ} (hq : 0 < q) {N p : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hp : p.Prime) (ha : 1 ≤ N.factorization p) {u : ℝ}
    (hu : 0 < u) (hprice : q * Real.log u ≤ Real.log (1 + 1 / u))
    (hps : (p : ℝ) ≤ Real.sqrt u) : layerTail N p ≤ 1 / u := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hpSq : (p : ℝ)^2 ≤ u := by
    nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg u]
  have hlogs := Real.log_le_log (pow_pos hp0 2) hpSq
  rw [Real.log_pow] at hlogs
  have h2c : 2 * (q * Real.log p) ≤ Real.log (1 + 1 / u) := by
    have h := mul_le_mul_of_nonneg_left hlogs hq.le
    norm_num at h
    nlinarith
  have hz : 1 < Real.exp (q * Real.log p) :=
    Real.one_lt_exp_iff.mpr (mul_pos hq hlog)
  have hzSq : Real.exp (q * Real.log p) * Real.exp (q * Real.log p) ≤ 1 + 1 / u := by
    have h := Real.exp_le_exp.mpr h2c
    rw [Real.exp_log (by positivity : 0 < 1 + 1 / u)] at h
    simpa only [two_mul, Real.exp_add] using h
  have hlin := (endpoint_local hq hN hp ha).2.2.2.1
  have hratio : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
    apply (div_le_iff₀ (sub_pos.mpr hp1)).2
    linarith
  calc
    layerTail N p ≤ (p : ℝ) / ((p : ℝ) - 1) *
        (Real.exp (q * Real.log p) - 1) := hlin
    _ ≤ 2 * (Real.exp (q * Real.log p) - 1) :=
      mul_le_mul_of_nonneg_right hratio (by linarith)
    _ ≤ 1 / u := by nlinarith [sq_nonneg (Real.exp (q * Real.log p) - 1)]

/-- One full-scope scientific supplier. The outer disjunction uses the ORIGINAL
strictInteger/maximalInteger at every positive real price, with no exponent
or prime cap. Both endpoints keep the original strict Robin target.

The final identity is an existing factorization application kept local here.
It is not claimed as new escape content or as a proof of its positive sign.
The uniform 7/(2 sqrt u) estimate has no cutoff hypothesis on the price. -/
theorem original_endpoint_prime_tail_supply {q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q) :
    (∑ p ∈ N.primeFactors, lowerPrice q p) ≤ tail N ∧
      tail N ≤ (∑ p ∈ N.primeFactors, upperPrice q p) ∧
      0 ≤ tail N ∧ tail N ≤ (7 / 2 : ℝ) / Real.sqrt (largestPrime N) ∧
      robinLogMargin N = Mertens.E₃ (largestPrime N) + tail N +
        Real.log (Real.log (Real.log N)) - Real.log (Real.log (largestPrime N)) := by
  classical
  have hpositive : 1 ≤ N := by
    rcases hN with rfl | rfl
    · exact strictInteger_pos hq
    · exact (maximalInteger_spec hq).1
  have hactive (p : ℕ) (hp : p ∈ N.primeFactors) : 1 ≤ N.factorization p := by
    have hz : N.factorization p ≠ 0 := by
      apply Finsupp.mem_support_iff.mp
      simpa only [Nat.support_factorization] using hp
    omega
  have hlocal (p : ℕ) (hp : p ∈ N.primeFactors) :=
    endpoint_local hq hN (Nat.prime_of_mem_primeFactors hp) (hactive p hp)
  have hlow : (∑ p ∈ N.primeFactors, lowerPrice q p) ≤ tail N :=
    sum_le_sum fun p hp => (hlocal p hp).2.1
  have hupp : tail N ≤ (∑ p ∈ N.primeFactors, upperPrice q p) :=
    sum_le_sum fun p hp => (hlocal p hp).2.2.1
  have hnonneg : 0 ≤ tail N := sum_nonneg fun p hp => (hlocal p hp).1
  have htail : tail N ≤ (7 / 2 : ℝ) / Real.sqrt (largestPrime N) := by
    by_cases hne : N.primeFactors.Nonempty
    · let S := N.primeFactors
      let u := S.sup id
      obtain ⟨v, hv, hvu⟩ := exists_mem_eq_sup S hne id
      have huS : u ∈ S := by
        have heq : u = v := hvu
        exact heq.symm ▸ hv
      have huPrime : u.Prime := Nat.prime_of_mem_primeFactors huS
      have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast huPrime.two_le
      have hu0 : (0 : ℝ) < u := by linarith
      have hr0 : 0 < Real.sqrt (u : ℝ) := Real.sqrt_pos.mpr hu0
      have hmax (p : ℕ) (hp : p ∈ S) : p ≤ u := le_sup (f := id) hp
      have hprice : q * Real.log (u : ℝ) ≤ Real.log (1 + 1 / (u : ℝ)) := by
        have h := (endpoint_bracket hq hN huPrime (hactive u huS)).2.2
        have huLog : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast huPrime.one_lt)
        rw [D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone.golden_layer_marginal_one_eq_log_one_add_inv huPrime,
          le_div_iff₀ huLog] at h
        exact h
      by_cases hu4 : (4 : ℝ) ≤ u
      · let r := Real.sqrt (u : ℝ)
        let small := S.filter (fun p : ℕ => (p : ℝ) ≤ r)
        let large := S.filter (fun p : ℕ => r < (p : ℝ))
        have hr : 0 < r := hr0
        have hs_sub : small ⊆ Ioc 0 ⌊r⌋₊ := by
          intro p hp
          obtain ⟨hpS, hpr⟩ := mem_filter.mp hp
          exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primeFactors hpS).pos, Nat.le_floor hpr⟩
        have hcard : (small.card : ℝ) ≤ r := by
          calc
            (small.card : ℝ) ≤ ((Ioc 0 ⌊r⌋₊).card : ℝ) := by
              exact_mod_cast card_le_card hs_sub
            _ = (⌊r⌋₊ : ℝ) := by simp
            _ ≤ r := Nat.floor_le hr.le
        have hsmall : (∑ p ∈ small, layerTail N p) ≤ 1 / r := by
          have hs := sum_le_card_nsmul small (layerTail N) (1 / (u : ℝ)) (by
            intro p hp
            obtain ⟨hpS, hpr⟩ := mem_filter.mp hp
            exact endpoint_small hq hN (Nat.prime_of_mem_primeFactors hpS)
              (hactive p hpS) hu0 hprice hpr)
          rw [nsmul_eq_mul] at hs
          calc
            _ ≤ (small.card : ℝ) * (1 / (u : ℝ)) := hs
            _ ≤ r * (1 / (u : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = 1 / r := by
              have hsq : r^2 = (u : ℝ) := Real.sq_sqrt hu0.le
              field_simp [hr.ne', hu0.ne']
              nlinarith
        -- Generic square summation is imported; no lcm tail is reproved.
        let K := ⌊r⌋₊ + 1
        have hK1 : 1 ≤ K := by dsimp [K]; omega
        have hrK : r ≤ (K : ℝ) := by
          dsimp [K]
          simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one r).le
        have hKp (p : ℕ) (hp : p ∈ large) : K ≤ p := by
          have hpr := (mem_filter.mp hp).2
          have := (Nat.floor_lt hr.le).2 hpr
          dsimp [K]
          omega
        have hshift : (∑ p ∈ large, 1 / (p : ℝ)^2) =
            ∑ k ∈ large.image (fun p => p - K), 1 / ((k + K : ℕ) : ℝ)^2 := by
          rw [sum_image (by
            intro p hp t ht heq
            have := hKp p hp
            have := hKp t ht
            change p - K = t - K at heq
            omega)]
          apply sum_congr rfl
          intro p hp
          rw [Nat.sub_add_cancel (hKp p hp)]
        have hsum : Summable (fun k : ℕ => 1 / ((k + K : ℕ) : ℝ)^2) := by
          simpa only [Nat.cast_add] using
            (summable_nat_add_iff K).mpr
              (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
        have hlarge_sq : (∑ p ∈ large, 1 / (p : ℝ)^2) ≤ 2 / r := by
          rw [hshift]
          calc
            _ ≤ ∑' k : ℕ, 1 / ((k + K : ℕ) : ℝ)^2 :=
              hsum.sum_le_tsum _ (by intro k hk; positivity)
            _ ≤ 2 / (K : ℝ) := by
              simpa only [Nat.cast_add] using
                (Mertens.sum_one_div_sq_le (N := (K : ℝ)) (by exact_mod_cast hK1))
            _ ≤ 2 / r := by
              exact div_le_div_of_nonneg_left (by norm_num) hr hrK
        have hlarge : (∑ p ∈ large, layerTail N p) ≤ (5 / 2 : ℝ) / r := by
          calc
            _ ≤ ∑ p ∈ large, (5 / 4 : ℝ) / (p : ℝ)^2 :=
              sum_le_sum fun p hp => (hlocal p (mem_filter.mp hp).1).2.2.2.2
            _ = (5 / 4 : ℝ) * ∑ p ∈ large, 1 / (p : ℝ)^2 := by
              rw [mul_sum]
              apply sum_congr rfl
              intro p hp
              ring
            _ ≤ (5 / 4 : ℝ) * (2 / r) :=
              mul_le_mul_of_nonneg_left hlarge_sq (by norm_num)
            _ = (5 / 2 : ℝ) / r := by ring
        have hsplit : tail N = (∑ p ∈ small, layerTail N p) +
            ∑ p ∈ large, layerTail N p := by
          have h := sum_filter_add_sum_filter_not S
            (fun p : ℕ => (p : ℝ) ≤ r) (layerTail N)
          simpa only [tail, S, small, large, not_le] using h.symm
        change tail N ≤ (7 / 2 : ℝ) / r
        rw [hsplit]
        calc
          _ ≤ 1 / r + (5 / 2 : ℝ) / r := add_le_add hsmall hlarge
          _ = (7 / 2 : ℝ) / r := by ring
      · have huSmall : u ≤ 3 := by
          have huNat : u < 4 := by exact_mod_cast (show (u : ℝ) < 4 by linarith)
          omega
        have hsub : S ⊆ ({2, 3} : Finset ℕ) := by
          intro p hp
          have hpPrime := Nat.prime_of_mem_primeFactors hp
          have hpge := hpPrime.two_le
          have hple := (hmax p hp).trans huSmall
          simp only [mem_insert, mem_singleton]
          omega
        have hsmall : tail N ≤ (65 / 144 : ℝ) := by
          calc
            tail N ≤ ∑ p ∈ S, (5 / 4 : ℝ) / (p : ℝ)^2 :=
              sum_le_sum fun p hp => (hlocal p hp).2.2.2.2
            _ ≤ ∑ p ∈ ({2, 3} : Finset ℕ), (5 / 4 : ℝ) / (p : ℝ)^2 := by
              apply sum_le_sum_of_subset_of_nonneg hsub
              intro p hp hnot
              positivity
            _ = (65 / 144 : ℝ) := by norm_num
        have hrle : Real.sqrt (u : ℝ) ≤ 2 := by
          have huR : (u : ℝ) ≤ 3 := by exact_mod_cast huSmall
          nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg (u : ℝ)]
        change tail N ≤ (7 / 2 : ℝ) / Real.sqrt (u : ℝ)
        exact hsmall.trans ((le_div_iff₀ hr0).2 (by nlinarith))
    · have hempty : N.primeFactors = ∅ := not_nonempty_iff_eq_empty.mp hne
      simp [tail, largestPrime, hempty]
  have hW := log_sigma_div_eq_eulerMass_sub_tail hpositive
  -- All first-layer support gaps are closed by the existing prime-antitone
  -- theorem. This connects Mertens to this SAME integer, not to an lcm.
  have hprefix : N.primeFactors = (Ioc 0 (largestPrime N)).filter Nat.Prime := by
    ext p
    constructor
    · intro hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hp).pos, le_sup (f := id) hp⟩,
        Nat.prime_of_mem_primeFactors hp⟩
    · intro hp
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
      have hpu := (mem_Ioc.mp hpI).2
      by_cases hne : N.primeFactors.Nonempty
      · obtain ⟨v, hv, hvu⟩ := exists_mem_eq_sup N.primeFactors hne id
        have huMem : largestPrime N ∈ N.primeFactors := by
          have heq : largestPrime N = v := hvu
          exact heq.symm ▸ hv
        by_cases heq : p = largestPrime N
        · simpa only [heq] using huMem
        · have hlt : p < largestPrime N := by omega
          have huPrime := Nat.prime_of_mem_primeFactors huMem
          have hprice := (endpoint_bracket hq hN huPrime
            (hactive _ huMem)).2.2
          have hgain : q < goldenLayerMarginal p 1 :=
            hprice.trans_lt
              (D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime.golden_layer_marginal_one_strictAnti
                hpp huPrime hlt)
          have hfac : 1 ≤ N.factorization p := by
            rcases hN with rfl | rfl
            · exact (strict_layer_iff hq hpp (by omega)).mpr hgain
            · exact (weak_layer_iff hq hpp (by omega)).mpr hgain.le
          rw [← Nat.support_factorization, Finsupp.mem_support_iff]
          omega
      · have hempty : N.primeFactors = ∅ := not_nonempty_iff_eq_empty.mp hne
        have hu0 : largestPrime N = 0 := by simp [largestPrime, hempty]
        rw [hu0] at hpu
        have := hpp.two_le
        omega
  have hE : Mertens.E₃ (largestPrime N) = -eulerMass N +
      Real.log (Real.log (largestPrime N)) + Real.eulerMascheroniConstant := by
    unfold Mertens.E₃ eulerMass
    rw [Nat.floor_natCast, ← hprefix]
    simp only [one_div, sum_neg_distrib]
    ring
  refine ⟨hlow, hupp, hnonneg, htail, ?_⟩
  rw [robinLogMargin, hW, hE]
  ring

private theorem layer_tail_nonneg (m : ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ layerTail m p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hi1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have hz : (p : ℝ)⁻¹ ^ (m.factorization p + 1) < 1 :=
    pow_lt_one₀ hi0.le hi1 (by omega)
  unfold layerTail
  apply neg_nonneg.mpr
  have hlog := Real.log_le_log (sub_pos.mpr hz)
    (show 1 - (p : ℝ)⁻¹ ^ (m.factorization p + 1) ≤ 1 by
      linarith [pow_nonneg hi0.le (m.factorization p + 1)])
  simpa only [Real.log_one] using hlog

/-- The complete actual tail is nonnegative and gives the exact original
Robin-margin identity on literal initial prime support. -/
theorem tail_robin_data {m : ℕ} (hm : 0 < m)
    (hsupport : m.primeFactors = Nat.primesLE (largestPrime m)) :
    0 ≤ tail m ∧
      robinLogMargin m = Mertens.E₃ (largestPrime m) + tail m +
        Real.log (Real.log (Real.log (m : ℝ))) -
        Real.log (Real.log (largestPrime m)) := by
  have hnonneg : 0 ≤ tail m :=
    sum_nonneg fun p hp => layer_tail_nonneg m (Nat.prime_of_mem_primeFactors hp)
  have hprefix : m.primeFactors =
      (Finset.Ioc 0 (largestPrime m)).filter Nat.Prime := by
    simpa only [Nat.primesLE_eq_filter_Ioc_zero] using hsupport
  have hE : Mertens.E₃ (largestPrime m : ℝ) = -eulerMass m +
      Real.log (Real.log (largestPrime m : ℝ)) + Real.eulerMascheroniConstant := by
    unfold Mertens.E₃ eulerMass
    rw [Nat.floor_natCast, ← hprefix]
    simp only [one_div, sum_neg_distrib]
    ring
  have hW := log_sigma_div_eq_eulerMass_sub_tail hm
  refine ⟨hnonneg, ?_⟩
  rw [robinLogMargin, hW, hE]
  ring

/-! A finite same-integer correction.  The support hypothesis is deliberately
separate from the optimizer endpoint hypothesis above: it is the exact
finite bridge used later by an actual-record consumer. -/
theorem finite_min_tail_robin_bound {m : ℕ} (hm : 0 < m)
    (hsupport : m.primeFactors = Nat.primesLE (largestPrime m))
    (htheta : 1 < Chebyshev.theta (largestPrime m)) :
    (∑ p ∈ m.primeFactors, min
        (Real.log p / (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))))
        (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))) ≤
      tail m + Real.log (Real.log (Real.log (m : ℝ))) -
        Real.log (Real.log (Chebyshev.theta (largestPrime m))) ∧
    (∑ p ∈ m.primeFactors, min
        (Real.log p / (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))))
        (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))) +
        Mertens.E₃ (largestPrime m) +
        Real.log (Real.log (Chebyshev.theta (largestPrime m))) -
        Real.log (Real.log (largestPrime m)) ≤ robinLogMargin m := by
  classical
  let P : ℕ := largestPrime m
  let X : ℝ := Real.log (m : ℝ)
  let Q : ℝ := ∑ p ∈ m.primeFactors,
    ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p
  have hsplit : X = Chebyshev.theta (P : ℝ) + Q := by
    dsimp [X, P, Q]
    rw [Chebyshev.theta_eq_sum_primesLE_log, ← hsupport]
    exact D5.S3.Arith.Robin.EulerLayerInventoryGrowth.log_factorization_split hm
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    exact sum_nonneg (fun p hp =>
      mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))
  have hX : 1 < X := by linarith [hsplit, htheta, hQnonneg]
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hden : 0 < X * Real.log X := mul_pos hX0 hlogX
  have hD : Q / (X * Real.log X) ≤
      Real.log (Real.log X) - Real.log (Real.log (Chebyshev.theta (P : ℝ))) := by
    by_cases heq : X = Chebyshev.theta (P : ℝ)
    · have hQzero : Q = 0 := by linarith [hsplit]
      rw [hQzero, heq]
      simp
    · have ht := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
        (x := X) (y := Chebyshev.theta (P : ℝ)) hX htheta heq
      have ht' : Real.log (Real.log (Chebyshev.theta (P : ℝ))) -
          Real.log (Real.log X) <
          (Chebyshev.theta (P : ℝ) - X) / (X * Real.log X) := by
        simpa [D5.S3.Arith.Robin.ActualRobinClockCovariance.g,
          div_eq_mul_inv] using ht
      have hrewrite : (Chebyshev.theta (P : ℝ) - X) / (X * Real.log X) =
          -Q / (X * Real.log X) := by rw [hsplit]; ring
      rw [hrewrite] at ht'
      have ht''' : Real.log (Real.log (Chebyshev.theta (P : ℝ))) -
          Real.log (Real.log X) < -(Q / (X * Real.log X)) := by
        simpa only [neg_div] using ht'
      have ht'' : Q / (X * Real.log X) <
          Real.log (Real.log X) - Real.log (Real.log (Chebyshev.theta (P : ℝ))) := by
        linarith only [ht''']
      exact ht''.le
  have hterm (p : ℕ) (hp : p ∈ m.primeFactors) :
      min (Real.log p / (X * Real.log X))
          (-Real.log (1 - (p : ℝ)⁻¹ ^ 2)) ≤
        layerTail m p +
          (((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) /
            (X * Real.log X) := by
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hv : 1 ≤ m.factorization p := by
      exact hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    have htail : 0 ≤ layerTail m p := layer_tail_nonneg m hpp
    by_cases hv1 : m.factorization p = 1
    · have htail1 : layerTail m p = -Real.log (1 - (p : ℝ)⁻¹ ^ 2) := by
        simp [layerTail, hv1]
      have hqzero : (((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) /
          (X * Real.log X) = 0 := by simp [hv1]
      rw [htail1, hqzero]
      simpa using (min_le_right (Real.log p / (X * Real.log X))
        (-Real.log (1 - (p : ℝ)⁻¹ ^ 2)))
    · have hv2 : 2 ≤ m.factorization p := by omega
      have hcoef : (1 : ℝ) ≤ ((m.factorization p - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ m.factorization p - 1 by omega)
      have hq : Real.log p / (X * Real.log X) ≤
          (((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) /
            (X * Real.log X) := by
        apply (div_le_div_iff₀ hden hden).2
        have hcoeflog : Real.log p ≤
            ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p := by
          calc
            Real.log p = 1 * Real.log p := by ring
            _ ≤ ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p :=
              mul_le_mul_of_nonneg_right hcoef (Real.log_natCast_nonneg p)
        exact mul_le_mul_of_nonneg_right hcoeflog hden.le
      exact (min_le_left _ _).trans (by linarith)
  have hsum :
      (∑ p ∈ m.primeFactors, min
        (Real.log p / (X * Real.log X))
        (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))) ≤
      tail m + Q / (X * Real.log X) := by
    calc
      _ ≤ ∑ p ∈ m.primeFactors,
          (layerTail m p +
            (((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) /
              (X * Real.log X)) :=
        sum_le_sum (fun p hp => hterm p hp)
      _ = tail m + Q / (X * Real.log X) := by
        rw [sum_add_distrib, ← Finset.sum_div]
        rfl
  have hV :
      (∑ p ∈ m.primeFactors, min
        (Real.log p / (X * Real.log X))
        (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))) ≤
      tail m + Real.log (Real.log X) -
        Real.log (Real.log (Chebyshev.theta (P : ℝ))) := by
    exact hsum.trans (by
      have hadd := add_le_add_left hD (tail m)
      convert hadd using 1 <;> ring)
  have hmargin := (tail_robin_data hm hsupport).2
  refine ⟨?_, ?_⟩
  · simpa [X, P] using hV
  · have hmargin' := hmargin
    simpa [X, P] using (show
      (∑ p ∈ m.primeFactors, min
        (Real.log p / (X * Real.log X))
        (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))) +
        Mertens.E₃ (P : ℝ) + Real.log (Real.log (Chebyshev.theta (P : ℝ))) -
        Real.log (Real.log (P : ℝ)) ≤ robinLogMargin m by
      linarith [hV, hmargin])
/-!
The first-layer exact replacement, firstLayerTail, secondOmitted,
firstLayerLower, higherLayerRemainder, and the complete
first_layer_lower_control / original_endpoint_first_layer_lower_supply
assertions and proofs are retained as transient source evidence in
transient/OriginalEndpointPrimeTail.pre-repair.lean and the extracted block.
They are not canonical declarations in this overlay: the original full-price
supplier above remains the sole retained supplier and keeps every prime, layer,
tie, endpoint, sharp-price, adaptive-support, and 7/(2*sqrt u) assertion.
-/

end D5.S3.Arith.Robin.OriginalEndpointPrimeTail
