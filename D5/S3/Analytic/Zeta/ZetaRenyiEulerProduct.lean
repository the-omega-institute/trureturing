/- GID: D5/S3/Analytic/Zeta/ZetaRenyiEulerProduct
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Renyi entropy of the zeta law decomposes over primes. -/

import Mathlib
/- Provenance: Native proof over pinned mathlib. -/
import D5.S3.Analytic.Zeta.EulerLogBridge
import D5.S3.Analytic.Zeta.ZetaRenyiEntropy

/-!
Search receipt (2026-08-23): repository searches for `countableRenyiEntropy`,
`primeExponent`, `tsum_prime`, and geometric power sums found the countable Renyi definition and
zeta closed form in `ZetaRenyiEntropy.lean`, the geometric prime marginal and Shannon-family
summability in `PrimeMarginalEntropy.lean`, and the reusable logarithmic Euler product in
`EulerLogBridge.lean`.  No existing Renyi prime decomposition or local Renyi closed form was found.
The pinned mathlib search for `Renyi`, `entropy.*PMF`, `rpow.*geometric`, and `geometric.*rpow`
found no Renyi entropy API; the only Renyi occurrence concerns Erdos-Renyi graphs.  The proof below
uses mathlib's ordinary geometric-series theorems after rewriting real powers pointwise.

The proof takes the closed-form route.  Each local entropy is a linear combination of the Euler-log
terms at `s` and `alpha * s`; their prime sums are then identified by
`log_partitionFunction_eq_tsum_prime`.  No independence theorem or exchange of double series is
needed.  The local Euler-log summability needed to justify every `tsum` rewrite is derived from the
already-public Shannon result `summable_primeExponent_entropy`, rather than reproving the private
majorization internal to `EulerLogBridge.lean`.
-/

namespace D5.S3.Analytic.Zeta.ZetaRenyiEulerProduct

open scoped ENNReal BigOperators
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy
open D5.S3.Analytic.Zeta.EulerLogBridge

noncomputable section

private lemma primeExponent_renyi_power_pointwise (s alpha : ℝ) (hs : 1 < s)
    (p : Nat.Primes) (k : ℕ) :
    (pmfReal (primeExponentPMF s hs p) k) ^ alpha =
      (1 - (p.1 : ℝ) ^ (-s)) ^ alpha *
        (((p.1 : ℝ) ^ (-s)) ^ alpha) ^ k := by
  have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hq0 : 0 < (p.1 : ℝ) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hq1 : (p.1 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have hpow : (p.1 : ℝ) ^ (-(k : ℝ) * s) = ((p.1 : ℝ) ^ (-s)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    ring
  rw [primeExponentPMF_apply, hpow,
    Real.mul_rpow (sub_pos.mpr hq1).le (pow_nonneg hq0.le k),
    ← Real.rpow_pow_comm hq0.le alpha k]

private lemma primeExponent_renyi_power_sum (s alpha : ℝ) (hs : 1 < s)
    (halpha : 0 < alpha) (p : Nat.Primes) :
    ∑' k, (pmfReal (primeExponentPMF s hs p) k) ^ alpha =
      (1 - (p.1 : ℝ) ^ (-s)) ^ alpha /
        (1 - (p.1 : ℝ) ^ (-(alpha * s))) := by
  have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hq0 : 0 < (p.1 : ℝ) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hq1 : (p.1 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have hqa0 : 0 < ((p.1 : ℝ) ^ (-s)) ^ alpha := Real.rpow_pos_of_pos hq0 _
  have hqa1 : ((p.1 : ℝ) ^ (-s)) ^ alpha < 1 := Real.rpow_lt_one hq0.le hq1 halpha
  have habs : ‖((p.1 : ℝ) ^ (-s)) ^ alpha‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqa0]
    exact hqa1
  have hgeom : Summable (fun k : ℕ ↦ (((p.1 : ℝ) ^ (-s)) ^ alpha) ^ k) :=
    summable_geometric_of_norm_lt_one habs
  rw [show (fun k ↦ (pmfReal (primeExponentPMF s hs p) k) ^ alpha) =
      fun k : ℕ ↦ (1 - (p.1 : ℝ) ^ (-s)) ^ alpha *
        (((p.1 : ℝ) ^ (-s)) ^ alpha) ^ k by
    funext k
    exact primeExponent_renyi_power_pointwise s alpha hs p k]
  rw [hgeom.tsum_mul_left, tsum_geometric_of_norm_lt_one habs]
  have hscale : ((p.1 : ℝ) ^ (-s)) ^ alpha =
      (p.1 : ℝ) ^ (-(alpha * s)) := by
    rw [← Real.rpow_mul hp0.le]
    congr 1
    ring
  rw [hscale, div_eq_mul_inv]

/-- Closed form for the Renyi entropy of one prime-exponent coordinate.

`1 < s` constructs the zeta prime marginal and puts its geometric ratio in `(0, 1)`.
`0 < alpha` is exactly what makes the powered ratio geometric with ratio below one; no
`alpha != 1` assumption is needed because both sides are the same totalized zero at order one. -/
theorem primeExponent_renyi_entropy_eq (s alpha : ℝ) (hs : 1 < s) (halpha : 0 < alpha)
    (p : Nat.Primes) :
    countableRenyiEntropy alpha (primeExponentPMF s hs p) =
      (1 / (1 - alpha)) *
        (-Real.log (1 - (p.1 : ℝ) ^ (-(alpha * s))) -
          alpha * (-Real.log (1 - (p.1 : ℝ) ^ (-s)))) := by
  have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hq1 : (p.1 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have hqa1 : (p.1 : ℝ) ^ (-(alpha * s)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by
      exact neg_neg_of_pos (mul_pos halpha (zero_lt_one.trans hs)))
  rw [countableRenyiEntropy, primeExponent_renyi_power_sum s alpha hs halpha p,
    Real.log_div (Real.rpow_pos_of_pos (sub_pos.mpr hq1) alpha).ne'
      (sub_pos.mpr hqa1).ne',
    Real.log_rpow (sub_pos.mpr hq1)]
  ring

private lemma summable_prime_eulerLog_from_entropy (t : ℝ) (ht : 1 < t) :
    Summable (fun p : Nat.Primes ↦ -Real.log (1 - (p.1 : ℝ) ^ (-t))) := by
  apply Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    (summable_primeExponent_entropy t ht)
  · have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
    have hq0 : 0 < (p.1 : ℝ) ^ (-t) := Real.rpow_pos_of_pos hp0 _
    have hq1 : (p.1 : ℝ) ^ (-t) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
    exact neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr hq1).le (sub_le_self 1 hq0.le))
  · rw [primeExponent_entropy_eq]
    have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
    have hq0 : 0 < (p.1 : ℝ) ^ (-t) := Real.rpow_pos_of_pos (zero_lt_one.trans hpR) _
    have hq1 : (p.1 : ℝ) ^ (-t) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by linarith) (Real.log_pos hpR).le)
      (div_nonneg hq0.le (sub_pos.mpr hq1).le))

/-- The family of Renyi entropies of the zeta law's prime coordinates is summable.

`1 < s` constructs the marginals and supplies Euler-log summability at `s`.
`1 < alpha * s` implies `0 < alpha` and supplies Euler-log summability at the powered exponent.
There is no order-one exclusion: when `alpha = 1` the displayed family is identically zero and is
therefore genuinely summable, rather than relying on `tsum`'s nonsummable totalization. -/
theorem summable_primeExponent_renyiEntropy (s alpha : ℝ) (hs : 1 < s)
    (halpha_s : 1 < alpha * s) :
    Summable (fun p : Nat.Primes ↦
      countableRenyiEntropy alpha (primeExponentPMF s hs p)) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have halpha : 0 < alpha := pos_of_mul_pos_left (zero_lt_one.trans halpha_s) hs0.le
  have hAs := summable_prime_eulerLog_from_entropy (alpha * s) halpha_s
  have hS := summable_prime_eulerLog_from_entropy s hs
  have hcomb := hAs.sub (hS.mul_left alpha)
  apply (hcomb.mul_left (1 / (1 - alpha))).congr
  intro p
  exact (primeExponent_renyi_entropy_eq s alpha hs halpha p).symm

/-- The Renyi entropy of the zeta law is the sum of the Renyi entropies of its prime coordinates.

`1 < s` constructs the zeta law and licenses the logarithmic Euler product at `s`.
`1 < alpha * s` both proves the local family summable and licenses the same Euler product at the
powered exponent.  No `alpha != 1` hypothesis is present: order one is proved in a separate branch,
where the repository's totalized definition makes the global entropy and every local entropy
simplify to zero; the public summability theorem above ensures the right-hand `tsum` is still
meaningful there. -/
theorem countableRenyiEntropy_zeta_eq_tsum_prime (s alpha : ℝ) (hs : 1 < s)
    (halpha_s : 1 < alpha * s) :
    countableRenyiEntropy alpha (zetaDist s hs) =
      ∑' p : Nat.Primes, countableRenyiEntropy alpha (primeExponentPMF s hs p) := by
  by_cases halpha_one : alpha = 1
  · subst alpha
    simp [countableRenyiEntropy]
  have hs0 : 0 < s := zero_lt_one.trans hs
  have halpha : 0 < alpha := pos_of_mul_pos_left (zero_lt_one.trans halpha_s) hs0.le
  have hZs : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
  have hZas : 0 < (riemannZeta ((alpha * s : ℝ) : ℂ)).re :=
    riemannZeta_re_pos_of_one_lt halpha_s
  have hAs := summable_prime_eulerLog_from_entropy (alpha * s) halpha_s
  have hS := summable_prime_eulerLog_from_entropy s hs
  have hcomb := hAs.sub (hS.mul_left alpha)
  rw [zeta_renyi_entropy_eq s alpha hs halpha_one halpha_s,
    Real.log_div hZas.ne' (Real.rpow_pos_of_pos hZs alpha).ne', Real.log_rpow hZs]
  simp_rw [primeExponent_renyi_entropy_eq s alpha hs halpha]
  rw [hcomb.tsum_mul_left, hAs.tsum_sub (hS.mul_left alpha), hS.tsum_mul_left]
  rw [← log_partitionFunction_eq_tsum_prime (alpha * s) halpha_s,
    ← log_partitionFunction_eq_tsum_prime s hs,
    partition_toReal_eq_zeta_re (alpha * s) halpha_s,
    partition_toReal_eq_zeta_re s hs]

end

end D5.S3.Analytic.Zeta.ZetaRenyiEulerProduct
