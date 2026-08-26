/- GID: D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeta log evidence sums over primes, vanishes diagonally, and strictly accumulates. -/

import D5.S3.Analytic.ZetaMinEntropy.PrimeDecomposition
import D5.S3.Divergence.StrictGibbs
import Mathlib.NumberTheory.SumPrimeReciprocals

/- Library-search audit trail (2026-08-25):
   * Repository exact hit `primeExponentPMF` is the single source for each zeta
     prime-exponent marginal; no second marginal or countable KL definition is introduced.
   * Exact hits `expectedLog_eq_tsum_prime` and
     `log_partitionFunction_eq_tsum_prime` provide the two infinite prime bridges.
   * Exact hits `summable_primeExponent_entropy` and
     `summable_primeExponent_minEntropy` prove the local energy family is summable.
   * Exact hit `kl_divergence_pos_of_ne` supplies strict finite Gibbs positivity; it is
     applied to the Bernoulli sufficient statistic of a geometric channel.
   * Repository and pinned-Mathlib searches for geometric KL, countable PMF KL, zeta
     likelihood ratios, and prime-channel log evidence found no equivalent declaration.
   * `Nat.Primes.not_summable_one_div` and `tsum_eq_zero_of_not_summable` provide the
     explicit contrast showing why a bare `tsum` must not represent divergent evidence.
   * Every imported repository module is tagged `I`, so this module is also tagged `I`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.PrimeChannelLogEvidence

open scoped BigOperators
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.EulerLogBridge
open D5.S3.Analytic.ZetaMinEntropy.PrimeDecomposition
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.StrictGibbs

noncomputable section

/-!
The source's first sentence is formalized as expected log-likelihood evidence. The local
definition is the KL expression for one geometric prime-exponent marginal, and the global
definition is the same expression for the zeta law on positive integers.

The source's second sentence, "mathematical additivity does not imply independence of real
experimental sources", is interpretive. 此句为解读警告,不构成可形式化命题: no real
experiment, source object, or independence predicate is specified. This is not an
out-of-scope theorem missing prerequisites; the sentence itself makes no mathematical claim.

Repository `klDivergence` and `Real.log` are real-valued total functions. In particular,
division by zero and `Real.log 0` are totalized, so a zero-denominator term is not extended-real
infinity. The present zeta ratios are positive on their intended support. At `n = 0`, both zeta
masses vanish and the totalized term is zero; no extended-real divergence claim is made.
-/

/-- Expected log-likelihood evidence supplied by prime `p` for parameter `s` against `t`. -/
def primeChannelLogEvidence
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) (p : Nat.Primes) : Real :=
  ∑' k : Nat, pmfReal (primeExponentPMF s hs p) k *
    Real.log
      (pmfReal (primeExponentPMF s hs p) k /
        pmfReal (primeExponentPMF t ht p) k)

/-- Expected global log-likelihood evidence in the zeta family. -/
def zetaFamilyLogEvidence
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) : Real :=
  ∑' n : Nat, pmfReal (zetaDist s hs) n *
    Real.log (pmfReal (zetaDist s hs) n / pmfReal (zetaDist t ht) n)

private lemma prime_pmf_geometric
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (k : Nat) :
    pmfReal (primeExponentPMF s hs p) k =
      (1 - (p.1 : Real) ^ (-s)) * ((p.1 : Real) ^ (-s)) ^ k := by
  rw [primeExponentPMF_apply]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- One prime channel has the closed geometric KL formula. -/
theorem primeChannelLogEvidence_eq
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) (p : Nat.Primes) :
    primeChannelLogEvidence s hs t ht p =
      Real.log
          ((1 - (p.1 : Real) ^ (-s)) / (1 - (p.1 : Real) ^ (-t))) +
        (t - s) * Real.log p.1 *
          ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s))) := by
  let q : Real := (p.1 : Real) ^ (-s)
  let r : Real := (p.1 : Real) ^ (-t)
  let P : PMF Nat := primeExponentPMF s hs p
  let Q : PMF Nat := primeExponentPMF t ht p
  have hp : 1 < (p.1 : Real) := by exact_mod_cast p.2.one_lt
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hP (k : Nat) : pmfReal P k = (1 - q) * q ^ k := by
    exact prime_pmf_geometric s hs p k
  have hQ (k : Nat) : pmfReal Q k = (1 - r) * r ^ k := by
    exact prime_pmf_geometric t ht p k
  have hlogRatio (k : Nat) :
      Real.log (pmfReal P k / pmfReal Q k) =
        Real.log ((1 - q) / (1 - r)) +
          (k : Real) * ((t - s) * Real.log p.1) := by
    rw [hP, hQ]
    have hqk : 0 < q ^ k := pow_pos hq0 _
    have hrk : 0 < r ^ k := pow_pos hr0 _
    rw [Real.log_div (mul_pos (sub_pos.mpr hq1) hqk).ne'
      (mul_pos (sub_pos.mpr hr1) hrk).ne']
    rw [Real.log_mul (sub_pos.mpr hq1).ne' hqk.ne',
      Real.log_mul (sub_pos.mpr hr1).ne' hrk.ne', Real.log_pow, Real.log_pow]
    rw [Real.log_div (sub_pos.mpr hq1).ne' (sub_pos.mpr hr1).ne']
    dsimp [q, r]
    rw [Real.log_rpow (by positivity : 0 < (p.1 : Real)),
      Real.log_rpow (by positivity : 0 < (p.1 : Real))]
    ring
  have hqNorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hweightedGeom : Summable (fun k : Nat => (k : Real) * q ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hqNorm).summable
  have hweighted : Summable (fun k : Nat => (k : Real) * pmfReal P k) := by
    apply (hweightedGeom.mul_left (1 - q)).congr
    intro k
    rw [hP]
    ring
  have hweightedSum :
      ∑' k : Nat, (k : Real) * pmfReal P k = q / (1 - q) := by
    rw [show (fun k : Nat => (k : Real) * pmfReal P k) =
        fun k : Nat => (1 - q) * ((k : Real) * q ^ k) by
      funext k
      rw [hP]
      ring]
    rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hqNorm]
    field_simp [(sub_pos.mpr hq1).ne']
  let a : Real := Real.log ((1 - q) / (1 - r))
  let b : Real := (t - s) * Real.log p.1
  rw [primeChannelLogEvidence]
  change (∑' k : Nat, pmfReal P k * Real.log (pmfReal P k / pmfReal Q k)) = _
  calc
    (∑' k : Nat, pmfReal P k * Real.log (pmfReal P k / pmfReal Q k)) =
        ∑' k : Nat, (a * pmfReal P k + b * ((k : Real) * pmfReal P k)) := by
      apply tsum_congr
      intro k
      rw [hlogRatio]
      dsimp [a, b]
      ring
    _ = a * (∑' k : Nat, pmfReal P k) +
        b * (∑' k : Nat, (k : Real) * pmfReal P k) := by
      rw [(pmfReal_summable P).mul_left a |>.tsum_add (hweighted.mul_left b),
        tsum_mul_left, tsum_mul_left]
    _ = a + b * (q / (1 - q)) := by rw [tsum_pmfReal, hweightedSum, mul_one]
    _ = Real.log
          ((1 - (p.1 : Real) ^ (-s)) / (1 - (p.1 : Real) ^ (-t))) +
        (t - s) * Real.log p.1 *
          ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s))) := by
      rfl

#print axioms primeChannelLogEvidence_eq

/-- Global zeta evidence has the usual energy-plus-log-partition formula. -/
theorem zetaFamilyLogEvidence_eq
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) :
    zetaFamilyLogEvidence s hs t ht =
      (t - s) * expectedLog (zetaDist s hs) +
        Real.log (partitionFunction t).toReal -
          Real.log (partitionFunction s).toReal := by
  let P : PMF Nat := zetaDist s hs
  let Q : PMF Nat := zetaDist t ht
  let Zs : Real := (partitionFunction s).toReal
  let Zt : Real := (partitionFunction t).toReal
  have hPsum : Summable (pmfReal P) := pmfReal_summable P
  have hPlog : Summable (fun n : Nat => pmfReal P n * Real.log n) := by
    apply ((summable_log_weight s hs).mul_left Zs⁻¹).congr
    intro n
    dsimp [P, Zs]
    rw [zeta_real_apply]
    ring
  have hterm (n : Nat) :
      pmfReal P n * Real.log (pmfReal P n / pmfReal Q n) =
        (t - s) * (pmfReal P n * Real.log n) +
          (Real.log Zt - Real.log Zs) * pmfReal P n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [P, Q, pmfReal, zeta_dist_apply, weight_zero s (by linarith),
        weight_zero t (by linarith)]
    · have hPpos : 0 < pmfReal P n := zeta_real_pos s hs hn
      have hQpos : 0 < pmfReal Q n := zeta_real_pos t ht hn
      rw [Real.log_div hPpos.ne' hQpos.ne']
      rw [show Real.log (pmfReal P n) =
          -s * Real.log n - Real.log Zs by
        exact log_zeta_real s hs hn]
      rw [show Real.log (pmfReal Q n) =
          -t * Real.log n - Real.log Zt by
        exact log_zeta_real t ht hn]
      ring
  rw [zetaFamilyLogEvidence]
  change (∑' n : Nat, pmfReal P n * Real.log (pmfReal P n / pmfReal Q n)) = _
  simp_rw [hterm]
  rw [(hPlog.mul_left (t - s)).tsum_add
    (hPsum.mul_left (Real.log Zt - Real.log Zs))]
  rw [hPlog.tsum_mul_left, hPsum.tsum_mul_left, tsum_pmfReal]
  dsimp [expectedLog, P, Zs, Zt]
  ring

#print axioms zetaFamilyLogEvidence_eq

private lemma summable_prime_energy (s : Real) (hs : 1 < s) :
    Summable (fun p : Nat.Primes => Real.log p.1 *
      ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)))) := by
  let energy : Nat.Primes → Real := fun p => Real.log p.1 *
    ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)))
  let eulerLog : Nat.Primes → Real := fun p =>
    -Real.log (1 - (p.1 : Real) ^ (-s))
  have hEuler : Summable eulerLog :=
    (summable_primeExponent_minEntropy s hs).congr (fun p => by
      rw [primeExponent_min_entropy_eq])
  have hScaled : Summable (fun p => s * energy p) := by
    apply (summable_primeExponent_entropy s hs).sub hEuler |>.congr
    intro p
    rw [primeExponent_entropy_eq]
    dsimp [energy, eulerLog]
    ring
  exact (summable_mul_left_iff (ne_of_gt (lt_trans zero_lt_one hs))).mp hScaled

/-- The valid zeta parameter range itself proves summability of all channel evidences. -/
theorem summable_primeChannelLogEvidence
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) :
    Summable (fun p : Nat.Primes => primeChannelLogEvidence s hs t ht p) := by
  let energy : Nat.Primes → Real := fun p => Real.log p.1 *
    ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)))
  let eulerS : Nat.Primes → Real := fun p =>
    -Real.log (1 - (p.1 : Real) ^ (-s))
  let eulerT : Nat.Primes → Real := fun p =>
    -Real.log (1 - (p.1 : Real) ^ (-t))
  have hS : Summable eulerS :=
    (summable_primeExponent_minEntropy s hs).congr (fun p => by
      rw [primeExponent_min_entropy_eq])
  have hT : Summable eulerT :=
    (summable_primeExponent_minEntropy t ht).congr (fun p => by
      rw [primeExponent_min_entropy_eq])
  have hEnergy : Summable energy := summable_prime_energy s hs
  apply ((hT.sub hS).add (hEnergy.mul_left (t - s))).congr
  intro p
  rw [primeChannelLogEvidence_eq]
  have hsPos : 0 < 1 - (p.1 : Real) ^ (-s) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.2.one_lt) (by linarith))
  have htPos : 0 < 1 - (p.1 : Real) ^ (-t) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.2.one_lt) (by linarith))
  rw [Real.log_div hsPos.ne' htPos.ne']
  dsimp [energy, eulerS, eulerT]
  ring

#print axioms summable_primeChannelLogEvidence

/-- Total zeta evidence is exactly the sum of its prime-channel evidences. -/
theorem zetaFamilyLogEvidence_eq_tsum_prime
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) :
    zetaFamilyLogEvidence s hs t ht =
      ∑' p : Nat.Primes, primeChannelLogEvidence s hs t ht p := by
  let energy : Nat.Primes → Real := fun p => Real.log p.1 *
    ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)))
  let eulerS : Nat.Primes → Real := fun p =>
    -Real.log (1 - (p.1 : Real) ^ (-s))
  let eulerT : Nat.Primes → Real := fun p =>
    -Real.log (1 - (p.1 : Real) ^ (-t))
  have hEnergy : Summable energy := summable_prime_energy s hs
  have hS : Summable eulerS :=
    (summable_primeExponent_minEntropy s hs).congr (fun p => by
      rw [primeExponent_min_entropy_eq])
  have hT : Summable eulerT :=
    (summable_primeExponent_minEntropy t ht).congr (fun p => by
      rw [primeExponent_min_entropy_eq])
  rw [zetaFamilyLogEvidence_eq, expectedLog_eq_tsum_prime,
    log_partitionFunction_eq_tsum_prime t ht,
    log_partitionFunction_eq_tsum_prime s hs]
  change (t - s) * (∑' p, energy p) + (∑' p, eulerT p) -
      (∑' p, eulerS p) = ∑' p, primeChannelLogEvidence s hs t ht p
  rw [← hEnergy.tsum_mul_left (t - s)]
  calc
    (∑' p, (t - s) * energy p) + (∑' p, eulerT p) - (∑' p, eulerS p) =
        (∑' p, eulerT p) - (∑' p, eulerS p) +
          ∑' p, (t - s) * energy p := by ring
    _ = (∑' p, (eulerT p - eulerS p)) +
        ∑' p, (t - s) * energy p := by rw [hT.tsum_sub hS]
    _ = ∑' p, ((eulerT p - eulerS p) + (t - s) * energy p) :=
      ((hT.sub hS).tsum_add (hEnergy.mul_left (t - s))).symm
    _ = ∑' p, primeChannelLogEvidence s hs t ht p := by
      apply tsum_congr
      intro p
      rw [primeChannelLogEvidence_eq]
      have hsPos : 0 < 1 - (p.1 : Real) ^ (-s) := sub_pos.mpr
        (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast p.2.one_lt) (by linarith))
      have htPos : 0 < 1 - (p.1 : Real) ^ (-t) := sub_pos.mpr
        (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast p.2.one_lt) (by linarith))
      rw [Real.log_div hsPos.ne' htPos.ne']
      dsimp [energy, eulerS, eulerT]
      ring

#print axioms zetaFamilyLogEvidence_eq_tsum_prime

/-- Equal parameters have zero local evidence, zero total evidence, and zero prime sum. -/
theorem equal_parameters_have_zero_evidence (s : Real) (hs : 1 < s) :
    (∀ p : Nat.Primes, primeChannelLogEvidence s hs s hs p = 0) ∧
      zetaFamilyLogEvidence s hs s hs = 0 ∧
      (∑' p : Nat.Primes, primeChannelLogEvidence s hs s hs p) = 0 := by
  simp [primeChannelLogEvidence, zetaFamilyLogEvidence]

#print axioms equal_parameters_have_zero_evidence

/-- Distinct zeta parameters give strictly positive evidence in every prime channel. -/
theorem primeChannelLogEvidence_pos
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) (hst : s ≠ t)
    (p : Nat.Primes) :
    0 < primeChannelLogEvidence s hs t ht p := by
  let q : Real := (p.1 : Real) ^ (-s)
  let r : Real := (p.1 : Real) ^ (-t)
  let a : Bool → Real := fun bit => if bit then q else 1 - q
  let b : Bool → Real := fun bit => if bit then r else 1 - r
  have hp : 1 < (p.1 : Real) := by exact_mod_cast p.2.one_lt
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hqr : q ≠ r := by
    intro h
    have hneg : -s = -t := (Real.strictMono_rpow_of_base_gt_one hp).injective h
    exact hst (neg_injective hneg)
  have ha : (∀ bit, 0 ≤ a bit) ∧ ∑ bit, a bit = 1 := by
    constructor
    · intro bit
      fin_cases bit <;> simp [a, hq0.le, hq1.le]
    · simp [a]
  have hb : (∀ bit, 0 ≤ b bit) ∧ ∑ bit, b bit = 1 := by
    constructor
    · intro bit
      fin_cases bit <;> simp [b, hr0.le, hr1.le]
    · simp [b]
  have hac : ∀ bit, b bit = 0 → a bit = 0 := by
    intro bit hzero
    exfalso
    fin_cases bit
    · exact hr0.ne' (by simpa [b] using hzero)
    · exact (sub_pos.mpr hr1).ne' (by simpa [b] using hzero)
  have hab : a ≠ b := by
    intro h
    exact hqr (by simpa [a, b] using congrFun h true)
  have hkl : 0 < klDivergence a b := kl_divergence_pos_of_ne a b ha hb hac hab
  have hlogqr : Real.log (q / r) = (t - s) * Real.log p.1 := by
    rw [Real.log_div hq0.ne' hr0.ne']
    dsimp [q, r]
    rw [Real.log_rpow (by positivity : 0 < (p.1 : Real)),
      Real.log_rpow (by positivity : 0 < (p.1 : Real))]
    ring
  have hscaled :
      klDivergence a b = (1 - q) * primeChannelLogEvidence s hs t ht p := by
    rw [primeChannelLogEvidence_eq]
    rw [show (p.1 : Real) ^ (-s) = q by rfl,
      show (p.1 : Real) ^ (-t) = r by rfl]
    rw [← hlogqr]
    simp only [klDivergence]
    rw [Fintype.sum_bool]
    dsimp [a, b]
    field_simp [(sub_pos.mpr hq1).ne']
    ring
  rw [hscaled] at hkl
  rcases (mul_pos_iff.mp hkl) with hpos | hneg
  · exact hpos.2
  · exact (not_lt_of_ge (sub_pos.mpr hq1).le hneg.1).elim

#print axioms primeChannelLogEvidence_pos

/-- The channels at primes two and three are positive and their sum exceeds each one. -/
theorem two_three_channels_strictly_accumulate
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) (hst : s ≠ t) :
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    let p3 : Nat.Primes := ⟨3, Nat.prime_three⟩
    0 < primeChannelLogEvidence s hs t ht p2 ∧
      0 < primeChannelLogEvidence s hs t ht p3 ∧
      primeChannelLogEvidence s hs t ht p2 <
        primeChannelLogEvidence s hs t ht p2 + primeChannelLogEvidence s hs t ht p3 ∧
      primeChannelLogEvidence s hs t ht p3 <
        primeChannelLogEvidence s hs t ht p2 + primeChannelLogEvidence s hs t ht p3 := by
  dsimp
  have h2 := primeChannelLogEvidence_pos s hs t ht hst
    (⟨2, Nat.prime_two⟩ : Nat.Primes)
  have h3 := primeChannelLogEvidence_pos s hs t ht hst
    (⟨3, Nat.prime_three⟩ : Nat.Primes)
  exact ⟨h2, h3, by linarith, by linarith⟩

#print axioms two_three_channels_strictly_accumulate

/-- Parameter disequality is necessary for strict positivity, witnessed at `s = t = 2`. -/
theorem parameter_disequality_is_necessary :
    ¬ 0 < primeChannelLogEvidence 2 (by norm_num) 2 (by norm_num)
      (⟨2, Nat.prime_two⟩ : Nat.Primes) := by
  rw [(equal_parameters_have_zero_evidence 2 (by norm_num)).1]
  norm_num

#print axioms parameter_disequality_is_necessary

/-- A divergent positive prime family has totalized `tsum` zero without summability. -/
theorem nonsummable_prime_family_totalized :
    ¬ Summable (fun p : Nat.Primes => (1 / p.1 : Real)) ∧
      (∑' p : Nat.Primes, (1 / p.1 : Real)) = 0 := by
  refine ⟨Nat.Primes.not_summable_one_div, ?_⟩
  exact tsum_eq_zero_of_not_summable Nat.Primes.not_summable_one_div

#print axioms nonsummable_prime_family_totalized

end

end D5.S3.Analytic.ZetaObservation.PrimeChannelLogEvidence
