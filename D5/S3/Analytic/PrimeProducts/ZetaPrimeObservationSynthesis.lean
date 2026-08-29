/- GID: D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis
   generality: I
   mirror-B: D5/B/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeta prime laws give exact spectra, information splits, and edge boundaries. -/
/- Library-search audit trail (2026-08-25): Lean and Blueprint shape searches found the
   eight source clauses only as declarations spread across twelve modules, with no theorem
   synthesizing them. The atom manifest has empty Lean and Scribe coverage, pinned Mathlib has
   no zeta PMF or prime-exponent law, and Git history has no theorem 145.1 synthesis. Existing
   entropy, log-evidence, support, realizability, precision, and phase results are reused below.
   `Real.sqrt_eq_rpow`, `Real.rexp_tsum_eq_tprod`, and the real Euler-log bridge supply the new
   Hellinger product. Fisher is represented by the proved summable prime sensitivity family;
   the thermal clause is deliberately spectral, since the repository has no countable
   trace-class operator or restricted tensor-product API. -/

import D5.S3.Analytic.Boundary.ZetaPrimeProductCommonBoundary
import D5.S3.Analytic.PrimeProducts.GlobalPrimeExponentRealizability
import D5.S3.Analytic.PrimeProducts.PrimePrecisionEntropyContraction
import D5.S3.Analytic.Zeta.ZetaRenyiEntropy
import D5.S3.Analytic.ZetaObservation.PrimeChannelLogEvidence
import D5.S3.ConceptDynamics.ObservationOrder.TypedPrimeLanguageHierarchy
import D5.S3.Quantum.CountableSlices.SinglePrimeThermalState
import D5.S3.Quantum.Tomography.DiagonalPhaseBlindness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.PrimeProducts.ZetaPrimeObservationSynthesis

open scoped ENNReal BigOperators ProbabilityTheory
open D5.S3.Analytic.Boundary.ZetaPrimeProductCommonBoundary
open D5.S3.Analytic.PrimeProducts.FiniteMarginalGlobalSupportContrast
open D5.S3.Analytic.PrimeProducts.GlobalPrimeExponentRealizability
open D5.S3.Analytic.PrimeProducts.PrimePrecisionEntropyContraction
open D5.S3.Analytic.Zeta.EulerLogBridge
open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy
open D5.S3.Analytic.Zeta.ZetaPrimeIndependence
open D5.S3.Analytic.ZetaMinEntropy.PrimeDecomposition
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.ZetaObservation.PrimeChannelLogEvidence
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.ObservationOrder.TypedPrimeLanguageHierarchy
open D5.S3.Factorization.ExponentCoordinates.PrimeExponentBijection
open D5.S3.Quantum.CountableSlices.SinglePrimeThermalState
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses
open D5.S3.Quantum.Tomography.DiagonalPhaseBlindness
open ProbabilityTheory

noncomputable section

/-- The Hellinger affinity of two PMFs on a countable natural-number carrier. -/
def countableHellingerAffinity (P Q : PMF Nat) : Real :=
  ∑' n : Nat, Real.sqrt (pmfReal P n * pmfReal Q n)

/-- A prime-exponent marginal is exactly the corresponding single-prime thermal spectrum. -/
theorem primeExponentPMF_eq_singlePrimeThermalPMF
    (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    primeExponentPMF s hs p =
      singlePrimeThermalPMF p.1 s p.2.one_lt (by linarith) := by
  apply PMF.ext
  intro k
  rw [← ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (primeExponentPMF s hs p) k)
    (PMF.apply_ne_top
      (singlePrimeThermalPMF p.1 s p.2.one_lt (by linarith)) k)]
  change pmfReal (primeExponentPMF s hs p) k =
    pmfReal (singlePrimeThermalPMF p.1 s p.2.one_lt (by linarith)) k
  rw [primeExponentPMF_apply, singlePrimeThermalPMF_apply]
  simp only [singlePrimeThermalState]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (p.1 : Real))]
  congr 1
  ring

#print axioms primeExponentPMF_eq_singlePrimeThermalPMF

private lemma countableHellingerAffinity_zeta_closed_form
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) :
    countableHellingerAffinity (zetaDist s hs) (zetaDist t ht) =
      (partitionFunction ((s + t) / 2)).toReal /
        ((partitionFunction s).toReal ^ (1 / 2 : Real) *
          (partitionFunction t).toReal ^ (1 / 2 : Real)) := by
  have hu : 1 < (s + t) / 2 := by linarith
  have hpoint (n : Nat) :
      Real.sqrt
          (pmfReal (zetaDist s hs) n * pmfReal (zetaDist t ht) n) =
        (n : Real) ^ (-((s + t) / 2)) *
          (((partitionFunction s).toReal ^ (1 / 2 : Real) *
            (partitionFunction t).toReal ^ (1 / 2 : Real))⁻¹) := by
    by_cases hn : n = 0
    · subst n
      rw [zeta_real_apply, zeta_real_apply]
      simp [Real.zero_rpow (by linarith : -s ≠ 0),
        Real.zero_rpow (by linarith : -t ≠ 0),
        Real.zero_rpow (by linarith : -((s + t) / 2) ≠ 0)]
    · have hnR : 0 < (n : Real) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hPs : 0 ≤ pmfReal (zetaDist s hs) n := ENNReal.toReal_nonneg
      have hPt : 0 ≤ pmfReal (zetaDist t ht) n := ENNReal.toReal_nonneg
      rw [Real.sqrt_eq_rpow,
        Real.mul_rpow hPs hPt,
        zeta_renyi_power_pointwise s (1 / 2) hs n,
        zeta_renyi_power_pointwise t (1 / 2) ht n]
      rw [show -(1 / 2 * s) = -(s / 2) by ring,
        show -(1 / 2 * t) = -(t / 2) by ring]
      have hpow :
          (n : Real) ^ (-(s / 2)) * (n : Real) ^ (-(t / 2)) =
            (n : Real) ^ (-((s + t) / 2)) := by
        rw [← Real.rpow_add hnR]
        congr 1
        ring
      calc
        (n : Real) ^ (-(s / 2)) *
              ((partitionFunction s).toReal ^ (1 / 2 : Real))⁻¹ *
              ((n : Real) ^ (-(t / 2)) *
                ((partitionFunction t).toReal ^ (1 / 2 : Real))⁻¹) =
            ((n : Real) ^ (-(s / 2)) * (n : Real) ^ (-(t / 2))) *
              (((partitionFunction s).toReal ^ (1 / 2 : Real))⁻¹ *
                ((partitionFunction t).toReal ^ (1 / 2 : Real))⁻¹) := by ring
        _ = (n : Real) ^ (-((s + t) / 2)) *
              (((partitionFunction s).toReal ^ (1 / 2 : Real))⁻¹ *
                ((partitionFunction t).toReal ^ (1 / 2 : Real))⁻¹) := by rw [hpow]
        _ = (n : Real) ^ (-((s + t) / 2)) *
              (((partitionFunction s).toReal ^ (1 / 2 : Real) *
                (partitionFunction t).toReal ^ (1 / 2 : Real))⁻¹) := by
          rw [mul_inv]
  rw [countableHellingerAffinity]
  simp_rw [hpoint]
  rw [(summable_real_weight ((s + t) / 2) hu).tsum_mul_right,
    tsum_real_weight_eq_partition_toReal ((s + t) / 2) hu]
  simp only [div_eq_mul_inv]

private lemma countableHellingerAffinity_prime_closed_form
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) (p : Nat.Primes) :
    countableHellingerAffinity
        (primeExponentPMF s hs p) (primeExponentPMF t ht p) =
      ((1 - (p.1 : Real) ^ (-s)) ^ (1 / 2 : Real) *
          (1 - (p.1 : Real) ^ (-t)) ^ (1 / 2 : Real)) /
        (1 - (p.1 : Real) ^ (-((s + t) / 2))) := by
  let u : Real := (s + t) / 2
  have hu : 1 < u := by dsimp [u]; linarith
  have hp0 : 0 < (p.1 : Real) := by exact_mod_cast p.2.pos
  have hqs0 : 0 < (p.1 : Real) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hqt0 : 0 < (p.1 : Real) ^ (-t) := Real.rpow_pos_of_pos hp0 _
  have hqu0 : 0 < (p.1 : Real) ^ (-u) := Real.rpow_pos_of_pos hp0 _
  have hqs1 : (p.1 : Real) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have hqt1 : (p.1 : Real) ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have hqu1 : (p.1 : Real) ^ (-u) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have hpoint (k : Nat) :
      Real.sqrt
          (pmfReal (primeExponentPMF s hs p) k *
            pmfReal (primeExponentPMF t ht p) k) =
        ((1 - (p.1 : Real) ^ (-s)) ^ (1 / 2 : Real) *
            (1 - (p.1 : Real) ^ (-t)) ^ (1 / 2 : Real)) *
          ((p.1 : Real) ^ (-u)) ^ k := by
    have hPs : 0 ≤ pmfReal (primeExponentPMF s hs p) k := ENNReal.toReal_nonneg
    have hPt : 0 ≤ pmfReal (primeExponentPMF t ht p) k := ENNReal.toReal_nonneg
    rw [Real.sqrt_eq_rpow,
      Real.mul_rpow hPs hPt,
      primeExponentPMF_apply, primeExponentPMF_apply,
      Real.mul_rpow (sub_pos.mpr hqs1).le (Real.rpow_nonneg hp0.le _),
      Real.mul_rpow (sub_pos.mpr hqt1).le (Real.rpow_nonneg hp0.le _),
      ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le]
    have hpow :
        (p.1 : Real) ^ (-(k : Real) * s * (1 / 2 : Real)) *
            (p.1 : Real) ^ (-(k : Real) * t * (1 / 2 : Real)) =
          ((p.1 : Real) ^ (-u)) ^ k := by
      rw [← Real.rpow_add hp0]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      congr 1
      dsimp [u]
      ring
    rw [← hpow]
    ring
  have hgeom : Summable (fun k : Nat => ((p.1 : Real) ^ (-u)) ^ k) :=
    summable_geometric_of_lt_one hqu0.le hqu1
  rw [countableHellingerAffinity]
  simp_rw [hpoint]
  rw [hgeom.tsum_mul_left, tsum_geometric_of_lt_one hqu0.le hqu1]
  dsimp [u]
  simp only [div_eq_mul_inv]

private lemma summable_prime_euler_log (a : Real) (ha : 1 < a) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (p.1 : Real) ^ (-a))) := by
  apply (summable_primeExponent_minEntropy a ha).congr
  intro p
  rw [primeExponent_min_entropy_eq]

/-- Hellinger affinity between two zeta laws is the product of its prime-mode affinities. -/
theorem countableHellingerAffinity_zeta_eq_tprod_prime
    (s : Real) (hs : 1 < s) (t : Real) (ht : 1 < t) :
    countableHellingerAffinity (zetaDist s hs) (zetaDist t ht) =
      ∏' p : Nat.Primes,
        countableHellingerAffinity
          (primeExponentPMF s hs p) (primeExponentPMF t ht p) := by
  let u : Real := (s + t) / 2
  let e : Real → Nat.Primes → Real := fun a p =>
    -Real.log (1 - (p.1 : Real) ^ (-a))
  have hu : 1 < u := by dsimp [u]; linarith
  have hS : Summable (e s) := by
    simpa only [e] using summable_prime_euler_log s hs
  have hT : Summable (e t) := by
    simpa only [e] using summable_prime_euler_log t ht
  have hU : Summable (e u) := by
    simpa only [e] using summable_prime_euler_log u hu
  have hLocalPos (p : Nat.Primes) :
      0 < countableHellingerAffinity
        (primeExponentPMF s hs p) (primeExponentPMF t ht p) := by
    rw [countableHellingerAffinity_prime_closed_form]
    have hqs : 0 < 1 - (p.1 : Real) ^ (-s) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.2.one_lt) (by linarith))
    have hqt : 0 < 1 - (p.1 : Real) ^ (-t) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.2.one_lt) (by linarith))
    have hqu : 0 < 1 - (p.1 : Real) ^ (-u) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.2.one_lt) (by linarith))
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hqs _) (Real.rpow_pos_of_pos hqt _)) hqu
  have hLogPoint (p : Nat.Primes) :
      Real.log
          (countableHellingerAffinity
            (primeExponentPMF s hs p) (primeExponentPMF t ht p)) =
        e u p - (1 / 2 : Real) * e s p - (1 / 2 : Real) * e t p := by
    rw [countableHellingerAffinity_prime_closed_form]
    have hqs : 0 < 1 - (p.1 : Real) ^ (-s) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.2.one_lt) (by linarith))
    have hqt : 0 < 1 - (p.1 : Real) ^ (-t) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.2.one_lt) (by linarith))
    have hqu : 0 < 1 - (p.1 : Real) ^ (-u) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.2.one_lt) (by linarith))
    rw [Real.log_div
      (mul_pos (Real.rpow_pos_of_pos hqs _) (Real.rpow_pos_of_pos hqt _)).ne'
      hqu.ne',
      Real.log_mul (Real.rpow_pos_of_pos hqs _).ne'
        (Real.rpow_pos_of_pos hqt _).ne',
      Real.log_rpow hqs, Real.log_rpow hqt]
    dsimp [e, u]
    ring
  have hLogSummable : Summable (fun p : Nat.Primes =>
      Real.log
        (countableHellingerAffinity
          (primeExponentPMF s hs p) (primeExponentPMF t ht p))) := by
    apply ((hU.sub (hS.mul_left (1 / 2))).sub
      (hT.mul_left (1 / 2))).congr
    intro p
    exact (hLogPoint p).symm
  have hLogTsum :
      ∑' p : Nat.Primes,
          Real.log
            (countableHellingerAffinity
              (primeExponentPMF s hs p) (primeExponentPMF t ht p)) =
        Real.log (partitionFunction u).toReal -
          (1 / 2 : Real) * Real.log (partitionFunction s).toReal -
          (1 / 2 : Real) * Real.log (partitionFunction t).toReal := by
    rw [show (fun p : Nat.Primes =>
        Real.log
          (countableHellingerAffinity
            (primeExponentPMF s hs p) (primeExponentPMF t ht p))) =
        fun p => e u p - (1 / 2 : Real) * e s p - (1 / 2 : Real) * e t p by
      funext p
      exact hLogPoint p]
    rw [(hU.sub (hS.mul_left (1 / 2))).tsum_sub (hT.mul_left (1 / 2)),
      hU.tsum_sub (hS.mul_left (1 / 2)), hS.tsum_mul_left,
      hT.tsum_mul_left, ← log_partitionFunction_eq_tsum_prime u hu,
      ← log_partitionFunction_eq_tsum_prime s hs,
      ← log_partitionFunction_eq_tsum_prime t ht]
  have hGlobalPos :
      0 < countableHellingerAffinity (zetaDist s hs) (zetaDist t ht) := by
    rw [countableHellingerAffinity_zeta_closed_form]
    exact div_pos (partition_toReal_pos u hu)
      (mul_pos
        (Real.rpow_pos_of_pos (partition_toReal_pos s hs) _)
        (Real.rpow_pos_of_pos (partition_toReal_pos t ht) _))
  have hGlobalLog :
      Real.log
          (countableHellingerAffinity (zetaDist s hs) (zetaDist t ht)) =
        Real.log (partitionFunction u).toReal -
          (1 / 2 : Real) * Real.log (partitionFunction s).toReal -
          (1 / 2 : Real) * Real.log (partitionFunction t).toReal := by
    rw [countableHellingerAffinity_zeta_closed_form]
    have hZs := partition_toReal_pos s hs
    have hZt := partition_toReal_pos t ht
    have hZu := partition_toReal_pos u hu
    rw [Real.log_div hZu.ne'
      (mul_pos (Real.rpow_pos_of_pos hZs _) (Real.rpow_pos_of_pos hZt _)).ne',
      Real.log_mul (Real.rpow_pos_of_pos hZs _).ne'
        (Real.rpow_pos_of_pos hZt _).ne',
      Real.log_rpow hZs, Real.log_rpow hZt]
    ring
  calc
    countableHellingerAffinity (zetaDist s hs) (zetaDist t ht) =
        Real.exp
          (Real.log
            (countableHellingerAffinity (zetaDist s hs) (zetaDist t ht))) :=
      (Real.exp_log hGlobalPos).symm
    _ = Real.exp
        (∑' p : Nat.Primes,
          Real.log
            (countableHellingerAffinity
              (primeExponentPMF s hs p) (primeExponentPMF t ht p))) := by
      rw [hGlobalLog, hLogTsum]
    _ = ∏' p : Nat.Primes,
        countableHellingerAffinity
          (primeExponentPMF s hs p) (primeExponentPMF t ht p) :=
      Real.rexp_tsum_eq_tprod hLocalPos hLogSummable

#print axioms countableHellingerAffinity_zeta_eq_tprod_prime

/-- The tail-conditioned prime law translated back to zero at a chosen precision. -/
def primeResidualLaw
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) : PMF Nat :=
  ((primeExponentPMF s hs p).filter (Set.Ici precision) (by
      refine ⟨precision, Set.mem_Ici.mpr le_rfl, ?_⟩
      rw [PMF.mem_support_iff]
      intro hzero
      have hpositive : 0 < pmfReal (primeExponentPMF s hs p) precision := by
        rw [primeExponentPMF_apply]
        exact mul_pos
          (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
            (by exact_mod_cast p.2.one_lt) (by linarith)))
          (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _)
      rw [pmfReal, hzero, ENNReal.toReal_zero] at hpositive
      exact (lt_irrefl 0) hpositive)).map
    (fun value : Nat => value - precision)

/-- The unresolved entropy after observing a prime exponent up to a chosen precision. -/
def primeResidualEntropy
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) : Real :=
  ((primeExponentPMF s hs p).toMeasure (Set.Ici precision)).toReal *
    countableEntropy (primeResidualLaw s hs p precision)

/-- Prime-indexed diagonal qubit observables are blind to the canonical relative-phase pair. -/
def PrimeDiagonalPhaseBlindness : Prop :=
  ∀ observable : Nat.Primes → QubitMatrix,
    (∀ p, (observable p).IsDiag) →
      equalSuperpositionDensity ≠
          qubitZ * equalSuperpositionDensity * qubitZ ∧
        jointReadout (fun p rho => bornProbability rho (observable p))
            equalSuperpositionDensity =
          jointReadout (fun p rho => bornProbability rho (observable p))
            (qubitZ * equalSuperpositionDensity * qubitZ)

/-!
The fifth clause below uses the repository's exact Shannon and real-valued log-evidence
decompositions and the new Hellinger product. The Fisher carrier available here is the summable
prime sensitivity family, not a global score-variance identity. The seventh clause similarly
asserts independence and exact thermal marginal spectra, not an unavailable restricted tensor
product of trace-class operators.
-/

/-- FPOD 145.1 on the repository's probability, information, and spectral carriers. -/
theorem zeta_prime_observation_synthesis (s : Real) (hs : 1 < s) :
    Function.Bijective primeExponentLanguageEquiv ∧
    iIndepFun (fun p : Nat.Primes ↦ fun n : Nat ↦ n.factorization p.1)
      (zetaDist s hs).toMeasure ∧
    exponentProduct s (by linarith)
      {exponents | (Function.support exponents).Finite} = 1 ∧
    (RealizesPrimeExponentLaw s (zetaDist s hs) ∧
      (∀ (q : PMF Nat), RealizesPrimeExponentLaw s q → q = zetaDist s hs) ∧
      (∀ (q : PMF Nat), RealizesPrimeExponentLaw s q → ∀ n : Nat,
        pmfReal q n = (n : Real) ^ (-s) / (riemannZeta (s : Complex)).re)) ∧
    (countableEntropy (zetaDist s hs) =
        ∑' p : Nat.Primes, countableEntropy (primeExponentPMF s hs p) ∧
      (∀ (t : Real) (ht : 1 < t),
        zetaFamilyLogEvidence s hs t ht =
          ∑' p : Nat.Primes, primeChannelLogEvidence s hs t ht p) ∧
      Summable (fun p : Nat.Primes =>
        Real.log p.1 ^ 2 *
          ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)) ^ 2)) ∧
      (∀ (t : Real) (ht : 1 < t),
        countableHellingerAffinity (zetaDist s hs) (zetaDist t ht) =
          ∏' p : Nat.Primes,
            countableHellingerAffinity
              (primeExponentPMF s hs p) (primeExponentPMF t ht p))) ∧
    (∀ (p : Nat.Primes) (k : Nat),
      primeResidualEntropy s hs p k =
          ((p.1 : Real) ^ (-s)) ^ k *
            countableEntropy (primeExponentPMF s hs p) ∧
        primeResidualEntropy s hs p (k + 1) =
          ((p.1 : Real) ^ (-s)) ^ (k + 1) *
            countableEntropy (primeExponentPMF s hs p) ∧
        primeResidualEntropy s hs p (k + 1) =
          (p.1 : Real) ^ (-s) * primeResidualEntropy s hs p k) ∧
    (iIndepFun (fun p : Nat.Primes ↦ fun n : Nat ↦ n.factorization p.1)
        (zetaDist s hs).toMeasure ∧
      (∀ p : Nat.Primes,
        primeExponentPMF s hs p =
          singlePrimeThermalPMF p.1 s p.2.one_lt (by linarith)) ∧
      countableEntropy (zetaDist s hs) =
        ∑' p : Nat.Primes,
          countableEntropy
            (singlePrimeThermalPMF p.1 s p.2.one_lt (by linarith))) ∧
    (Function.Bijective primeExponentLanguageEquiv ∧
      PrimeDiagonalPhaseBlindness) := by
  have hs0 : 0 < s := by linarith
  have hBoundary := zeta_prime_product_common_boundary s hs0
  refine ⟨prime_exponent_language_bijection, iIndepFun_factorization s hs,
    hBoundary.2.2.1.mpr hs, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨zeta_realizes_prime_exponent_law s hs, ?_, ?_⟩
    · intro q hq
      exact prime_exponent_realization_unique s hs q hq
    · intro q hq n
      exact prime_exponent_realization_mass s hs q hq n
  · refine ⟨countableEntropy_zeta_eq_tsum_prime s hs, ?_,
      hBoundary.2.2.2.2.mpr hs, ?_⟩
    · intro t ht
      exact zetaFamilyLogEvidence_eq_tsum_prime s hs t ht
    · intro t ht
      exact countableHellingerAffinity_zeta_eq_tprod_prime s hs t ht
  · intro p k
    simpa only [primeResidualEntropy, primeResidualLaw] using
      prime_precision_entropy_contraction s hs p k
  · refine ⟨iIndepFun_factorization s hs, ?_, modal_thermal_entropy_additive s hs⟩
    intro p
    exact primeExponentPMF_eq_singlePrimeThermalPMF s hs p
  · refine ⟨prime_exponent_language_bijection, ?_⟩
    simpa only [PrimeDiagonalPhaseBlindness] using
      (@diagonal_prime_observables_cannot_recover_relative_phase Nat.Primes).1

#print axioms zeta_prime_observation_synthesis

/-- The strict lower boundary is necessary for a positive-integer prime-law realization. -/
theorem one_lt_is_necessary :
    ¬ ∃ q : PMF Nat, RealizesPrimeExponentLaw 1 q :=
  critical_exponent_not_realizable

#print axioms one_lt_is_necessary

/- Degenerate audit: point laws, zero slots, zero precision, empty and singleton observable
   families, identity and constant maps, and equal phases do not create extra information. -/
example : countableHellingerAffinity (PMF.pure 0) (PMF.pure 0) = 1 := by
  rw [countableHellingerAffinity]
  rw [tsum_eq_single 0]
  · simp [pmfReal, PMF.pure_apply]
  · intro n hn
    simp [pmfReal, PMF.pure_apply, hn]

example : countableHellingerAffinity (PMF.pure 0) (PMF.pure 1) = 0 := by
  rw [countableHellingerAffinity]
  have hzero : (fun n : Nat =>
      Real.sqrt (pmfReal (PMF.pure 0) n * pmfReal (PMF.pure 1) n)) =
      fun _ => 0 := by
    funext n
    by_cases hzero : n = 0
    · subst n
      simp [pmfReal, PMF.pure_apply]
    · by_cases hone : n = 1
      · subst n
        simp [pmfReal, PMF.pure_apply]
      · simp [pmfReal, PMF.pure_apply, hzero, hone]
  rw [hzero, tsum_zero]

example (s : Real) (hs : 1 < s) : pmfReal (zetaDist s hs) 0 = 0 := by
  rw [zeta_real_apply]
  simp [Real.zero_rpow (by linarith : -s ≠ 0)]

example (s : Real) (hs : 1 < s) (p : Nat.Primes) :=
  prime_precision_entropy_contraction s hs p 0

example := @diagonal_prime_observables_cannot_recover_relative_phase Empty

example := @diagonal_prime_observables_cannot_recover_relative_phase Unit

example : Function.Bijective (id : Unit → Unit) := Function.bijective_id

example : ¬Function.Injective (fun _ : Bool => ()) := by
  intro h
  have := h (a₁ := false) (a₂ := true) rfl
  simp at this

example (rho : DensityState (Fin 2)) :
    qubitPrimeDiagonalLanguage rho = qubitPrimeDiagonalLanguage rho := rfl

end

end D5.S3.Analytic.PrimeProducts.ZetaPrimeObservationSynthesis
