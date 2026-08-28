/- GID: D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability
   generality: I
   mirror-B: D5/B/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive integer prime-exponent realizations exist uniquely exactly for s above one. -/
/- Library-search audit trail (2026-08-29):
   * Repository exact hits `iIndepFun_factorization` and `measure_factorization_eq`
     give the zeta law's independence and geometric marginals.
   * `zetaDist`, `zeta_dist_apply`, `zeta_real_apply`,
     `partition_toReal_eq_zeta_re`, and `primeEvidence_summable_iff_one_lt`
     were inspected. The first four identify the unique mass; the threshold is
     already carried by `finite_marginals_and_global_support_contrast` below.
   * `FiniteMarginalGlobalSupportContrast` publicly supplies the canonical
     product law and its almost-sure infinite support for `0 < s <= 1`.
   * Pinned Mathlib exact hits include `iIndepFun.map_fun_eq_infinitePi_map`,
     `Measure.ext_of_singleton`, `Nat.eq_of_factorization_eq`,
     `PMF.toMeasure_apply_singleton`, and second Borel-Cantelli theorem
     `measure_limsup_eq_one`. Searches also inspected `Nat.factorization`,
     `Summable`, `MeasureTheory.ae_of_all`, and the independence API.
   * The dispatched `LocalEvidenceOrderThreshold` and its `firstEventMass_*`
     declarations are absent at pinned commit 153287c; no exact global iff or
     uniqueness theorem was found. -/

import D5.S3.Analytic.PrimeProducts.FiniteMarginalGlobalSupportContrast
import D5.S3.Analytic.Zeta.ZetaPrimeIndependence
import D5.S3.Analytic.Zeta.ZetaRenyiEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.PrimeProducts.GlobalPrimeExponentRealizability

open scoped ENNReal

open MeasureTheory ProbabilityTheory
open D5.S3.Analytic.PrimeProducts.FiniteMarginalGlobalSupportContrast
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.ZetaPrimeIndependence
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy

noncomputable section

/-- The prescribed zero-start geometric mass at one prime exponent. -/
def geometricPrimeMass (s : Real) (p : Nat.Primes) (k : Nat) : ENNReal :=
  ENNReal.ofReal
    ((1 - (p.1 : Real) ^ (-s)) * (p.1 : Real) ^ (-(k : Real) * s))

/-- The complete prime-exponent code of a natural number. -/
def primeExponentCode (n : Nat) (p : Nat.Primes) : Nat :=
  n.factorization p.1

/-- A PMF on naturals realizes the positive-integer independent prime-exponent law. -/
def RealizesPrimeExponentLaw (s : Real) (q : PMF Nat) : Prop :=
  q 0 = 0 ∧
    iIndepFun (fun p : Nat.Primes => fun n : Nat => primeExponentCode n p)
      q.toMeasure ∧
    ∀ (p : Nat.Primes) (k : Nat),
      q.toMeasure {n : Nat | primeExponentCode n p = k} =
        geometricPrimeMass s p k

/-- Without positive support, the exponent code cannot distinguish zero from one. -/
theorem positive_integer_support_is_necessary :
    (PMF.pure 0 : PMF Nat).toMeasure.map primeExponentCode =
        (PMF.pure 1 : PMF Nat).toMeasure.map primeExponentCode ∧
      (PMF.pure 0 : PMF Nat) ≠ PMF.pure 1 := by
  have hcode : primeExponentCode 0 = primeExponentCode 1 := by
    funext p
    simp [primeExponentCode]
  constructor
  · rw [PMF.toMeasure_pure, PMF.toMeasure_pure,
      Measure.map_dirac' (by fun_prop), Measure.map_dirac' (by fun_prop), hcode]
  · intro h
    have hmass := congrArg (fun q : PMF Nat => q 0) h
    norm_num [PMF.pure_apply] at hmass

#print axioms positive_integer_support_is_necessary

/-- At exponent zero, the prescribed mass is `1 - p ^ (-s)`. -/
theorem geometric_prime_mass_zero (s : Real) (p : Nat.Primes) :
    geometricPrimeMass s p 0 =
      ENNReal.ofReal (1 - (p.1 : Real) ^ (-s)) := by
  simp [geometricPrimeMass]

#print axioms geometric_prime_mass_zero

private lemma activation_probability_lt_one (s : Real) (hs : 0 < s)
    (p : Nat.Primes) : activationProbability s p < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast p.2.one_lt
  · linarith

private lemma exponent_success_ne_zero (s : Real) (hs : 0 < s)
    (p : Nat.Primes) : exponentSuccess s hs p ≠ 0 := by
  apply ne_of_gt
  change 0 < 1 - activationProbability s p
  exact sub_pos.mpr (activation_probability_lt_one s hs p)

private lemma geometric_prime_mass_eq_activation (s : Real) (p : Nat.Primes)
    (k : Nat) :
    geometricPrimeMass s p k =
      ENNReal.ofReal
        ((1 - activationProbability s p) * (activationProbability s p) ^ k) := by
  unfold geometricPrimeMass activationProbability
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring_nf

private lemma mapped_prime_exponent_marginal (s : Real) (hs : 0 < s)
    (q : PMF Nat) (hq : RealizesPrimeExponentLaw s q) (p : Nat.Primes) :
    q.toMeasure.map (fun n : Nat => primeExponentCode n p) =
      exponentMeasure s hs p := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton k)]
  change q.toMeasure {n : Nat | primeExponentCode n p = k} =
    exponentMeasure s hs p {k}
  rw [hq.2.2 p k, geometric_prime_mass_eq_activation]
  rw [exponentMeasure, geometricMeasure_singleton
    (exponent_success_ne_zero s hs p)]
  change ENNReal.ofReal
      ((1 - activationProbability s p) * (activationProbability s p) ^ k) =
    ENNReal.ofReal
      ((1 - (1 - activationProbability s p)) ^ k *
        (1 - activationProbability s p))
  congr 1
  ring

private lemma realization_joint_law_eq_product (s : Real) (hs : 0 < s)
    (q : PMF Nat) (hq : RealizesPrimeExponentLaw s q) :
    q.toMeasure.map primeExponentCode = exponentProduct s hs := by
  calc
    q.toMeasure.map primeExponentCode =
        Measure.infinitePi
          (fun p : Nat.Primes =>
            q.toMeasure.map (fun n : Nat => primeExponentCode n p)) := by
      exact hq.2.1.map_fun_eq_infinitePi_map fun _ => by fun_prop
    _ = Measure.infinitePi (exponentMeasure s hs) := by
      congr 1
      funext p
      exact mapped_prime_exponent_marginal s hs q hq p
    _ = exponentProduct s hs := rfl

private lemma prime_exponent_code_support_finite (n : Nat) :
    (Function.support (primeExponentCode n)).Finite := by
  change (Subtype.val ⁻¹' Function.support n.factorization).Finite
  exact n.factorization.hasFiniteSupport.preimage Subtype.coe_injective.injOn

private lemma no_realization_of_pos_le_one (s : Real) (hs : 0 < s)
    (hs_le : s ≤ 1) (q : PMF Nat) (hq : RealizesPrimeExponentLaw s q) : False := by
  let finiteProfiles : Set (Nat.Primes → Nat) :=
    {exponents | (Function.support exponents).Finite}
  have hproductZero : exponentProduct s hs finiteProfiles = 0 :=
    (finite_marginals_and_global_support_contrast s hs).2.2.2 hs_le
  have hjoint : q.toMeasure.map primeExponentCode = exponentProduct s hs :=
    realization_joint_law_eq_product s hs q hq
  have hrangeMeasurable : MeasurableSet (Set.range primeExponentCode) :=
    Set.countable_range primeExponentCode |>.measurableSet
  have hrangeFull :
      q.toMeasure.map primeExponentCode (Set.range primeExponentCode) = 1 := by
    rw [Measure.map_apply (by fun_prop) hrangeMeasurable]
    simp
  have hrangeSubset : Set.range primeExponentCode ⊆ finiteProfiles := by
    rintro exponents ⟨n, rfl⟩
    exact prime_exponent_code_support_finite n
  have hle :
      q.toMeasure.map primeExponentCode (Set.range primeExponentCode) ≤
        q.toMeasure.map primeExponentCode finiteProfiles :=
    measure_mono hrangeSubset
  rw [hrangeFull, hjoint, hproductZero] at hle
  exact one_ne_zero (nonpos_iff_eq_zero.mp hle)

private lemma no_realization_of_nonpos (s : Real) (hs : s ≤ 0)
    (q : PMF Nat) (hq : RealizesPrimeExponentLaw s q) : False := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let marginal := q.toMeasure.map (fun n : Nat => primeExponentCode n p)
  have hmarginalZero : marginal = 0 := by
    apply Measure.ext_of_singleton
    intro k
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton k)]
    change q.toMeasure {n : Nat | primeExponentCode n p = k} = 0
    rw [hq.2.2 p k, geometricPrimeMass]
    apply ENNReal.ofReal_eq_zero.mpr
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply sub_nonpos.mpr
      have hpow : (1 : Real) ≤ (2 : Real) ^ (-s) := by
        exact Real.one_le_rpow (by norm_num) (by linarith)
      simpa [p] using hpow
    · exact Real.rpow_nonneg (by positivity) _
  have hprobability : marginal Set.univ = 1 := by
    dsimp [marginal]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  rw [hmarginalZero] at hprobability
  simp at hprobability

/-- Above exponent one, the zeta PMF realizes all prescribed prime-exponent laws. -/
theorem zeta_realizes_prime_exponent_law (s : Real) (hs : 1 < s) :
    RealizesPrimeExponentLaw s (zetaDist s hs) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [zeta_dist_apply, weight_zero s (by linarith)]
  · simpa [primeExponentCode] using iIndepFun_factorization s hs
  · intro p k
    simpa [primeExponentCode, geometricPrimeMass] using
      measure_factorization_eq s hs p.1 k p.2

#print axioms zeta_realizes_prime_exponent_law

/-- A positive-integer independent geometric prime-exponent law exists exactly for `1 < s`. -/
theorem global_prime_exponent_realizable_iff (s : Real) :
    (∃ q : PMF Nat, RealizesPrimeExponentLaw s q) ↔ 1 < s := by
  constructor
  · rintro ⟨q, hq⟩
    by_contra hs_not
    have hs_le : s ≤ 1 := le_of_not_gt hs_not
    by_cases hs : 0 < s
    · exact no_realization_of_pos_le_one s hs hs_le q hq
    · exact no_realization_of_nonpos s (le_of_not_gt hs) q hq
  · intro hs
    exact ⟨zetaDist s hs, zeta_realizes_prime_exponent_law s hs⟩

#print axioms global_prime_exponent_realizable_iff

private lemma prime_exponent_code_injective_off_zero {m n : Nat}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hcode : primeExponentCode m = primeExponentCode n) : m = n := by
  apply Nat.eq_of_factorization_eq hm hn
  intro p
  by_cases hp : p.Prime
  · exact congrFun hcode ⟨p, hp⟩
  · rw [Nat.factorization_eq_zero_of_not_prime m hp,
      Nat.factorization_eq_zero_of_not_prime n hp]

private lemma measure_prime_exponent_fiber (q : PMF Nat) (hq0 : q 0 = 0)
    (n : Nat) (hn : n ≠ 0) :
    q.toMeasure (primeExponentCode ⁻¹' {primeExponentCode n}) =
      q.toMeasure {n} := by
  have hz : q.toMeasure ({0} : Set Nat) = 0 := by
    rw [q.toMeasure_apply_singleton 0 (measurableSet_singleton 0)]
    exact hq0
  have hne : ∀ᵐ m ∂q.toMeasure, m ≠ 0 := by
    rw [ae_iff]
    simpa using hz
  apply measure_congr
  filter_upwards [hne] with m hm
  apply propext
  change primeExponentCode m = primeExponentCode n ↔ m = n
  constructor
  · exact fun h => prime_exponent_code_injective_off_zero hm hn h
  · exact fun h => h ▸ rfl

/-- Every realization is the zeta PMF; positive support removes the `0`/`1` ambiguity. -/
theorem prime_exponent_realization_unique (s : Real) (hs : 1 < s)
    (q : PMF Nat) (hq : RealizesPrimeExponentLaw s q) :
    q = zetaDist s hs := by
  let z := zetaDist s hs
  have hz : RealizesPrimeExponentLaw s z :=
    zeta_realizes_prime_exponent_law s hs
  have hmap : q.toMeasure.map primeExponentCode =
      z.toMeasure.map primeExponentCode := by
    rw [realization_joint_law_eq_product s (by linarith) q hq]
    rw [realization_joint_law_eq_product s (by linarith) z hz]
  apply PMF.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [z, hq.1, hz.1]
  have hqFiber := measure_prime_exponent_fiber q hq.1 n hn
  have hzFiber := measure_prime_exponent_fiber z hz.1 n hn
  calc
    q n = q.toMeasure {n} :=
      (q.toMeasure_apply_singleton n (measurableSet_singleton n)).symm
    _ = q.toMeasure (primeExponentCode ⁻¹' {primeExponentCode n}) := hqFiber.symm
    _ = q.toMeasure.map primeExponentCode {primeExponentCode n} := by
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    _ = z.toMeasure.map primeExponentCode {primeExponentCode n} := by rw [hmap]
    _ = z.toMeasure (primeExponentCode ⁻¹' {primeExponentCode n}) := by
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    _ = z.toMeasure {n} := hzFiber
    _ = z n := z.toMeasure_apply_singleton n (measurableSet_singleton n)

#print axioms prime_exponent_realization_unique

/-- The unique realization has mass `n ^ (-s) / zeta(s)` at every natural number. -/
theorem prime_exponent_realization_mass (s : Real) (hs : 1 < s)
    (q : PMF Nat) (hq : RealizesPrimeExponentLaw s q) (n : Nat) :
    pmfReal q n =
      (n : Real) ^ (-s) / (riemannZeta (s : Complex)).re := by
  rw [prime_exponent_realization_unique s hs q hq]
  rw [zeta_real_apply s hs n, partition_toReal_eq_zeta_re s hs]
  rfl

#print axioms prime_exponent_realization_mass

/-- Exponent zero is a concrete non-realizable degeneration. -/
theorem zero_exponent_not_realizable :
    ¬ ∃ q : PMF Nat, RealizesPrimeExponentLaw 0 q := by
  intro hq
  have : (1 : Real) < 0 := (global_prime_exponent_realizable_iff 0).mp hq
  linarith

#print axioms zero_exponent_not_realizable

/-- The critical exponent one is also not globally realizable. -/
theorem critical_exponent_not_realizable :
    ¬ ∃ q : PMF Nat, RealizesPrimeExponentLaw 1 q := by
  intro hq
  have : (1 : Real) < 1 := (global_prime_exponent_realizable_iff 1).mp hq
  linarith

#print axioms critical_exponent_not_realizable

end

end D5.S3.Analytic.PrimeProducts.GlobalPrimeExponentRealizability
