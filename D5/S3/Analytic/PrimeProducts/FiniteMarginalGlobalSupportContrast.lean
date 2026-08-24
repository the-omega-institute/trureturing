/- GID: D5/S3/Analytic/PrimeProducts/FiniteMarginalGlobalSupportContrast
   generality: G
   mirror-B: D5/B/S3/Analytic/PrimeProducts/FiniteMarginalGlobalSupportContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible finite prime-exponent laws coexist with almost-sure infinite support. -/

import Mathlib

/- Library-search audit trail (2026-08-24):
   * Exact pinned-Mathlib hits `geometricMeasure`, `geometricMeasure_singleton`,
     `infinitePi_map_restrict`, and `infinitePi_pi` construct the coordinate laws,
     their canonical product, its finite restrictions, and its cylinder masses.
   * Exact hits `iIndepFun_infinitePi` and `iIndepSet_iff_meas_biInter` supply
     independence of the coordinate activation events.
   * Exact hits `Nat.Primes.summable_rpow`,
     `ENNReal.tsum_coe_eq_top_iff_not_summable_coe`, and
     `measure_limsup_eq_one` give the prime-series divergence and the second
     Borel-Cantelli conclusion used for the global support clause.
   * Repository search found only the instance-plane zeta-distribution exponent
     law, which is not an importable general construction. No prior general theorem
     combines compatible finite geometric marginals with the support contrast.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal BigOperators

noncomputable section

namespace D5.S3.Analytic.PrimeProducts.FiniteMarginalGlobalSupportContrast

open Filter MeasureTheory ProbabilityTheory Set

/-- The source activation probability at a prime coordinate. -/
def activationProbability (s : Real) (p : Nat.Primes) : Real :=
  (p : Real) ^ (-s)

/-- The success parameter whose zero-start geometric law has activation mass `p ^ (-s)`. -/
def exponentSuccess (s : Real) (hs : 0 < s) (p : Nat.Primes) : unitInterval := by
  have hp : (1 : Real) < (p : Real) := by
    exact_mod_cast p.property.one_lt
  have hq_lt : activationProbability s p < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg hp
    linarith
  exact ⟨1 - activationProbability s p,
    sub_nonneg.mpr hq_lt.le,
    sub_le_self 1 (Real.rpow_nonneg (by positivity) _)⟩

/-- The zero-start geometric exponent law at one prime. -/
def exponentMeasure (s : Real) (hs : 0 < s) (p : Nat.Primes) : Measure Nat :=
  geometricMeasure (exponentSuccess s hs p)

instance exponentMeasure_isProbability (s : Real) (hs : 0 < s) (p : Nat.Primes) :
    IsProbabilityMeasure (exponentMeasure s hs p) := by
  unfold exponentMeasure
  infer_instance

/-- The canonical independent product of all prime-coordinate exponent laws. -/
def exponentProduct (s : Real) (hs : 0 < s) : Measure (Nat.Primes -> Nat) :=
  Measure.infinitePi (exponentMeasure s hs)

instance exponentProduct_isProbability (s : Real) (hs : 0 < s) :
    IsProbabilityMeasure (exponentProduct s hs) := by
  unfold exponentProduct
  infer_instance

/-- The event that a prime coordinate has positive exponent. -/
def activationEvent (p : Nat.Primes) : Set (Nat.Primes -> Nat) :=
  (fun exponents => exponents p) ⁻¹' ({0} : Set Nat)ᶜ

private lemma activation_probability_nonneg (s : Real) (p : Nat.Primes) :
    0 <= activationProbability s p :=
  Real.rpow_nonneg (by positivity) _

private lemma activation_probability_lt_one (s : Real) (hs : 0 < s)
    (p : Nat.Primes) : activationProbability s p < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast p.property.one_lt
  · linarith

private lemma exponent_success_ne_zero (s : Real) (hs : 0 < s)
    (p : Nat.Primes) : exponentSuccess s hs p ≠ 0 := by
  apply ne_of_gt
  change 0 < 1 - activationProbability s p
  exact sub_pos.mpr (activation_probability_lt_one s hs p)

private lemma activation_event_measurable (p : Nat.Primes) :
    MeasurableSet (activationEvent p) := by
  exact (measurable_pi_apply p (measurableSet_singleton 0).compl)

private lemma exponent_measure_activation (s : Real) (hs : 0 < s)
    (p : Nat.Primes) :
    exponentMeasure s hs p ({0} : Set Nat)ᶜ =
      ENNReal.ofReal (activationProbability s p) := by
  have hsuccess := exponent_success_ne_zero s hs p
  have hq_nonneg := activation_probability_nonneg s p
  have hq_le := (activation_probability_lt_one s hs p).le
  rw [prob_compl_eq_one_sub (measurableSet_singleton 0)]
  rw [exponentMeasure, geometricMeasure_singleton hsuccess]
  change 1 - ENNReal.ofReal ((1 - (1 - activationProbability s p)) ^ 0 *
    (1 - activationProbability s p)) = _
  rw [pow_zero, one_mul, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr hq_le)]
  congr 1
  ring

private lemma exponent_product_activation (s : Real) (hs : 0 < s)
    (p : Nat.Primes) :
    exponentProduct s hs (activationEvent p) =
      ENNReal.ofReal (activationProbability s p) := by
  calc
    exponentProduct s hs (activationEvent p) =
        (exponentProduct s hs).map (fun exponents => exponents p) ({0}ᶜ) := by
      exact (Measure.map_apply (by fun_prop) (measurableSet_singleton 0).compl).symm
    _ = exponentMeasure s hs p ({0}ᶜ) := by
      rw [exponentProduct, Measure.infinitePi_map_eval]
    _ = ENNReal.ofReal (activationProbability s p) := by
      exact exponent_measure_activation s hs p

private lemma activation_events_independent (s : Real) (hs : 0 < s) :
    iIndepSet activationEvent (exponentProduct s hs) := by
  have hindependent :
      iIndepFun (fun p (exponents : Nat.Primes -> Nat) => exponents p)
        (exponentProduct s hs) := by
    exact iIndepFun_infinitePi (X := fun _ n => n) (fun _ => measurable_id)
  apply (iIndepSet_iff_meas_biInter activation_event_measurable).2
  intro primes
  simpa only [activationEvent] using
    hindependent.measure_inter_preimage_eq_mul primes
      (fun _ _ => (measurableSet_singleton 0).compl)

private noncomputable def enumeratePrimes : Nat ≃ Nat.Primes :=
  nonempty_equiv_of_countable.some

private lemma activation_measure_tsum_eq_top (s : Real) (hs : 0 < s)
    (hs_le : s <= 1) :
    (∑' n, exponentProduct s hs (activationEvent (enumeratePrimes n))) = ∞ := by
  have hnotSummable :
      ¬Summable (fun p : Nat.Primes => activationProbability s p) := by
    intro hsummable
    have hexponent : -s < -1 := Nat.Primes.summable_rpow.mp <| by
      simpa only [activationProbability] using hsummable
    linarith
  let masses : Nat.Primes -> NNReal := fun p =>
    Real.toNNReal (activationProbability s p)
  have hnotSummableCoe : ¬Summable (fun p => (masses p : Real)) := by
    simpa only [masses, Real.coe_toNNReal _ (activation_probability_nonneg s _)] using
      hnotSummable
  have hprimeTsum : (∑' p, (masses p : ENNReal)) = ∞ :=
    ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr hnotSummableCoe
  rw [show (∑' n, exponentProduct s hs (activationEvent (enumeratePrimes n))) =
      ∑' n, (masses (enumeratePrimes n) : ENNReal) by
    apply tsum_congr
    intro n
    rw [exponent_product_activation]
    rfl]
  exact (enumeratePrimes.tsum_eq fun p => (masses p : ENNReal)).trans hprimeTsum

private lemma finite_support_disjoint_limsup (exponents : Nat.Primes -> Nat)
    (hfinite : (Function.support exponents).Finite) :
    exponents ∉ limsup (fun n => activationEvent (enumeratePrimes n)) atTop := by
  rw [mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite]
  intro hinfinite
  apply hinfinite
  simp only [activationEvent, Set.mem_preimage, Set.mem_compl_iff,
    Set.mem_singleton_iff] at hinfinite ⊢
  have heq : {n | exponents (enumeratePrimes n) ≠ 0} =
      enumeratePrimes ⁻¹' Function.support exponents := by
    rfl
  rw [heq]
  exact hfinite.preimage enumeratePrimes.injective.injOn

/-- Every finite prime-coordinate marginal is a compatible geometric probability law,
but for `0 < s <= 1` the canonical global product almost surely has infinite support. -/
theorem finite_marginals_and_global_support_contrast (s : Real) (hs : 0 < s) :
    (∀ primes : Finset Nat.Primes,
      IsProbabilityMeasure (Measure.pi fun p : primes => exponentMeasure s hs p)) ∧
    (∀ primes : Finset Nat.Primes,
      (exponentProduct s hs).map primes.restrict =
        Measure.pi fun p : primes => exponentMeasure s hs p) ∧
    (∀ (primes : Finset Nat.Primes) (exponents : Nat.Primes -> Nat),
      exponentProduct s hs (Set.pi primes fun p => {exponents p}) =
        ∏ p ∈ primes, ENNReal.ofReal
          ((1 - activationProbability s p) *
            (activationProbability s p) ^ (exponents p))) ∧
    (s <= 1 ->
      exponentProduct s hs {exponents | (Function.support exponents).Finite} = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro primes
    infer_instance
  · intro primes
    exact Measure.infinitePi_map_restrict (exponentMeasure s hs)
  · intro primes exponents
    rw [exponentProduct, Measure.infinitePi_pi]
    · apply Finset.prod_congr rfl
      intro p hp
      rw [exponentMeasure, geometricMeasure_singleton
        (exponent_success_ne_zero s hs p)]
      change ENNReal.ofReal
        ((1 - (1 - activationProbability s p)) ^ (exponents p) *
          (1 - activationProbability s p)) = _
      congr 1
      ring
    · intro p hp
      exact measurableSet_singleton _
  · intro hs_le
    let events : Nat -> Set (Nat.Primes -> Nat) :=
      fun n => activationEvent (enumeratePrimes n)
    have hevents : ∀ n, MeasurableSet (events n) :=
      fun n => activation_event_measurable (enumeratePrimes n)
    have hindependent : iIndepSet events (exponentProduct s hs) := by
      exact iIndepSet.precomp (s := activationEvent) (g := enumeratePrimes)
        enumeratePrimes.injective
        (activation_events_independent s hs)
    have hlimsup : exponentProduct s hs (limsup events atTop) = 1 :=
      measure_limsup_eq_one hevents hindependent
        (activation_measure_tsum_eq_top s hs hs_le)
    have hlimsupMeasurable : MeasurableSet (limsup events atTop) :=
      MeasurableSet.measurableSet_limsup hevents
    apply measure_mono_null
    · intro exponents hfinite
      exact Set.mem_compl <| finite_support_disjoint_limsup exponents hfinite
    · exact (prob_compl_eq_zero_iff hlimsupMeasurable).2 hlimsup

#print axioms finite_marginals_and_global_support_contrast

end D5.S3.Analytic.PrimeProducts.FiniteMarginalGlobalSupportContrast
