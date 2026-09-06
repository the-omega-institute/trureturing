/- GID: D5/S0/Certificates/RationalMomentQueryEnvelope
   generality: G
   mirror-B: D5/B/S0/Certificates/RationalMomentQueryEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Certificates/RationalAffineMomentCompression]
   utility: kind=checker; basis=consumer=D5/S3/ConceptDynamics/PartialIdentification/RankAdaptiveSparseCausalWitness.checked_compressed_query_decision
   digest: Pointwise rational affine residual envelopes certify uniform query-error bounds for one checked compression; a zero weighted square residual yields exact reconstruction on its support. -/

import D5.S0.Certificates.RationalAffineMomentCompression

/- Cross-lane audit (2026-09-06): loning's #5326 separates preservation of a
   chosen behavior from preservation of additional invariants. #5750 selects a
   common rule before unknown acquisition parameters, and #5803 checks the
   actual coefficient identity rather than a numerical proxy. The present
   theorem concerns finite rational moment laws only; none of their physical
   claims is imported. Reuse existing replay, expectations and support descent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.RationalMomentQueryEnvelope

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalMomentElimination
open D5.S0.Certificates.RationalMomentReplay
open D5.S0.Certificates.RationalAffineMomentCompression

/-- Data describing an affine predictor and a pointwise residual interval. -/
structure QueryEnvelope (d : Nat) where
  offset : ℚ
  coefficient : Fin d → ℚ
  lower : ℚ
  upper : ℚ

/-- Residual relative to the specified affine predictor, before expectation. -/
def queryResidual {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (query : Fin n → ℚ) (envelope : QueryEnvelope d) : Fin n → ℚ :=
  fun i => query i - affineCoefficient feature envelope.offset envelope.coefficient i

/-- Center of the query interval computed from the retained moments. -/
def predictedMean {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (weight : Fin n → ℚ) (envelope : QueryEnvelope d) : ℚ :=
  envelope.offset + ∑ j, envelope.coefficient j * linearObjective (fun i => feature i j) weight

/-- The residual interval must hold at every original nonzero atom. -/
def ValidQueryEnvelope {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (weight query : Fin n → ℚ) (envelope : QueryEnvelope d) : Prop :=
  ∀ i, weight i ≠ 0 → envelope.lower ≤ queryResidual feature query envelope i ∧
    queryResidual feature query envelope i ≤ envelope.upper

/-- Exact finite check, including the actual omitted query coefficient. -/
def checkQueryEnvelope {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (weight query : Fin n → ℚ) (envelope : QueryEnvelope d) : Bool :=
  @decide (ValidQueryEnvelope feature weight query envelope)
    (by unfold ValidQueryEnvelope; infer_instance)

theorem checkQueryEnvelope_eq_true_iff {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (weight query : Fin n → ℚ) (envelope : QueryEnvelope d) :
    checkQueryEnvelope feature weight query envelope = true ↔
      ValidQueryEnvelope feature weight query envelope := by
  simp only [checkQueryEnvelope, decide_eq_true_eq]

/-- Nonnegative normalized weights transfer a support-local residual interval
into an exact expectation enclosure. No statistical estimation is assumed. -/
theorem query_interval_of_envelope {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (weight query : Fin n → ℚ) (envelope : QueryEnvelope d)
    (nonnegative : ∀ i, 0 ≤ weight i) (total : (∑ i, weight i) = 1)
    (valid : ValidQueryEnvelope feature weight query envelope) :
    predictedMean feature weight envelope + envelope.lower ≤ linearObjective query weight ∧
      linearObjective query weight ≤ predictedMean feature weight envelope + envelope.upper := by
  have pointwise : ∀ i,
      envelope.lower * weight i ≤ queryResidual feature query envelope i * weight i ∧
      queryResidual feature query envelope i * weight i ≤ envelope.upper * weight i := by
    intro i
    by_cases zero : weight i = 0
    · simp only [zero, mul_zero, le_refl, and_self]
    · exact ⟨mul_le_mul_of_nonneg_right (valid i zero).1 (nonnegative i),
        mul_le_mul_of_nonneg_right (valid i zero).2 (nonnegative i)⟩
  have lower := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (pointwise i).1)
  have upper := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (pointwise i).2)
  rw [← Finset.mul_sum, total, mul_one] at lower
  rw [← Finset.mul_sum, total, mul_one] at upper
  have residual_identity : linearObjective (queryResidual feature query envelope) weight =
      linearObjective query weight - predictedMean feature weight envelope := by
    calc
      _ = linearObjective query weight -
          linearObjective (affineCoefficient feature envelope.offset envelope.coefficient) weight := by
        simp only [linearObjective, queryResidual, sub_mul, Finset.sum_sub_distrib]
      _ = _ := by rw [linearObjective_affineCoefficient feature weight total] <;> rfl
  change envelope.lower ≤ linearObjective (queryResidual feature query envelope) weight at lower
  change linearObjective (queryResidual feature query envelope) weight ≤ envelope.upper at upper
  rw [residual_identity] at lower upper
  constructor <;> linarith

/-- Both original and compressed query values lie in the same residual enclosure.
The center uses original retained moments, not the unknown omitted query mean. -/
theorem checked_query_enclosures {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (weight result query : Fin n → ℚ)
    (steps : List (EliminationStep n)) (envelope : QueryEnvelope d)
    (accepted : checkCompression feature weight steps = some result)
    (certified : checkQueryEnvelope feature weight query envelope = true) :
    (predictedMean feature weight envelope + envelope.lower ≤ linearObjective query weight ∧
      linearObjective query weight ≤ predictedMean feature weight envelope + envelope.upper) ∧
    (predictedMean feature weight envelope + envelope.lower ≤ linearObjective query result ∧
      linearObjective query result ≤ predictedMean feature weight envelope + envelope.upper) := by
  have input := checkCompression_input_probability feature weight result steps accepted
  have valid := (checkQueryEnvelope_eq_true_iff feature weight query envelope).mp certified
  obtain ⟨hn, ht, moments, contained, _, _⟩ := checkCompression_sound feature weight result steps accepted
  have output_valid : ValidQueryEnvelope feature result query envelope := by
    intro i hi
    have member := contained (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    exact valid i (Finset.mem_filter.mp member).2
  have output := query_interval_of_envelope feature result query envelope hn ht output_valid
  have same_center : predictedMean feature result envelope = predictedMean feature weight envelope := by
    unfold predictedMean
    simp_rw [moments]
  rw [same_center] at output
  exact ⟨query_interval_of_envelope feature weight query envelope input.1 input.2 valid, output⟩

/-- An omitted query changes by at most the residual oscillation. In particular,
a symmetric residual bound epsilon gives at most 2*epsilon, not epsilon. -/
theorem checked_query_error_bound {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (weight result query : Fin n → ℚ)
    (steps : List (EliminationStep n)) (envelope : QueryEnvelope d)
    (accepted : checkCompression feature weight steps = some result)
    (certified : checkQueryEnvelope feature weight query envelope = true) :
    |linearObjective query result - linearObjective query weight| ≤ envelope.upper - envelope.lower := by
  obtain ⟨original, compressed⟩ :=
    checked_query_enclosures feature weight result query steps envelope accepted certified
  apply abs_le.mpr
  constructor <;> linarith [original.1, original.2, compressed.1, compressed.2]

/-- The accepted compression is fixed before the query-family parameter is
chosen. A certified pointwise envelope for every parameter gives one uniform
family guarantee without rerunning compression for individual queries. -/
theorem checked_uniform_query_family {n d : Nat} {Parameter : Type*}
    (feature : Fin n → Fin d → ℚ) (weight result : Fin n → ℚ)
    (steps : List (EliminationStep n))
    (query : Parameter → Fin n → ℚ) (envelope : Parameter → QueryEnvelope d)
    (accepted : checkCompression feature weight steps = some result)
    (certified : ∀ parameter, checkQueryEnvelope feature weight (query parameter) (envelope parameter) = true) :
    ∀ parameter, |linearObjective (query parameter) result - linearObjective (query parameter) weight| ≤
      (envelope parameter).upper - (envelope parameter).lower := by
  intro parameter
  exact checked_query_error_bound feature weight result (query parameter) steps
    (envelope parameter) accepted (certified parameter)

/-- Zero weighted square residual is equivalent to zero residual at every active
atom. A zero signed mean alone does not have this consequence. -/
theorem residual_energy_zero_iff {n : Nat} (weight residual : Fin n → ℚ)
    (nonnegative : ∀ i, 0 ≤ weight i) :
    linearObjective (fun i => residual i ^ 2) weight = 0 ↔
      ∀ i, weight i ≠ 0 → residual i = 0 := by
  constructor
  · intro energy i active
    have point_le : residual i ^ 2 * weight i ≤ ∑ j, residual j ^ 2 * weight j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg (residual j)) (nonnegative j))
        (Finset.mem_univ i)
    change residual i ^ 2 * weight i ≤ linearObjective (fun j => residual j ^ 2) weight at point_le
    rw [energy] at point_le
    have zero := le_antisymm point_le (mul_nonneg (sq_nonneg (residual i)) (nonnegative i))
    have square_zero : residual i ^ 2 = 0 := (mul_eq_zero.mp zero).resolve_right active
    exact mul_self_eq_zero.mp (by simpa only [pow_two] using square_zero)
  · intro vanishes
    unfold linearObjective
    apply Finset.sum_eq_zero
    intro i _
    dsimp only
    by_cases zero : weight i = 0
    · simp only [zero, mul_zero]
    · rw [vanishes i zero, zero_pow (by decide : 2 ≠ 0), zero_mul]

/-- A certified zero square residual upgrades reconstruction to exact query
preservation through every accepted compression of the nominated features. -/
theorem checked_query_exact_of_zero_residual_energy {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (weight result query : Fin n → ℚ)
    (steps : List (EliminationStep n)) (constant : ℚ) (coefficient : Fin d → ℚ)
    (accepted : checkCompression feature weight steps = some result)
    (energy : linearObjective (fun i =>
      (query i - affineCoefficient feature constant coefficient i) ^ 2) weight = 0) :
    linearObjective query result = linearObjective query weight := by
  have input := checkCompression_input_probability feature weight result steps accepted
  have vanishes := (residual_energy_zero_iff weight
    (fun i => query i - affineCoefficient feature constant coefficient i) input.1).mp energy
  let envelope : QueryEnvelope d := ⟨constant, coefficient, 0, 0⟩
  have certified : checkQueryEnvelope feature weight query envelope = true := by
    apply (checkQueryEnvelope_eq_true_iff feature weight query envelope).mpr
    intro i hi
    change 0 ≤ query i - affineCoefficient feature constant coefficient i ∧
      query i - affineCoefficient feature constant coefficient i ≤ 0
    rw [vanishes i hi]
    exact ⟨le_rfl, le_rfl⟩
  have bound := checked_query_error_bound feature weight result query steps envelope accepted certified
  change |linearObjective query result - linearObjective query weight| ≤ 0 - 0 at bound
  have zero := le_antisymm (by simpa only [sub_self] using bound)
    (abs_nonneg (linearObjective query result - linearObjective query weight))
  exact sub_eq_zero.mp (abs_eq_zero.mp zero)

/-- A signed residual with zero mean can hide an omitted probability query.
The existing valid mean-preserving replay changes that event from 2/3 to zero. -/
theorem signed_residual_cancellation_counterexample :
    let query : Fin 3 → ℚ := fun i => if i = 1 then 0 else 1
    let weight : Fin 3 → ℚ := fun _ => 1 / 3
    linearObjective (fun i => query i - 2 / 3) weight = 0 ∧
      linearObjective (fun i => (query i - 2 / 3) ^ 2) weight = 2 / 9 ∧
      linearObjective query weight = 2 / 3 ∧
      (checkCompression (n := 3) (d := 1) (fun i _ => (i.val : ℚ)) weight
        [{ direction := fun i => if i = 1 then -2 else 1, pivot := 0 }]).map
          (linearObjective query) = some 0 := by
  decide +kernel

#print axioms checked_query_error_bound
#print axioms checked_uniform_query_family
#print axioms residual_energy_zero_iff
#print axioms checked_query_exact_of_zero_residual_energy
#print axioms signed_residual_cancellation_counterexample

end D5.S0.Certificates.RationalMomentQueryEnvelope
