/- GID: D5/S0/Certificates/RationalMomentAmbiguityCertificate
   generality: G
   mirror-B: D5/B/S0/Certificates/RationalMomentAmbiguityCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefit_marginal_tolerance_sharp
   digest: Rational contact witnesses certify both maximal query ambiguity and minimal residual budget under componentwise moment tolerances. -/

import D5.S0.Certificates.RationalMomentQueryEnvelope

/-!
The two vectors below are independent candidate probability laws on the same
finite carrier. No support-containment or compression assumption is imposed.
The envelope is checked on that entire carrier. For a smaller allowed carrier,
instantiate the definitions on its finite subtype before producing a certificate.

Library audit, 2026-09-06: the existing query_interval_of_envelope and affine
expectation lemmas supply the numerical semantics. LinearObjectiveDual supplies
weak dual certificates but not existence of an optimizer. The dev theorem
ProjectiveStrongDuality assumes finite strong duality. Dvorak--Kolmogorov's
StandardLP.strongDuality is a genuine external owner (madvorak/duality v3.2.0),
but its Lean 4.18 closure has not been ported into this Lean 4.33 repository.
This file checks proposed primal/dual contacts; it does not re-prove that owner
or assume its missing dependency. The Boolean consumer supplies certificates
for every nonnegative rational tolerance pair, without optimizer hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.RationalMomentAmbiguityCertificate

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalMomentElimination
open D5.S0.Certificates.RationalMomentReplay
open D5.S0.Certificates.RationalAffineMomentCompression
open D5.S0.Certificates.RationalMomentQueryEnvelope

/-- Two normalized nonnegative laws whose retained moments are close. The
bounds compare the two laws directly, rather than comparing each to a center. -/
def MomentTolerancePair {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (tolerance : Fin d → ℚ) (high low : Fin n → ℚ) : Prop :=
  (∀ i, 0 ≤ high i) ∧ (∑ i, high i) = 1 ∧
  (∀ i, 0 ≤ low i) ∧ (∑ i, low i) = 1 ∧
  ∀ j, |linearObjective (fun i => feature i j) high -
    linearObjective (fun i => feature i j) low| ≤ tolerance j

/-- The residual interval is valid on every allowed atom, independently of a
particular law's positive support. -/
def GlobalQueryEnvelope {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (query : Fin n → ℚ) (envelope : QueryEnvelope d) : Prop :=
  ∀ i, envelope.lower ≤ queryResidual feature query envelope i ∧
    queryResidual feature query envelope i ≤ envelope.upper

/-- Cost of moment uncertainty for the proposed affine predictor. -/
def momentToleranceCost {d : Nat} (tolerance : Fin d → ℚ)
    (envelope : QueryEnvelope d) : ℚ :=
  ∑ j, |envelope.coefficient j| * tolerance j

/-- Residual width plus the moment-uncertainty cost. -/
def residualBudget {d : Nat} (tolerance : Fin d → ℚ)
    (envelope : QueryEnvelope d) : ℚ :=
  envelope.upper - envelope.lower + momentToleranceCost tolerance envelope

private theorem center_difference {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (high low : Fin n → ℚ)
    (envelope : QueryEnvelope d) :
    predictedMean feature high envelope - predictedMean feature low envelope =
      ∑ j, envelope.coefficient j *
        (linearObjective (fun i => feature i j) high -
          linearObjective (fun i => feature i j) low) := by
  unfold predictedMean
  calc
    _ = (∑ j, envelope.coefficient j * linearObjective (fun i => feature i j) high) -
        ∑ j, envelope.coefficient j * linearObjective (fun i => feature i j) low := by ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem center_difference_bound {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (tolerance : Fin d → ℚ)
    (high low : Fin n → ℚ) (envelope : QueryEnvelope d)
    (close : ∀ j, |linearObjective (fun i => feature i j) high -
      linearObjective (fun i => feature i j) low| ≤ tolerance j) :
    |predictedMean feature high envelope - predictedMean feature low envelope| ≤
      momentToleranceCost tolerance envelope := by
  have pointwise (j : Fin d) :
      |envelope.coefficient j * (linearObjective (fun i => feature i j) high -
        linearObjective (fun i => feature i j) low)| ≤
          |envelope.coefficient j| * tolerance j := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (close j) (abs_nonneg _)
  rw [center_difference]
  unfold momentToleranceCost
  apply abs_le.mpr
  constructor
  · have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
      (abs_le.mp (pointwise j)).1)
    simpa only [Finset.sum_neg_distrib] using h
  · exact Finset.sum_le_sum (fun j _ => (abs_le.mp (pointwise j)).2)

/-- A single global envelope bounds every pair with the nominated moment
errors. Zero tolerances recover exact moment-matching ambiguity. -/
theorem query_gap_le_residualBudget {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (query : Fin n → ℚ)
    (tolerance : Fin d → ℚ) (high low : Fin n → ℚ)
    (envelope : QueryEnvelope d)
    (pair : MomentTolerancePair feature tolerance high low)
    (valid : GlobalQueryEnvelope feature query envelope) :
    |linearObjective query high - linearObjective query low| ≤
      residualBudget tolerance envelope := by
  obtain ⟨hn, ht, ln, lt, close⟩ := pair
  have h := query_interval_of_envelope feature high query envelope hn ht (fun i _ => valid i)
  have l := query_interval_of_envelope feature low query envelope ln lt (fun i _ => valid i)
  have c := center_difference_bound feature tolerance high low envelope close
  unfold residualBudget
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2, l.1, l.2, (abs_le.mp c).1, (abs_le.mp c).2]

private theorem residual_mean {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (query weight : Fin n → ℚ) (envelope : QueryEnvelope d)
    (total : (∑ i, weight i) = 1) :
    linearObjective (queryResidual feature query envelope) weight =
      linearObjective query weight - predictedMean feature weight envelope := by
  calc
    _ = linearObjective query weight -
        linearObjective (affineCoefficient feature envelope.offset envelope.coefficient) weight := by
      simp only [linearObjective, queryResidual, sub_mul, Finset.sum_sub_distrib]
    _ = _ := by rw [linearObjective_affineCoefficient feature weight total]; rfl

/-- Exact gap accounting. Under feasibility, each of the three displayed sums
is nonnegative: upper contacts, lower contacts, and signed moment alignment. -/
theorem primal_dual_gap_identity {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (query : Fin n → ℚ)
    (tolerance : Fin d → ℚ) (high low : Fin n → ℚ)
    (envelope : QueryEnvelope d)
    (ht : (∑ i, high i) = 1) (lt : (∑ i, low i) = 1) :
    residualBudget tolerance envelope -
      (linearObjective query high - linearObjective query low) =
      (∑ i, (envelope.upper - queryResidual feature query envelope i) * high i) +
      (∑ i, (queryResidual feature query envelope i - envelope.lower) * low i) +
      ∑ j, (|envelope.coefficient j| * tolerance j - envelope.coefficient j *
        (linearObjective (fun i => feature i j) high -
          linearObjective (fun i => feature i j) low)) := by
  have hsum : (∑ i, (envelope.upper - queryResidual feature query envelope i) * high i) =
      envelope.upper - linearObjective (queryResidual feature query envelope) high := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ht, mul_one]
    rfl
  have lsum : (∑ i, (queryResidual feature query envelope i - envelope.lower) * low i) =
      linearObjective (queryResidual feature query envelope) low - envelope.lower := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, lt, mul_one]
    rfl
  rw [hsum, lsum, residual_mean feature query high envelope ht,
    residual_mean feature query low envelope lt, Finset.sum_sub_distrib,
    ← center_difference]
  unfold residualBudget momentToleranceCost
  ring

/-- Raw certificate data. Probability, residual and contact facts are checked
from these rational values; the payload contains no proof fields. -/
structure ContactCertificate (n d : Nat) where
  high : Fin n → ℚ
  low : Fin n → ℚ
  envelope : QueryEnvelope d

/-- Contact conditions saturate all three nonnegative contributions to the
primal-dual gap. The upper and lower witnesses use the same moment contract. -/
def ValidContactCertificate {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (query : Fin n → ℚ)
    (tolerance : Fin d → ℚ) (certificate : ContactCertificate n d) : Prop :=
  MomentTolerancePair feature tolerance certificate.high certificate.low ∧
  GlobalQueryEnvelope feature query certificate.envelope ∧
  (∀ i, certificate.high i ≠ 0 →
    queryResidual feature query certificate.envelope i = certificate.envelope.upper) ∧
  (∀ i, certificate.low i ≠ 0 →
    queryResidual feature query certificate.envelope i = certificate.envelope.lower) ∧
  ∀ j, certificate.envelope.coefficient j *
    (linearObjective (fun i => feature i j) certificate.high -
      linearObjective (fun i => feature i j) certificate.low) =
        |certificate.envelope.coefficient j| * tolerance j

/-- Exact rational checker for a proposed pair and its residual certificate. -/
def checkContactCertificate {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (query : Fin n → ℚ)
    (tolerance : Fin d → ℚ) (certificate : ContactCertificate n d) : Bool :=
  @decide (ValidContactCertificate feature query tolerance certificate)
    (by unfold ValidContactCertificate MomentTolerancePair GlobalQueryEnvelope; infer_instance)

theorem checkContactCertificate_eq_true_iff {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (query : Fin n → ℚ)
    (tolerance : Fin d → ℚ) (certificate : ContactCertificate n d) :
    checkContactCertificate feature query tolerance certificate = true ↔
      ValidContactCertificate feature query tolerance certificate := by
  simp only [checkContactCertificate, decide_eq_true_eq]

/-- A valid contact payload attains its budget as an oriented query gap. -/
theorem contact_gap_eq_budget {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (query : Fin n → ℚ)
    (tolerance : Fin d → ℚ) (certificate : ContactCertificate n d)
    (valid : ValidContactCertificate feature query tolerance certificate) :
    linearObjective query certificate.high - linearObjective query certificate.low =
      residualBudget tolerance certificate.envelope := by
  obtain ⟨pair, _, hc, lc, alignment⟩ := valid
  have gap := primal_dual_gap_identity feature query tolerance certificate.high certificate.low
    certificate.envelope pair.2.1 pair.2.2.2.1
  have hz : (∑ i, (certificate.envelope.upper -
      queryResidual feature query certificate.envelope i) * certificate.high i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases zero : certificate.high i = 0
    · simp only [zero, mul_zero]
    · rw [hc i zero, sub_self, zero_mul]
  have lz : (∑ i, (queryResidual feature query certificate.envelope i -
      certificate.envelope.lower) * certificate.low i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases zero : certificate.low i = 0
    · simp only [zero, mul_zero]
    · rw [lc i zero, sub_self, zero_mul]
  have az : (∑ j, (|certificate.envelope.coefficient j| * tolerance j -
      certificate.envelope.coefficient j *
        (linearObjective (fun i => feature i j) certificate.high -
          linearObjective (fun i => feature i j) certificate.low))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [alignment j, sub_self]
  rw [hz, lz, az] at gap
  linarith

/-- All query differences allowed by the fixed finite moment-error contract. -/
def ambiguityValues {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (query : Fin n → ℚ) (tolerance : Fin d → ℚ) : Set ℚ :=
  {value | ∃ high low, MomentTolerancePair feature tolerance high low ∧
    value = |linearObjective query high - linearObjective query low|}

/-- All globally valid affine residual budgets, on the same allowed carrier. -/
def residualBudgetValues {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (query : Fin n → ℚ) (tolerance : Fin d → ℚ) : Set ℚ :=
  {value | ∃ envelope, GlobalQueryEnvelope feature query envelope ∧
    value = residualBudget tolerance envelope}

/-- Acceptance certifies an attained maximum and an attained minimum with the
same value. This is a soundness theorem, not a general optimizer-discovery or
certificate-existence theorem. -/
theorem checkContactCertificate_sound {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (query : Fin n → ℚ)
    (tolerance : Fin d → ℚ) (certificate : ContactCertificate n d)
    (accepted : checkContactCertificate feature query tolerance certificate = true) :
    IsGreatest (ambiguityValues feature query tolerance)
      (residualBudget tolerance certificate.envelope) ∧
    IsLeast (residualBudgetValues feature query tolerance)
      (residualBudget tolerance certificate.envelope) := by
  have valid := (checkContactCertificate_eq_true_iff feature query tolerance certificate).mp accepted
  have bound := query_gap_le_residualBudget feature query tolerance certificate.high certificate.low
    certificate.envelope valid.1 valid.2.1
  have nonnegative := (abs_nonneg _).trans bound
  have gap := contact_gap_eq_budget feature query tolerance certificate valid
  have abs_gap : |linearObjective query certificate.high - linearObjective query certificate.low| =
      residualBudget tolerance certificate.envelope := by
    rw [gap, abs_of_nonneg nonnegative]
  constructor
  · constructor
    · exact ⟨certificate.high, certificate.low, valid.1, abs_gap.symm⟩
    · rintro value ⟨high, low, pair, rfl⟩
      exact query_gap_le_residualBudget feature query tolerance high low certificate.envelope
        pair valid.2.1
  · constructor
    · exact ⟨certificate.envelope, valid.2.1, rfl⟩
    · rintro value ⟨envelope, envelope_valid, rfl⟩
      have h := query_gap_le_residualBudget feature query tolerance certificate.high certificate.low
        envelope valid.1 envelope_valid
      rw [abs_gap] at h
      exact h

/-- Compress the two contact supports separately using only the d retained
moments. No additional query coordinate is needed: support containment keeps
both residual levels and moment preservation keeps the signed alignment. -/
theorem contact_certificate_preserved_by_compression {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (query : Fin n → ℚ)
    (tolerance : Fin d → ℚ) (certificate : ContactCertificate n d)
    (high low : Fin n → ℚ) (highSteps lowSteps : List (EliminationStep n))
    (valid : ValidContactCertificate feature query tolerance certificate)
    (highAccepted : checkCompression feature certificate.high highSteps = some high)
    (lowAccepted : checkCompression feature certificate.low lowSteps = some low) :
    ValidContactCertificate feature query tolerance
      { certificate with high := high, low := low } ∧
    (activeAtoms high).card ≤ d + 1 ∧ (activeAtoms low).card ≤ d + 1 ∧
    linearObjective query high - linearObjective query low =
      linearObjective query certificate.high - linearObjective query certificate.low := by
  obtain ⟨hn, ht, hm, hs, hb, _⟩ :=
    checkCompression_sound feature certificate.high high highSteps highAccepted
  obtain ⟨ln, lt, lm, ls, lb, _⟩ :=
    checkCompression_sound feature certificate.low low lowSteps lowAccepted
  have newValid : ValidContactCertificate feature query tolerance
      { certificate with high := high, low := low } := by
    refine ⟨⟨hn, ht, ln, lt, ?_⟩, valid.2.1, ?_, ?_, ?_⟩
    · intro j
      simpa only [hm j, lm j] using valid.1.2.2.2.2 j
    · intro i hi
      have original := hs (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      exact valid.2.2.1 i (Finset.mem_filter.mp original).2
    · intro i hi
      have original := ls (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      exact valid.2.2.2.1 i (Finset.mem_filter.mp original).2
    · intro j
      simpa only [hm j, lm j] using valid.2.2.2.2 j
  refine ⟨newValid, hb, lb, ?_⟩
  calc
    _ = residualBudget tolerance certificate.envelope :=
      contact_gap_eq_budget feature query tolerance
        { certificate with high := high, low := low } newValid
    _ = _ := (contact_gap_eq_budget feature query tolerance certificate valid).symm

#print axioms query_gap_le_residualBudget
#print axioms primal_dual_gap_identity
#print axioms checkContactCertificate_sound
#print axioms contact_certificate_preserved_by_compression

end D5.S0.Certificates.RationalMomentAmbiguityCertificate
