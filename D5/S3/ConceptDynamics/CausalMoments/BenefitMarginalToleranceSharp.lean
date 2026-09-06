/- GID: D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: For every nonnegative rational marginal tolerance pair, explicit response laws and checked contacts attain the exact Boolean benefit ambiguity and optimal residual budget. -/

import D5.S0.Certificates.RationalMomentAmbiguityCertificate
import D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
import Mathlib.Tactic.FinCases

/-!
The carrier and causal readouts are the existing FiniteResponseLaw (Bool × Bool),
controlSuccessMarginal, treatmentSuccessMarginal and benefitResponseMass.
Fin 4 is only their coefficient-array encoding, in order 00,01,10,11.

The tolerances bound discrepancies BETWEEN TWO models. They are not confidence
radii about one observed center. This theorem maximizes over all marginal
locations; it does not replace the data-dependent Frechet interval at fixed
marginals. Within each outcome mechanism, the two potential outcomes may be
dependent. No treatment/outcome graph or cross-world independence is added.

The common moment-error duality is an established finite LP principle. The
new obligations here are the actual two-branch certificates, validity at every
nonnegative tolerance, saturation, and transport to the existing causal law.
No generic strong-duality existence theorem is used as a hidden premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.BenefitMarginalToleranceSharp

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalAffineMomentCompression
open D5.S0.Certificates.RationalMomentQueryEnvelope
open D5.S0.Certificates.RationalMomentAmbiguityCertificate
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary

/-- The two actual potential-outcome indicators on the four response cells. -/
def benefitMomentFeature (i : Fin 4) (j : Fin 2) : ℚ :=
  if j = 0 then (if i = 2 ∨ i = 3 then 1 else 0)
  else (if i = 1 ∨ i = 3 then 1 else 0)

/-- The actual benefit event, indexed in order 00,01,10,11. -/
def benefitMomentQuery (i : Fin 4) : ℚ := if i = 1 then 1 else 0

/-- Exact worst discrepancy over all pairs of compatible marginal locations. -/
def benefitAmbiguityValue (eta0 eta1 : ℚ) : ℚ :=
  min 1 ((1 + eta0 + eta1) / 2)

/-- A data-only certificate for every tolerance. In the small-error regime the
high law is on 01/10 and the low law on 00/11; beyond total tolerance one the
high law is the point 01 and the low law stays diagonal. -/
def benefitToleranceCertificate (eta0 eta1 : ℚ) : ContactCertificate 4 2 :=
  let small := eta0 + eta1 ≤ 1
  let t := if small then (1 + eta0 + eta1) / 2 else 1
  let s := if small then (1 + eta0 - eta1) / 2 else min 1 eta0
  { high := fun i => if i = 1 then t else if i = 2 then 1 - t else 0
    low := fun i => if i = 0 then 1 - s else if i = 3 then s else 0
    envelope := if small then
      { offset := 0, coefficient := fun j => if j = 0 then -(1 / 2) else 1 / 2,
        lower := 0, upper := 1 / 2 }
      else { offset := 0, coefficient := fun _ => 0, lower := 0, upper := 1 } }

/-- Universal certificate validity, including zero tolerances, the joining
boundary, and arbitrarily large nonnegative tolerances. -/
theorem benefitToleranceCertificate_accepted (eta0 eta1 : ℚ)
    (h0 : 0 ≤ eta0) (h1 : 0 ≤ eta1) :
    checkContactCertificate benefitMomentFeature benefitMomentQuery
      (fun j => if j = 0 then eta0 else eta1)
      (benefitToleranceCertificate eta0 eta1) = true := by
  apply (checkContactCertificate_eq_true_iff benefitMomentFeature benefitMomentQuery
    (fun j => if j = 0 then eta0 else eta1)
    (benefitToleranceCertificate eta0 eta1)).mpr
  by_cases small : eta0 + eta1 ≤ 1
  · have e0 : eta0 ≤ 1 := by linarith
    have e1 : eta1 ≤ 1 := by linarith
    simp only [ValidContactCertificate, MomentTolerancePair, GlobalQueryEnvelope,
      benefitToleranceCertificate, if_pos small]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp <;> linarith
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff] <;> ring
    · intro i
      fin_cases i <;> norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff] <;> linarith
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff] <;> ring
    · intro j
      fin_cases j <;>
        norm_num [linearObjective, benefitMomentFeature, Fin.sum_univ_succ,
          Fin.ext_iff, -Fin.val_eq_zero_iff] <;>
        apply abs_le.mpr <;> constructor <;> linarith
    · intro i
      fin_cases i <;> norm_num [queryResidual, affineCoefficient,
        benefitMomentFeature, benefitMomentQuery, Fin.sum_univ_succ,
        Fin.ext_iff, -Fin.val_eq_zero_iff]
    · intro i hi
      fin_cases i <;> simp [queryResidual, affineCoefficient,
        benefitMomentFeature, benefitMomentQuery, Fin.sum_univ_succ,
        Fin.ext_iff, -Fin.val_eq_zero_iff] at hi ⊢
      norm_num
    · intro i hi
      fin_cases i <;> simp [queryResidual, affineCoefficient,
        benefitMomentFeature, benefitMomentQuery, Fin.sum_univ_succ,
        Fin.ext_iff, -Fin.val_eq_zero_iff] at hi ⊢
    · intro j
      fin_cases j <;> norm_num [linearObjective, benefitMomentFeature,
        Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff] <;> ring
  · have sn : 0 ≤ min (1 : ℚ) eta0 := le_min (by norm_num) h0
    have su : min (1 : ℚ) eta0 ≤ 1 := min_le_left _ _
    have se : min (1 : ℚ) eta0 ≤ eta0 := min_le_right _ _
    have remainder : 1 - min (1 : ℚ) eta0 ≤ eta1 := by
      by_cases h : eta0 ≤ 1
      · rw [min_eq_right h]
        linarith
      · rw [min_eq_left (le_of_lt (lt_of_not_ge h))]
        linarith
    simp only [ValidContactCertificate, MomentTolerancePair, GlobalQueryEnvelope,
      benefitToleranceCertificate, if_neg small]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff] <;> linarith
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff] <;> ring
    · intro j
      fin_cases j <;>
        norm_num [linearObjective, benefitMomentFeature, Fin.sum_univ_succ,
          Fin.ext_iff, -Fin.val_eq_zero_iff] <;>
        apply abs_le.mpr <;> constructor <;> linarith
    · intro i
      fin_cases i <;> norm_num [queryResidual, affineCoefficient,
        benefitMomentFeature, benefitMomentQuery, Fin.sum_univ_succ]
    · intro i hi
      fin_cases i <;> simp [queryResidual, affineCoefficient,
        benefitMomentFeature, benefitMomentQuery, Fin.ext_iff, -Fin.val_eq_zero_iff] at hi ⊢
    · intro i hi
      fin_cases i <;> simp [queryResidual, affineCoefficient,
        benefitMomentFeature, benefitMomentQuery, Fin.ext_iff, -Fin.val_eq_zero_iff] at hi ⊢
    · intro j
      fin_cases j <;> norm_num [linearObjective, benefitMomentFeature,
        Fin.sum_univ_succ]

/-- The two certificate branches meet at total tolerance one. -/
theorem benefitToleranceCertificate_budget (eta0 eta1 : ℚ) :
    residualBudget (fun j => if j = 0 then eta0 else eta1)
      (benefitToleranceCertificate eta0 eta1).envelope =
        benefitAmbiguityValue eta0 eta1 := by
  by_cases small : eta0 + eta1 ≤ 1
  · have h : (1 + eta0 + eta1) / 2 ≤ 1 := by linarith
    simp only [benefitToleranceCertificate, if_pos small, benefitAmbiguityValue,
      min_eq_right h]
    norm_num [residualBudget, momentToleranceCost, Fin.sum_univ_succ] <;> ring
  · have h : (1 : ℚ) ≤ (1 + eta0 + eta1) / 2 := by linarith
    simp only [benefitToleranceCertificate, if_neg small, benefitAmbiguityValue,
      min_eq_left h]
    norm_num [residualBudget, momentToleranceCost, Fin.sum_univ_succ]

private def indexedMass (mass : Bool × Bool → ℚ) : Fin 4 → ℚ :=
  fun i => if i = 0 then mass (false, false) else if i = 1 then mass (false, true)
    else if i = 2 then mass (true, false) else mass (true, true)

private theorem indexed_total (law : FiniteResponseLaw (Bool × Bool)) :
    (∑ i, indexedMass law.mass i) = 1 := by
  have h := law.total
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at h
  norm_num [indexedMass, Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]
  linarith

private theorem indexed_nonnegative (law : FiniteResponseLaw (Bool × Bool)) :
    ∀ i, 0 ≤ indexedMass law.mass i := by
  intro i
  fin_cases i
  · exact law.nonnegative (false, false)
  · exact law.nonnegative (false, true)
  · exact law.nonnegative (true, false)
  · exact law.nonnegative (true, true)

private theorem indexed_control (mass : Bool × Bool → ℚ) :
    linearObjective (fun i => benefitMomentFeature i 0) (indexedMass mass) =
      controlSuccessMarginal mass := by
  norm_num [linearObjective, benefitMomentFeature, indexedMass,
    controlSuccessMarginal, Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]

private theorem indexed_treatment (mass : Bool × Bool → ℚ) :
    linearObjective (fun i => benefitMomentFeature i 1) (indexedMass mass) =
      treatmentSuccessMarginal mass := by
  norm_num [linearObjective, benefitMomentFeature, indexedMass,
    treatmentSuccessMarginal, Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]

private theorem indexed_benefit (mass : Bool × Bool → ℚ) :
    linearObjective benefitMomentQuery (indexedMass mass) = benefitResponseMass mass := by
  norm_num [linearObjective, benefitMomentQuery, indexedMass,
    benefitResponseMass, Fin.sum_univ_succ, Fin.ext_iff, -Fin.val_eq_zero_iff]

private def responseLaw (mass : Fin 4 → ℚ) (hn : ∀ i, 0 ≤ mass i)
    (ht : (∑ i, mass i) = 1) : FiniteResponseLaw (Bool × Bool) where
  mass := fun
    | (false, false) => mass 0
    | (false, true) => mass 1
    | (true, false) => mass 2
    | (true, true) => mass 3
  nonnegative := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> exact hn _
  total := by
    norm_num [Fin.sum_univ_succ] at ht
    change mass 0 + (mass 1 + (mass 2 + mass 3)) = 1 at ht
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    linarith

private theorem indexed_responseLaw (mass : Fin 4 → ℚ) (hn : ∀ i, 0 ≤ mass i)
    (ht : (∑ i, mass i) = 1) : indexedMass (responseLaw mass hn ht).mass = mass := by
  funext i
  fin_cases i <;> rfl

private theorem indexed_pair (eta0 eta1 : ℚ)
    (high low : FiniteResponseLaw (Bool × Bool))
    (hc : |controlSuccessMarginal high.mass - controlSuccessMarginal low.mass| ≤ eta0)
    (ht : |treatmentSuccessMarginal high.mass - treatmentSuccessMarginal low.mass| ≤ eta1) :
    MomentTolerancePair benefitMomentFeature (fun j => if j = 0 then eta0 else eta1)
      (indexedMass high.mass) (indexedMass low.mass) := by
  refine ⟨indexed_nonnegative high, indexed_total high, indexed_nonnegative low,
    indexed_total low, ?_⟩
  intro j
  fin_cases j
  · simpa [indexed_control] using hc
  · simpa [indexed_treatment] using ht

/-- Exact causal ambiguity with attained original-carrier witnesses, together
with the matching least residual budget. No primal or dual optimizer is assumed. -/
theorem benefit_marginal_tolerance_sharp (eta0 eta1 : ℚ)
    (h0 : 0 ≤ eta0) (h1 : 0 ≤ eta1) :
    (∀ high low : FiniteResponseLaw (Bool × Bool),
      |controlSuccessMarginal high.mass - controlSuccessMarginal low.mass| ≤ eta0 →
      |treatmentSuccessMarginal high.mass - treatmentSuccessMarginal low.mass| ≤ eta1 →
      |benefitResponseMass high.mass - benefitResponseMass low.mass| ≤
        benefitAmbiguityValue eta0 eta1) ∧
    (∃ high low : FiniteResponseLaw (Bool × Bool),
      |controlSuccessMarginal high.mass - controlSuccessMarginal low.mass| ≤ eta0 ∧
      |treatmentSuccessMarginal high.mass - treatmentSuccessMarginal low.mass| ≤ eta1 ∧
      benefitResponseMass high.mass - benefitResponseMass low.mass =
        benefitAmbiguityValue eta0 eta1) ∧
    IsLeast (residualBudgetValues benefitMomentFeature benefitMomentQuery
      (fun j => if j = 0 then eta0 else eta1)) (benefitAmbiguityValue eta0 eta1) := by
  let certificate := benefitToleranceCertificate eta0 eta1
  have accepted := benefitToleranceCertificate_accepted eta0 eta1 h0 h1
  have valid := (checkContactCertificate_eq_true_iff benefitMomentFeature benefitMomentQuery
    (fun j => if j = 0 then eta0 else eta1) certificate).mp accepted
  have extremes := checkContactCertificate_sound benefitMomentFeature benefitMomentQuery
    (fun j => if j = 0 then eta0 else eta1) certificate accepted
  have budget := benefitToleranceCertificate_budget eta0 eta1
  change residualBudget (fun j => if j = 0 then eta0 else eta1) certificate.envelope = _ at budget
  rw [budget] at extremes
  refine ⟨?_, ?_, extremes.2⟩
  · intro high low hc ht
    have pair := indexed_pair eta0 eta1 high low hc ht
    have bound := extremes.1.2
      (show |linearObjective benefitMomentQuery (indexedMass high.mass) -
          linearObjective benefitMomentQuery (indexedMass low.mass)| ∈
        ambiguityValues benefitMomentFeature benefitMomentQuery
          (fun j => if j = 0 then eta0 else eta1) from
        ⟨indexedMass high.mass, indexedMass low.mass, pair, rfl⟩)
    simpa only [indexed_benefit] using bound
  · let high := responseLaw certificate.high valid.1.1 valid.1.2.1
    let low := responseLaw certificate.low valid.1.2.2.1 valid.1.2.2.2.1
    have ih : indexedMass high.mass = certificate.high := indexed_responseLaw _ _ _
    have il : indexedMass low.mass = certificate.low := indexed_responseLaw _ _ _
    have hc := valid.1.2.2.2.2 (0 : Fin 2)
    have ht := valid.1.2.2.2.2 (1 : Fin 2)
    have gap := contact_gap_eq_budget benefitMomentFeature benefitMomentQuery
      (fun j => if j = 0 then eta0 else eta1) certificate valid
    rw [← ih, ← il, indexed_control, indexed_control] at hc
    rw [← ih, ← il, indexed_treatment, indexed_treatment] at ht
    rw [← ih, ← il, indexed_benefit, indexed_benefit, budget] at gap
    exact ⟨high, low, by simpa using hc, by simpa using ht, gap⟩

#print axioms benefitToleranceCertificate_accepted
#print axioms benefit_marginal_tolerance_sharp

end D5.S3.ConceptDynamics.CausalMoments.BenefitMarginalToleranceSharp
