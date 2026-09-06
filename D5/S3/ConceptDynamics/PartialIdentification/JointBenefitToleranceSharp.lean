/- GID: D5/S3/ConceptDynamics/PartialIdentification/JointBenefitToleranceSharp
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/JointBenefitToleranceSharp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/ConceptDynamics/PartialIdentification/BenefitMarginalToleranceSharp]
   utility: none
   digest: The exact four-tolerance ambiguity of simultaneous benefit in two independent mechanisms is attained by one of three explicit product-model configurations. -/

import D5.S3.ConceptDynamics.PartialIdentification.BenefitMarginalToleranceSharp
import D5.S3.ConceptDynamics.PartialIdentification.MarkovianJointMechanismBenefitSharpBounds

/-!
Research target: the multi-component optimization extension left open in
Arroyo et al., arXiv:2509.03548v1, Section 6. This source solves one explicit
bilinear robustness problem within that broader direction. It does not give a
column-generation algorithm, settle arbitrary multi-intervention SCMs, or
assert priority for a literature-wide new formula.

Library audit (2026-09-06): reuse the actual two-mechanism model, product query,
complete four-cell response law, and the single-mechanism tolerance theorem.
The new proof does not multiply individual ambiguity bounds. It retains the
coupling between each mechanism's two candidate benefit values, proves a
three-corner bilinear envelope, and constructs attaining product models.
Tolerances compare two models directly. No fixed observed center, sampling
confidence statement, or shared-root conditional independence is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.JointBenefitToleranceSharp

open scoped BigOperators
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianJointMechanismBenefitSharpBounds
open D5.S3.ConceptDynamics.PartialIdentification.BenefitMarginalToleranceSharp

/-- Componentwise comparison of the four actual intervention marginals. -/
def JointMarginalTolerance (high low : MarkovianJointMechanismModel)
    (eta10 eta11 eta20 eta21 : ℚ) : Prop :=
  |controlSuccessMarginal high.firstLaw.mass - controlSuccessMarginal low.firstLaw.mass| ≤ eta10 ∧
  |treatmentSuccessMarginal high.firstLaw.mass - treatmentSuccessMarginal low.firstLaw.mass| ≤ eta11 ∧
  |controlSuccessMarginal high.secondLaw.mass - controlSuccessMarginal low.secondLaw.mass| ≤ eta20 ∧
  |treatmentSuccessMarginal high.secondLaw.mass - treatmentSuccessMarginal low.secondLaw.mass| ≤ eta21

/-- Three competing configurations: uncertainty in either mechanism alone, or
both upper models at certain benefit with their lower models jointly depleted. -/
def jointBenefitAmbiguityValue (eta10 eta11 eta20 eta21 : ℚ) : ℚ :=
  let a := benefitAmbiguityValue eta10 eta11
  let b := benefitAmbiguityValue eta20 eta21
  max (max a b) (1 - 4 * (1 - a) * (1 - b))

private theorem benefit_unit (law : FiniteResponseLaw (Bool × Bool)) :
    0 ≤ benefitResponseMass law.mass ∧ benefitResponseMass law.mass ≤ 1 := by
  refine ⟨law.nonnegative (false, true), ?_⟩
  calc
    benefitResponseMass law.mass ≤ ∑ r, law.mass r :=
      Finset.single_le_sum (fun r _ => law.nonnegative r) (Finset.mem_univ (false, true))
    _ = 1 := law.total

private theorem ambiguity_unit (eta0 eta1 : ℚ) (h0 : 0 ≤ eta0) (h1 : 0 ≤ eta1) :
    0 ≤ benefitAmbiguityValue eta0 eta1 ∧ benefitAmbiguityValue eta0 eta1 ≤ 1 := by
  unfold benefitAmbiguityValue
  exact ⟨le_min (by norm_num) (by linarith), min_le_left _ _⟩

/-- Retaining only a bound on the difference of benefits loses information.
This one-sided affine relation retains the individual endpoint location. -/
private theorem benefit_pair_constraint (eta0 eta1 : ℚ)
    (high low : FiniteResponseLaw (Bool × Bool))
    (hc : |controlSuccessMarginal high.mass - controlSuccessMarginal low.mass| ≤ eta0)
    (ht : |treatmentSuccessMarginal high.mass - treatmentSuccessMarginal low.mass| ≤ eta1) :
    2 * benefitResponseMass high.mass - 2 * benefitAmbiguityValue eta0 eta1 ≤
      benefitResponseMass low.mass := by
  by_cases small : eta0 + eta1 ≤ 1
  · have aa : benefitAmbiguityValue eta0 eta1 = (1 + eta0 + eta1) / 2 := by
      apply min_eq_right
      linarith
    have total := high.total
    simp only [Fintype.sum_prod_type, Fintype.sum_bool] at total
    have h00 := high.nonnegative (false, false)
    have h11 := high.nonnegative (true, true)
    have l10 := low.nonnegative (true, false)
    have control_lower := (abs_le.mp hc).1
    have treated_upper := (abs_le.mp ht).2
    rw [aa]
    unfold controlSuccessMarginal at control_lower
    unfold treatmentSuccessMarginal at treated_upper
    unfold benefitResponseMass
    linarith
  · have aa : benefitAmbiguityValue eta0 eta1 = 1 := by
      apply min_eq_left
      linarith
    rw [aa]
    linarith [(benefit_unit high).2, (benefit_unit low).1]

/-- The bilinear maximum is controlled by three corners, not the product of
separate difference bounds. The proof uses exact slope signs in each slice. -/
private theorem bilinear_upper (a b x y u v : ℚ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hxu : 2 * x - 2 * a ≤ u) (hyv : 2 * y - 2 * b ≤ v) :
    x * y - u * v ≤ max (max a b) (1 - 4 * (1 - a) * (1 - b)) := by
  let M := max (max a b) (1 - 4 * (1 - a) * (1 - b))
  have am : a ≤ M := (le_max_left a b).trans (le_max_left _ _)
  have bm : b ≤ M := (le_max_right a b).trans (le_max_left _ _)
  have cm : 1 - 4 * (1 - a) * (1 - b) ≤ M := le_max_right _ _
  have uv : 0 ≤ u * v := mul_nonneg hu hv
  change x * y - u * v ≤ M
  by_cases xa : x ≤ a
  · have xy : x * y ≤ x := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hy1)]
    linarith
  by_cases yb : y ≤ b
  · have xy : x * y ≤ y := by nlinarith [mul_nonneg hy (sub_nonneg.mpr hx1)]
    linarith
  have ax : a ≤ x := (lt_of_not_ge xa).le
  have by_ : b ≤ y := (lt_of_not_ge yb).le
  have lo_u : 0 ≤ 2 * x - 2 * a := by linarith
  have lo_v : 0 ≤ 2 * y - 2 * b := by linarith
  have product_lower := mul_le_mul hxu hyv lo_v hu
  have upper : x * y - u * v ≤ x * y - 4 * (x - a) * (y - b) := by
    nlinarith [product_lower]
  apply upper.trans
  by_cases slope : 0 ≤ 4 * b - 3 * y
  · have step := mul_nonneg (sub_nonneg.mpr hx1) slope
    have edge : x * y - 4 * (x - a) * (y - b) ≤
        y - 4 * (1 - a) * (y - b) := by nlinarith [step]
    apply edge.trans
    by_cases rising : 0 ≤ 4 * a - 3
    · have step2 := mul_nonneg (sub_nonneg.mpr hy1) rising
      nlinarith [step2, cm]
    · have negative_slope : 0 ≤ 3 - 4 * a := by linarith
      have step2 := mul_nonneg (sub_nonneg.mpr by_) negative_slope
      nlinarith [step2, bm]
  · have negative_slope : 0 ≤ 3 * y - 4 * b := by linarith
    have step := mul_nonneg (sub_nonneg.mpr ax) negative_slope
    have edge : x * y - 4 * (x - a) * (y - b) ≤ a * y := by
      nlinarith [step]
    have ay : a * y ≤ a := by nlinarith [mul_nonneg ha (sub_nonneg.mpr hy1)]
    linarith

private def certainBenefitLaw : FiniteResponseLaw (Bool × Bool) :=
  mechanismBenefitLaw 1 (by norm_num) le_rfl

private theorem certain_benefit : benefitResponseMass certainBenefitLaw.mass = 1 := by
  exact mechanismBenefitLaw_benefit 1 (by norm_num) le_rfl

private theorem certain_control : controlSuccessMarginal certainBenefitLaw.mass = 0 := by
  simp [certainBenefitLaw, mechanismBenefitLaw]

private theorem certain_treated : treatmentSuccessMarginal certainBenefitLaw.mass = 1 := by
  simp [certainBenefitLaw, mechanismBenefitLaw]

/-- An actual law close to certain benefit can lose exactly twice the excess
of the single-mechanism ambiguity above one half. -/
private theorem exists_depleted_law (eta0 eta1 : ℚ) (h0 : 0 ≤ eta0) (h1 : 0 ≤ eta1) :
    ∃ low : FiniteResponseLaw (Bool × Bool),
      |controlSuccessMarginal certainBenefitLaw.mass - controlSuccessMarginal low.mass| ≤ eta0 ∧
      |treatmentSuccessMarginal certainBenefitLaw.mass - treatmentSuccessMarginal low.mass| ≤ eta1 ∧
      benefitResponseMass low.mass = 2 * (1 - benefitAmbiguityValue eta0 eta1) := by
  rw [certain_control, certain_treated]
  by_cases small : eta0 + eta1 ≤ 1
  · have lo : max 0 ((1 - eta1) - eta0) ≤ 1 - eta0 - eta1 := by
      apply max_le <;> linarith
    have hi : 1 - eta0 - eta1 ≤ min (1 - eta1) (1 - eta0) := by
      apply le_min <;> linarith
    refine ⟨benefitResponseLaw eta0 (1 - eta1) (1 - eta0 - eta1) lo hi, ?_⟩
    simp only [benefitResponseLaw_controlMarginal, benefitResponseLaw_treatmentMarginal,
      benefitResponseLaw_benefit]
    have aa : benefitAmbiguityValue eta0 eta1 = (1 + eta0 + eta1) / 2 := by
      apply min_eq_right
      linarith
    refine ⟨?_, ?_, ?_⟩
    · simpa only [zero_sub, abs_neg, abs_of_nonneg h0] using (le_rfl : eta0 ≤ eta0)
    · have : (1 : ℚ) - (1 - eta1) = eta1 := by ring
      simpa only [this, abs_of_nonneg h1] using (le_rfl : eta1 ≤ eta1)
    · rw [aa]
      ring
  · let s := min (1 : ℚ) eta0
    have sn : 0 ≤ s := le_min (by norm_num) h0
    have su : s ≤ 1 := min_le_left _ _
    have se : s ≤ eta0 := min_le_right _ _
    have rest : 1 - s ≤ eta1 := by
      by_cases h : eta0 ≤ 1
      · change 1 - min 1 eta0 ≤ eta1
        rw [min_eq_right h]
        linarith
      · change 1 - min 1 eta0 ≤ eta1
        rw [min_eq_left (le_of_lt (lt_of_not_ge h))]
        linarith
    have lo : max 0 (s - s) ≤ (0 : ℚ) := by simp
    have hi : (0 : ℚ) ≤ min s (1 - s) := le_min sn (sub_nonneg.mpr su)
    refine ⟨benefitResponseLaw s s 0 lo hi, ?_⟩
    simp only [benefitResponseLaw_controlMarginal, benefitResponseLaw_treatmentMarginal,
      benefitResponseLaw_benefit]
    have aa : benefitAmbiguityValue eta0 eta1 = 1 := by
      apply min_eq_left
      linarith
    refine ⟨?_, ?_, ?_⟩
    · simpa only [zero_sub, abs_neg, abs_of_nonneg sn] using se
    · simpa only [abs_of_nonneg (sub_nonneg.mpr su)] using rest
    · rw [aa]
      ring

private theorem tolerance_swap (high low : MarkovianJointMechanismModel)
    (eta10 eta11 eta20 eta21 : ℚ)
    (h : JointMarginalTolerance high low eta10 eta11 eta20 eta21) :
    JointMarginalTolerance low high eta10 eta11 eta20 eta21 := by
  simpa only [JointMarginalTolerance, abs_sub_comm] using h

private theorem oriented_upper (eta10 eta11 eta20 eta21 : ℚ)
    (h10 : 0 ≤ eta10) (h11 : 0 ≤ eta11) (h20 : 0 ≤ eta20) (h21 : 0 ≤ eta21)
    (high low : MarkovianJointMechanismModel)
    (close : JointMarginalTolerance high low eta10 eta11 eta20 eta21) :
    jointMechanismBenefitMass (markovianJointResponseMass high) -
      jointMechanismBenefitMass (markovianJointResponseMass low) ≤
        jointBenefitAmbiguityValue eta10 eta11 eta20 eta21 := by
  rcases close with ⟨c10, c11, c20, c21⟩
  rw [markovianJointBenefit_eq_product, markovianJointBenefit_eq_product]
  exact bilinear_upper _ _ _ _ _ _
    (ambiguity_unit eta10 eta11 h10 h11).1 (ambiguity_unit eta10 eta11 h10 h11).2
    (ambiguity_unit eta20 eta21 h20 h21).1 (ambiguity_unit eta20 eta21 h20 h21).2
    (benefit_unit high.firstLaw).1 (benefit_unit high.firstLaw).2
    (benefit_unit high.secondLaw).1 (benefit_unit high.secondLaw).2
    (benefit_unit low.firstLaw).1 (benefit_unit low.secondLaw).1
    (benefit_pair_constraint eta10 eta11 high.firstLaw low.firstLaw c10 c11)
    (benefit_pair_constraint eta20 eta21 high.secondLaw low.secondLaw c20 c21)

/-- Sharp global pairwise modulus on the existing product-mechanism model.
Every four-tolerance tuple has an explicit attaining pair of original models.
The assertion keeps all four marginal comparisons and the actual product query.
It is not a fixed-data identified interval or a theorem for coupled disturbances. -/
theorem joint_benefit_marginal_tolerance_sharp (eta10 eta11 eta20 eta21 : ℚ)
    (h10 : 0 ≤ eta10) (h11 : 0 ≤ eta11) (h20 : 0 ≤ eta20) (h21 : 0 ≤ eta21) :
    (∀ high low : MarkovianJointMechanismModel,
      JointMarginalTolerance high low eta10 eta11 eta20 eta21 →
      |jointMechanismBenefitMass (markovianJointResponseMass high) -
        jointMechanismBenefitMass (markovianJointResponseMass low)| ≤
          jointBenefitAmbiguityValue eta10 eta11 eta20 eta21) ∧
    (∃ high low : MarkovianJointMechanismModel,
      JointMarginalTolerance high low eta10 eta11 eta20 eta21 ∧
      jointMechanismBenefitMass (markovianJointResponseMass high) -
        jointMechanismBenefitMass (markovianJointResponseMass low) =
          jointBenefitAmbiguityValue eta10 eta11 eta20 eta21) := by
  let a := benefitAmbiguityValue eta10 eta11
  let b := benefitAmbiguityValue eta20 eta21
  let c := 1 - 4 * (1 - a) * (1 - b)
  have first : ∃ high low : MarkovianJointMechanismModel,
      JointMarginalTolerance high low eta10 eta11 eta20 eta21 ∧
      jointMechanismBenefitMass (markovianJointResponseMass high) -
        jointMechanismBenefitMass (markovianJointResponseMass low) = a := by
    obtain ⟨high, low, hc, ht, gap⟩ :=
      (benefit_marginal_tolerance_sharp eta10 eta11 h10 h11).2.1
    refine ⟨⟨high, certainBenefitLaw⟩, ⟨low, certainBenefitLaw⟩, ?_, ?_⟩
    · exact ⟨hc, ht, by simpa using h20, by simpa using h21⟩
    · simpa only [markovianJointBenefit_eq_product, certain_benefit, mul_one] using gap
  have second : ∃ high low : MarkovianJointMechanismModel,
      JointMarginalTolerance high low eta10 eta11 eta20 eta21 ∧
      jointMechanismBenefitMass (markovianJointResponseMass high) -
        jointMechanismBenefitMass (markovianJointResponseMass low) = b := by
    obtain ⟨high, low, hc, ht, gap⟩ :=
      (benefit_marginal_tolerance_sharp eta20 eta21 h20 h21).2.1
    refine ⟨⟨certainBenefitLaw, high⟩, ⟨certainBenefitLaw, low⟩, ?_, ?_⟩
    · exact ⟨by simpa using h10, by simpa using h11, hc, ht⟩
    · simpa only [markovianJointBenefit_eq_product, certain_benefit, one_mul] using gap
  have both : ∃ high low : MarkovianJointMechanismModel,
      JointMarginalTolerance high low eta10 eta11 eta20 eta21 ∧
      jointMechanismBenefitMass (markovianJointResponseMass high) -
        jointMechanismBenefitMass (markovianJointResponseMass low) = c := by
    obtain ⟨low1, c10, c11, v1⟩ := exists_depleted_law eta10 eta11 h10 h11
    obtain ⟨low2, c20, c21, v2⟩ := exists_depleted_law eta20 eta21 h20 h21
    refine ⟨⟨certainBenefitLaw, certainBenefitLaw⟩, ⟨low1, low2⟩,
      ⟨c10, c11, c20, c21⟩, ?_⟩
    simp only [markovianJointBenefit_eq_product, certain_benefit, v1, v2]
    dsimp [c, a, b]
    ring
  constructor
  · intro high low close
    have upper := oriented_upper eta10 eta11 eta20 eta21 h10 h11 h20 h21 high low close
    have reverse := oriented_upper eta10 eta11 eta20 eta21 h10 h11 h20 h21 low high
      (tolerance_swap high low eta10 eta11 eta20 eta21 close)
    exact abs_le.mpr ⟨by linarith, upper⟩
  · change ∃ high low, JointMarginalTolerance high low eta10 eta11 eta20 eta21 ∧
      jointMechanismBenefitMass (markovianJointResponseMass high) -
        jointMechanismBenefitMass (markovianJointResponseMass low) = max (max a b) c
    by_cases hc : c ≤ max a b
    · rw [max_eq_left hc]
      by_cases hab : b ≤ a
      · rw [max_eq_left hab]
        exact first
      · rw [max_eq_right (le_of_lt (lt_of_not_ge hab))]
        exact second
    · rw [max_eq_right (le_of_lt (lt_of_not_ge hc))]
      exact both

/-- With equal total marginal tolerance s in both mechanisms, the maximizing
configuration changes at s=1/2. This is a deterministic ambiguity formula,
not a physical phase transition or a sample-size claim. -/
theorem equal_total_tolerance_regimes (eta10 eta11 eta20 eta21 s : ℚ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (first : eta10 + eta11 = s) (second : eta20 + eta21 = s) :
    jointBenefitAmbiguityValue eta10 eta11 eta20 eta21 =
      if s ≤ 1 / 2 then (1 + s) / 2 else 2 * s - s ^ 2 := by
  have ac : (1 + s) / 2 ≤ 1 := by linarith
  have aa : benefitAmbiguityValue eta10 eta11 = (1 + s) / 2 := by
    unfold benefitAmbiguityValue
    rw [show 1 + eta10 + eta11 = 1 + s by linarith, min_eq_right ac]
  have bb : benefitAmbiguityValue eta20 eta21 = (1 + s) / 2 := by
    unfold benefitAmbiguityValue
    rw [show 1 + eta20 + eta21 = 1 + s by linarith, min_eq_right ac]
  have curve : 1 - 4 * (1 - (1 + s) / 2) * (1 - (1 + s) / 2) = 2 * s - s ^ 2 := by ring
  simp only [jointBenefitAmbiguityValue, aa, bb, max_self, curve]
  by_cases small : s ≤ 1 / 2
  · have order : 2 * s - s ^ 2 ≤ (1 + s) / 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - s by linarith) (show 0 ≤ 1 / 2 - s by linarith)]
    rw [if_pos small, max_eq_left order]
  · have order : (1 + s) / 2 ≤ 2 * s - s ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - s by linarith) (show 0 ≤ s - 1 / 2 by linarith)]
    rw [if_neg small, max_eq_right order]

#print axioms joint_benefit_marginal_tolerance_sharp
#print axioms equal_total_tolerance_regimes

end D5.S3.ConceptDynamics.PartialIdentification.JointBenefitToleranceSharp
