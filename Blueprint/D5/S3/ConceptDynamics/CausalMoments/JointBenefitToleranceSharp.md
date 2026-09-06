# Sharp two-mechanism joint-benefit robustness

## Abstract

The four intervention-marginal tolerances define a genuine bilinear comparison between two product-mechanism models. A three-corner envelope and original-carrier attaining models give its exact value.

All scalar variables are rational. The variables high and low are the existing MarkovianJointMechanismModel values: each contains two independent complete response laws on Bool times Bool. Potential outcomes within an individual law may remain dependent. The comparison is across all marginal locations, not about one fixed observed center.

**Definition 1.1 (Four actual marginal comparisons).**

$$\forall high, low, eta10, eta11, eta20, eta21, (\operatorname{JointMarginalTolerance}(high, low, eta10, eta11, eta20, eta21)) \Leftrightarrow (((\lvert(\operatorname{controlSuccessMarginal}(\operatorname{mass}(\operatorname{firstLaw}(high)))) - (\operatorname{controlSuccessMarginal}(\operatorname{mass}(\operatorname{firstLaw}(low))))\rvert) \le (eta10)) \land (((\lvert(\operatorname{treatmentSuccessMarginal}(\operatorname{mass}(\operatorname{firstLaw}(high)))) - (\operatorname{treatmentSuccessMarginal}(\operatorname{mass}(\operatorname{firstLaw}(low))))\rvert) \le (eta11)) \land (((\lvert(\operatorname{controlSuccessMarginal}(\operatorname{mass}(\operatorname{secondLaw}(high)))) - (\operatorname{controlSuccessMarginal}(\operatorname{mass}(\operatorname{secondLaw}(low))))\rvert) \le (eta20)) \land ((\lvert(\operatorname{treatmentSuccessMarginal}(\operatorname{mass}(\operatorname{secondLaw}(high)))) - (\operatorname{treatmentSuccessMarginal}(\operatorname{mass}(\operatorname{secondLaw}(low))))\rvert) \le (eta21)))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/JointBenefitToleranceSharp.JointMarginalTolerance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These four inequalities concern the original response-law readouts. The product restriction is in the original model semantics, not imposed by a new joint-coupling relaxation.

**Definition 1.2 (Three competing configurations).**

$$\forall eta10, eta11, eta20, eta21, (\operatorname{jointBenefitAmbiguityValue}(eta10, eta11, eta20, eta21)) = (\operatorname{max}(\operatorname{max}(\operatorname{benefitAmbiguityValue}(eta10, eta11), \operatorname{benefitAmbiguityValue}(eta20, eta21)), (1) - (((4) \cdot ((1) - (\operatorname{benefitAmbiguityValue}(eta10, eta11)))) \cdot ((1) - (\operatorname{benefitAmbiguityValue}(eta20, eta21))))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/JointBenefitToleranceSharp.jointBenefitAmbiguityValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first two candidates place ambiguity in one mechanism and hold the other at certain benefit. The third places both upper mechanisms at certain benefit and simultaneously reduces both lower benefits.

**Theorem 1.3 (Global bound and attaining product models).**

$$\forall eta10, eta11, eta20, eta21, (((0) \le (eta10)) \land (((0) \le (eta11)) \land (((0) \le (eta20)) \land ((0) \le (eta21))))) \Rightarrow ((\forall high, low, (\operatorname{JointMarginalTolerance}(high, low, eta10, eta11, eta20, eta21)) \Rightarrow ((\lvert(\operatorname{jointMechanismBenefitMass}(\operatorname{markovianJointResponseMass}(high))) - (\operatorname{jointMechanismBenefitMass}(\operatorname{markovianJointResponseMass}(low)))\rvert) \le (\operatorname{jointBenefitAmbiguityValue}(eta10, eta11, eta20, eta21)))) \land (\exists high, low, (\operatorname{JointMarginalTolerance}(high, low, eta10, eta11, eta20, eta21)) \land (((\operatorname{jointMechanismBenefitMass}(\operatorname{markovianJointResponseMass}(high))) - (\operatorname{jointMechanismBenefitMass}(\operatorname{markovianJointResponseMass}(low)))) = (\operatorname{jointBenefitAmbiguityValue}(eta10, eta11, eta20, eta21)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/JointBenefitToleranceSharp.joint_benefit_marginal_tolerance_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof first derives the endpoint-sensitive inequality 2 times the upper benefit minus 2 times the single-mechanism ambiguity is at most the lower benefit. A slice-slope argument bounds the bilinear product difference at three corners.

The first two corners reuse the existing one-mechanism sharpness theorem. The last corner uses explicitly normalized four-cell response laws. All four marginal tolerances and the actual joint-benefit query survive in the attaining pair.

This is an exact subfamily within the broader multi-component optimization research direction. It is not a complete column-generation method, a theorem for shared disturbances, or a claim of literature-wide novelty.

**Theorem 1.4 (Equal-tolerance maximizing regime).**

$$\forall eta10, eta11, eta20, eta21, s, (((0) \le (s)) \land (((s) \le (1)) \land ((((eta10) + (eta11)) = (s)) \land (((eta20) + (eta21)) = (s))))) \Rightarrow ((\operatorname{jointBenefitAmbiguityValue}(eta10, eta11, eta20, eta21)) = (\operatorname{ite}((s) \le (\frac{1}{2}), \frac{(1) + (s)}{2}, ((2) \cdot (s)) - (s^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/JointBenefitToleranceSharp.equal_total_tolerance_regimes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On 0 to 1, equal sums of the two within-mechanism tolerances yield (1+s)/2 through s=1/2, and 2s-s squared afterward. The algebraic formula needs the stated sum and s conditions; nonnegativity of each separate tolerance is supplied by the sharpness theorem when it is interpreted as a model guarantee.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/JointBenefitToleranceSharp.JointMarginalTolerance`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/JointBenefitToleranceSharp.equal_total_tolerance_regimes`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/JointBenefitToleranceSharp.jointBenefitAmbiguityValue`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/JointBenefitToleranceSharp.joint_benefit_marginal_tolerance_sharp`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp](BenefitMarginalToleranceSharp.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds](MarkovianJointMechanismBenefitSharpBounds.md)
