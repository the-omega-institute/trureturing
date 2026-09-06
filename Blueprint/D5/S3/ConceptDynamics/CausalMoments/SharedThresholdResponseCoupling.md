# Simultaneous response-cell attainment

## Abstract

One complete outcome mechanism attains every pairwise upper cell at once; another attains every lower cell. This is the constructive prerequisite for an exact mediator transport reduction.

Mediator is any finite type with decidable equality. Complete outcome tables have type Bool times Mediator to Bool. Both interventions evaluate the same table. The notation thresholdOutcomeLaw includes its positive-denominator proof argument hN. All probabilities and expectations are rational.

**Definition 1.1 (One finite disturbance).**

$$\forall N, hN, u, (\operatorname{mass}(\operatorname{uniformThresholdLaw}(N, hN), u)) = (\frac{1}{N})$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.uniformThresholdLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N is a natural number, hN proves N is positive, and u ranges over Fin N. The defining structure proves nonnegativity and normalization.

**Theorem 1.2 (Exact prefix probability).**

$$\forall N, K, hN, hK, (\operatorname{linearObjective}(\operatorname{prefixIndicator}(K), \operatorname{mass}(\operatorname{uniformThresholdLaw}(N, hN)))) = (\frac{K}{N})$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.uniformThreshold_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

hN proves 0<N and hK proves K<=N. prefixIndicator(K)(u) is one exactly when the natural value of u is smaller than K. The proof counts this entire prefix, not a sample.

**Definition 1.3 (Actual success expectation).**

$$\forall law, a, m, (\operatorname{outcomeSuccess}(law, a, m)) = (\operatorname{linearObjective}(\operatorname{successIndicator}(a, m), \operatorname{mass}(law)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.outcomeSuccess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

successIndicator(a,m)(table) is one exactly when table(a,m) is true. law is a normalized FiniteResponseLaw on complete outcome tables.

**Definition 1.4 (A cross-world benefit cell).**

$$\forall law, m0, m1, (\operatorname{outcomeBenefitCell}(law, m0, m1)) = (\operatorname{linearObjective}(\operatorname{benefitIndicator}(m0, m1), \operatorname{mass}(law)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.outcomeBenefitCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

benefitIndicator(m0,m1)(table) is one exactly when table(false,m0) is false and table(true,m1) is true. This uses two entries of one table law.

**Definition 1.5 (Two explicit shared-threshold mechanisms).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Push uniformThresholdLaw through the complete table readout. The lower witness reads u<count(a,m) in both worlds. The upper witness reads the complement of u<N-count(false,m) in the control world and u<count(true,m) in the treated world. The flag chooses a witness, not an assumption on every admissible outcome mechanism.

**Theorem 1.6 (Both mechanisms match all success rows).**

$$\forall N, hN, count, upper, a, m, (((0) < (N)) \land (\forall index, (\operatorname{count}(index)) \le (N))) \Rightarrow ((\operatorname{outcomeSuccess}(\operatorname{thresholdOutcomeLaw}(N, hN, count, upper), a, m)) = (\frac{\operatorname{count}((a, m))}{N}))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement holds for every mediator value and either witness flag, including probability zero and one.

**Theorem 1.7 (All upper cells from one law).**

$$\forall N, hN, count, m0, m1, (((0) < (N)) \land (\forall index, (\operatorname{count}(index)) \le (N))) \Rightarrow ((\operatorname{outcomeBenefitCell}(\operatorname{thresholdOutcomeLaw}(N, hN, count, true), m0, m1)) = (\operatorname{min}((1) - (\frac{\operatorname{count}((false, m0))}{N}), \frac{\operatorname{count}((true, m1))}{N})))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw_upper_cells` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two favourable threshold events are nested prefixes of the same disturbance. Their intersection has the smaller mass, simultaneously for every m0,m1.

**Theorem 1.8 (All lower cells from one law).**

$$\forall N, hN, count, m0, m1, (((0) < (N)) \land (\forall index, (\operatorname{count}(index)) \le (N))) \Rightarrow ((\operatorname{outcomeBenefitCell}(\operatorname{thresholdOutcomeLaw}(N, hN, count, false), m0, m1)) = (\operatorname{max}(0, (\frac{\operatorname{count}((true, m1))}{N}) - (\frac{\operatorname{count}((false, m0))}{N}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw_lower_cells` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the common-prefix intersection computes every lower cell. No independent disturbance is introduced per mediator pair.

**Theorem 1.9 (Bounds for every complete outcome mechanism).**

$$\forall law, m0, m1, ((\operatorname{max}(0, (\operatorname{outcomeSuccess}(law, true, m1)) - (\operatorname{outcomeSuccess}(law, false, m0)))) \le (\operatorname{outcomeBenefitCell}(law, m0, m1))) \land ((\operatorname{outcomeBenefitCell}(law, m0, m1)) \le (\operatorname{min}((1) - (\operatorname{outcomeSuccess}(law, false, m0)), \operatorname{outcomeSuccess}(law, true, m1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.outcomeBenefitCell_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only nonnegative normalization and the actual Boolean response entries are used for necessity.

**Theorem 1.10 (All finite rational kernels have simultaneous endpoint mechanisms).**

$$\forall probability, (\forall index, ((0) \le (\operatorname{probability}(index))) \land ((\operatorname{probability}(index)) \le (1))) \Rightarrow (\exists lower, upper, (\forall a, m, (\operatorname{outcomeSuccess}(lower, a, m)) = (\operatorname{probability}((a, m)))) \land (\forall a, m, (\operatorname{outcomeSuccess}(upper, a, m)) = (\operatorname{probability}((a, m)))) \land (\forall m0, m1, (\operatorname{outcomeBenefitCell}(lower, m0, m1)) = (\operatorname{max}(0, (\operatorname{probability}((true, m1))) - (\operatorname{probability}((false, m0)))))) \land (\forall m0, m1, (\operatorname{outcomeBenefitCell}(upper, m0, m1)) = (\operatorname{min}((1) - (\operatorname{probability}((false, m0))), \operatorname{probability}((true, m1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.simultaneous_frechet_outcome_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof first derives a common positive denominator for the entire finite rational kernel. It then constructs the two actual finite laws. The existential laws precede the universal mediator-pair quantifiers.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.outcomeBenefitCell`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.outcomeBenefitCell_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.outcomeSuccess`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.simultaneous_frechet_outcome_laws`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw_lower_cells`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw_success`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.thresholdOutcomeLaw_upper_cells`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.uniformThresholdLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling.uniformThreshold_prefix`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSparseLaw](FiniteMomentSparseLaw.md)
