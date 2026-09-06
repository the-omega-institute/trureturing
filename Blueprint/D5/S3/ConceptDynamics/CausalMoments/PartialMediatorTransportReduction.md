# Exact partial-mediator transport reduction

## Abstract

For binary treatment and outcome with a finite mediator and independent mechanism disturbances, one transportation matrix and two linear inequalities characterize every attainable rational benefit target.

Mediator is any finite type with decidable equality. control and treated are FiniteResponseLaw values on Mediator; coupling is such a law on Mediator times Mediator; outcome is such a law on complete tables Bool times Mediator to Bool. probability is a rational success kernel. Expectations below use the existing linearObjective. The direct treatment-to-outcome edge is allowed; there is no exclusion restriction equating the two treatment rows.

**Definition 1.1 (One mediator transport matrix).**

$$\forall coupling, control, treated, (\operatorname{HasMediatorMarginals}(coupling, control, treated)) \Leftrightarrow ((\forall m, (\operatorname{leftResponseMarginal}(\operatorname{mass}(coupling), m)) = (\operatorname{mass}(control, m))) \land (\forall m, (\operatorname{rightResponseMarginal}(\operatorname{mass}(coupling), m)) = (\operatorname{mass}(treated, m))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.HasMediatorMarginals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonnegative normalization is supplied by FiniteResponseLaw. All row and column equations constrain the same matrix, rather than separate cellwise maximizers.

**Definition 1.2 (Prescribed outcome mechanism kernel).**

$$\forall outcome, probability, (\operatorname{HasOutcomeKernel}(outcome, probability)) \Leftrightarrow (\forall a, m, (\operatorname{outcomeSuccess}(outcome, a, m)) = (\operatorname{probability}((a, m))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.HasOutcomeKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel consists of intervention success probabilities. Observational identification and zero-probability parent cells require separate assumptions.

**Definition 1.3 (Actual common-source counterfactual law).**

$$\forall coupling, outcome, (\operatorname{partialMediatorResponseLaw}(coupling, outcome)) = (\operatorname{pushforwardResponseLaw}(\operatorname{productResponseLaw}(coupling, outcome), responseMap))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorResponseLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

responseMap((m0,m1),table) is (table(false,m0),table(true,m1)). Both worlds read the same mediator pair and the same outcome table. The product law makes only the two mechanisms independent.

**Definition 1.4 (Benefit under the independent source law).**

$$\forall coupling, outcome, (\operatorname{partialMediatorBenefit}(coupling, outcome)) = (\operatorname{linearObjective}(benefitEvent, \operatorname{mass}(\operatorname{productResponseLaw}(coupling, outcome))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorBenefit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

benefitEvent is the indicator that responseMap is (false,true). It is evaluated on the complete product source, not declared to equal a transport objective.

**Theorem 1.5 (Bind to the existing causal benefit readout).**

$$\forall coupling, outcome, (\operatorname{partialMediatorBenefit}(coupling, outcome)) = (\operatorname{benefitResponseMass}(\operatorname{mass}(\operatorname{partialMediatorResponseLaw}(coupling, outcome))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorBenefit_actual_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the existing deterministic-pushforward expectation identity and the actual 01 response cell.

**Theorem 1.6 (Derive the bilinear mechanism decomposition).**

$$\forall coupling, outcome, (\operatorname{partialMediatorBenefit}(coupling, outcome)) = (\sum_{pair} ((\operatorname{outcomeBenefitCell}(outcome, \operatorname{fst}(pair), \operatorname{snd}(pair))) \cdot (\operatorname{mass}(coupling, pair))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorBenefit_eq_cells` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite independent-product sum is expanded without discarding the common mediator coupling.

**Definition 1.7 (Lower transport cost).**

$$\forall probability, pair, (\operatorname{lowerTransportCost}(probability, pair)) = (\operatorname{max}(0, (\operatorname{probability}((true, \operatorname{snd}(pair)))) - (\operatorname{probability}((false, \operatorname{fst}(pair))))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.lowerTransportCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the lower Boolean response-cell bound at the two mediator values.

**Definition 1.8 (Upper transport cost).**

$$\forall probability, pair, (\operatorname{upperTransportCost}(probability, pair)) = (\operatorname{min}((1) - (\operatorname{probability}((false, \operatorname{fst}(pair)))), \operatorname{probability}((true, \operatorname{snd}(pair)))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.upperTransportCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost is multiplied by one globally feasible transport matrix. There is no substitution of an independently maximized mediator cell.

**Theorem 1.9 (Necessary bounds at the actual mediator law).**

$$\forall probability, coupling, outcome, (\operatorname{HasOutcomeKernel}(outcome, probability)) \Rightarrow (((\operatorname{linearObjective}(\operatorname{lowerTransportCost}(probability), \operatorname{mass}(coupling))) \le (\operatorname{partialMediatorBenefit}(coupling, outcome))) \land ((\operatorname{partialMediatorBenefit}(coupling, outcome)) \le (\operatorname{linearObjective}(\operatorname{upperTransportCost}(probability), \operatorname{mass}(coupling)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorBenefit_transport_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weights are nonnegative and every outcome-law cell obeys the already proved bound.

**Theorem 1.10 (Common mechanisms attain both costs).**

$$\forall probability, (\forall index, ((0) \le (\operatorname{probability}(index))) \land ((\operatorname{probability}(index)) \le (1))) \Rightarrow (\exists lower, upper, (\operatorname{HasOutcomeKernel}(lower, probability)) \land ((\operatorname{HasOutcomeKernel}(upper, probability)) \land (\forall coupling, ((\operatorname{partialMediatorBenefit}(coupling, lower)) = (\operatorname{linearObjective}(\operatorname{lowerTransportCost}(probability), \operatorname{mass}(coupling)))) \land ((\operatorname{partialMediatorBenefit}(coupling, upper)) = (\operatorname{linearObjective}(\operatorname{upperTransportCost}(probability), \operatorname{mass}(coupling)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.simultaneous_transport_endpoint_mechanisms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two outcome laws are selected before all mediator couplings. This discharges simultaneous attainability rather than assuming that individual cell bounds can be combined.

**Theorem 1.11 (Full rational interval at one mediator coupling).**

$$\forall probability, coupling, target, (\forall index, ((0) \le (\operatorname{probability}(index))) \land ((\operatorname{probability}(index)) \le (1))) \Rightarrow ((\exists outcome, (\operatorname{HasOutcomeKernel}(outcome, probability)) \land ((\operatorname{partialMediatorBenefit}(coupling, outcome)) = (target))) \Leftrightarrow (((\operatorname{linearObjective}(\operatorname{lowerTransportCost}(probability), \operatorname{mass}(coupling))) \le (target)) \land ((target) \le (\operatorname{linearObjective}(\operatorname{upperTransportCost}(probability), \operatorname{mass}(coupling))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.fixed_coupling_benefit_sharp_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Interior targets mix only the two complete outcome laws, with the mediator law fixed. Rational interpolation covers endpoints and the zero-width case while retaining mechanism independence.

**Theorem 1.12 (Exact transportation-LP characterization).**

$$\forall control, treated, probability, target, (\forall index, ((0) \le (\operatorname{probability}(index))) \land ((\operatorname{probability}(index)) \le (1))) \Rightarrow ((\exists coupling, outcome, (\operatorname{HasMediatorMarginals}(coupling, control, treated)) \land ((\operatorname{HasOutcomeKernel}(outcome, probability)) \land ((\operatorname{partialMediatorBenefit}(coupling, outcome)) = (target)))) \Leftrightarrow (\exists coupling, (\operatorname{HasMediatorMarginals}(coupling, control, treated)) \land (((\operatorname{linearObjective}(\operatorname{lowerTransportCost}(probability), \operatorname{mass}(coupling))) \le (target)) \land ((target) \le (\operatorname{linearObjective}(\operatorname{upperTransportCost}(probability), \operatorname{mass}(coupling)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partial_mediator_target_iff_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right side has m-squared coupling variables and linear row, column and target conditions. No outcome-law optimization, independent pairwise witnesses, or optimizer-existence premise remains.

**Theorem 1.13 (Transport optima give causal endpoint witnesses).**

$$\forall control, treated, probability, lower, upper, lowerCoupling, upperCoupling, ((\forall index, ((0) \le (\operatorname{probability}(index))) \land ((\operatorname{probability}(index)) \le (1))) \land ((\operatorname{HasMediatorMarginals}(lowerCoupling, control, treated)) \land ((\operatorname{HasMediatorMarginals}(upperCoupling, control, treated)) \land (((\operatorname{linearObjective}(\operatorname{lowerTransportCost}(probability), \operatorname{mass}(lowerCoupling))) = (lower)) \land (((\operatorname{linearObjective}(\operatorname{upperTransportCost}(probability), \operatorname{mass}(upperCoupling))) = (upper)) \land (\forall coupling, (\operatorname{HasMediatorMarginals}(coupling, control, treated)) \Rightarrow (((lower) \le (\operatorname{linearObjective}(\operatorname{lowerTransportCost}(probability), \operatorname{mass}(coupling)))) \land ((\operatorname{linearObjective}(\operatorname{upperTransportCost}(probability), \operatorname{mass}(coupling))) \le (upper))))))))) \Rightarrow ((\forall coupling, outcome, ((\operatorname{HasMediatorMarginals}(coupling, control, treated)) \land (\operatorname{HasOutcomeKernel}(outcome, probability))) \Rightarrow (((lower) \le (\operatorname{partialMediatorBenefit}(coupling, outcome))) \land ((\operatorname{partialMediatorBenefit}(coupling, outcome)) \le (upper)))) \land ((\exists outcome, (\operatorname{HasOutcomeKernel}(outcome, probability)) \land ((\operatorname{partialMediatorBenefit}(lowerCoupling, outcome)) = (lower))) \land (\exists outcome, (\operatorname{HasOutcomeKernel}(outcome, probability)) \land ((\operatorname{partialMediatorBenefit}(upperCoupling, outcome)) = (upper)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.transport_endpoints_are_causal_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lowerCoupling and upperCoupling are actual probability laws with the displayed marginals. The premise includes their transport objective values and universal transport bounds. The conclusion gives universal causal bounds and actual outcome mechanisms attaining both endpoints with those same couplings.

**Theorem 1.14 (One-dimensional absolute-distance cost identities).**

$$\forall probability, coupling, (((2) \cdot (\operatorname{linearObjective}(\operatorname{lowerTransportCost}(probability), \operatorname{mass}(coupling)))) = (((mean1) - (mean0)) + (distance01))) \land (((2) \cdot (\operatorname{linearObjective}(\operatorname{upperTransportCost}(probability), \operatorname{mass}(coupling)))) = ((((1) - (mean0)) + (mean1)) - (distanceComplement)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.transport_cost_absolute_distance_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

mean0 and mean1 abbreviate coupling expectations of probability(false,pair.first) and probability(true,pair.second). distance01 is the expectation of their absolute difference. distanceComplement is the expectation of the absolute value of one minus their sum. These are aliases for the full displayed finite sums in Lean. The theorem itself does not certify a sorting algorithm or invoke a Wasserstein implementation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.HasMediatorMarginals`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.HasOutcomeKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.fixed_coupling_benefit_sharp_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.lowerTransportCost`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorBenefit`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorBenefit_actual_response`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorBenefit_eq_cells`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorBenefit_transport_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partialMediatorResponseLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.partial_mediator_target_iff_transport`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.simultaneous_transport_endpoint_mechanisms`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.transport_cost_absolute_distance_identities`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.transport_endpoints_are_causal_sharp`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/PartialMediatorTransportReduction.upperTransportCost`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification](ProductLawMomentSparsification.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling](SharedThresholdResponseCoupling.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary](../PartialIdentification/MarkovianBenefitIdentificationBoundary.md)
