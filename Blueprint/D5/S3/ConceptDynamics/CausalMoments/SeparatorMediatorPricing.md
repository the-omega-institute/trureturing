# SeparatorMediatorPricing

## Abstract

All separator branches are certified and reassembled into the original complete-mediator optimization.

M is finite with decidable equality. coupling is a normalized rational mediator-pair law; K is a Finset M. Branch variables range over the whole function type K to Bool. multiplier and probability map M to Q; threshold is rational. law and candidate are original FiniteResponseLaw values on M to Bool. Structure-field applications refer to the displayed raw certificate fields.

**Definition 1.1 (A total family of branch certificates).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.SeparatorPricingCertificate`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.SeparatorPricingCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The raw fields are color : M to Bool; flows : (K to Bool) to STCutCertificate M; winner : K to Bool. The total function covers all 2^card(K) assignments. There is no proof-valued field and no producer-selected branch sublist.

**Definition 1.2 (Price one branch in original units).**

$$\forall M, coupling, K, multiplier, certificate, branch, (\operatorname{branchValue}(coupling, K, multiplier, certificate, branch)) = ((\operatorname{branchOffset}(coupling, K, branch, multiplier)) + (\operatorname{certifiedPricingValue}(\operatorname{residualCoupling}(coupling, K), \operatorname{color}(certificate), \operatorname{branchMultiplier}(coupling, K, branch, multiplier), \operatorname{flows}(certificate, branch))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.branchValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value includes the original fixed-coordinate offset and the checked residual price.

**Definition 1.3 (Check all branches and the proposed winner).**

$$\forall M, coupling, K, multiplier, certificate, (\operatorname{checkSeparatorPricing}(coupling, K, multiplier, certificate)) = (\operatorname{decide}((\forall branch, (\operatorname{checkBipartitePricing}(\operatorname{residualCoupling}(coupling, K), \operatorname{color}(certificate), \operatorname{branchMultiplier}(coupling, K, branch, multiplier), \operatorname{flows}(certificate, branch))) = (true)) \land (\forall branch, (\operatorname{branchValue}(coupling, K, multiplier, certificate, branch)) \le (\operatorname{branchValue}(coupling, K, multiplier, certificate, \operatorname{winner}(certificate))))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checkSeparatorPricing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both universal tests range over every function from K to Bool, including the unique assignment for empty K. Every branch uses the actual residual coupling and corrected multipliers.

**Definition 1.4 (Lift the winning cut to a causal response).**

$$\forall M, K, certificate, (\operatorname{winningTable}(K, certificate)) = (\operatorname{clampTable}(K, \operatorname{winner}(certificate), \operatorname{flipTable}(\operatorname{color}(certificate), \operatorname{side}(\operatorname{flows}(certificate, \operatorname{winner}(certificate))))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.winningTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected coordinates are restored after undoing the residual graph coloring. The result lies in the original full response-table carrier.

**Theorem 1.5 (An attained global maximum over all original columns).**

$$\forall M, coupling, K, multiplier, certificate, ((\operatorname{checkSeparatorPricing}(coupling, K, multiplier, certificate)) = (true)) \Rightarrow (((\operatorname{completeMediatorPricingScore}(coupling, multiplier, \operatorname{winningTable}(K, certificate))) = (\operatorname{branchValue}(coupling, K, multiplier, certificate, \operatorname{winner}(certificate)))) \land (\operatorname{IsGreatest}(\operatorname{range}(\operatorname{completeMediatorPricingScore}(coupling, multiplier)), \operatorname{branchValue}(coupling, K, multiplier, certificate, \operatorname{winner}(certificate)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checkSeparatorPricing_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each competitor is assigned to its own restriction on K. Its certified branch maximum is bounded by the proposed winner, so no unvisited original column can exceed the returned value.

**Theorem 1.6 (Exact full-family stopping test).**

$$\forall M, coupling, K, multiplier, certificate, threshold, ((\operatorname{checkSeparatorPricing}(coupling, K, multiplier, certificate)) = (true)) \Rightarrow ((\forall table, (\operatorname{completeMediatorPricingScore}(coupling, multiplier, table)) \le (threshold)) \Leftrightarrow ((\operatorname{branchValue}(coupling, K, multiplier, certificate, \operatorname{winner}(certificate))) \le (threshold)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checked_separator_stopping_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalization multiplier is compared to the certified maximum over all complete response columns, not only generated columns.

**Theorem 1.7 (Bound every law with the original marginal rows).**

$$\forall M, coupling, K, multiplier, probability, certificate, law, (((\operatorname{checkSeparatorPricing}(coupling, K, multiplier, certificate)) = (true)) \land (\forall i, (\operatorname{linearObjective}(\lambda table, \operatorname{ite}(\operatorname{table}(i), 1, 0), \operatorname{mass}(law))) = (\operatorname{probability}(i)))) \Rightarrow ((\operatorname{completeMediatorBenefit}(coupling, law)) \le ((\operatorname{branchValue}(coupling, K, multiplier, certificate, \operatorname{winner}(certificate))) + (\sum_{i} ((\operatorname{multiplier}(i)) \cdot (\operatorname{probability}(i))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checked_separator_causal_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing expectation/dual bound is reused on the original coupling. This bound is valid before restricted-master optimality and does not require fair outcome marginals.

**Theorem 1.8 (Certify the original sharp upper endpoint).**

$$\forall M, coupling, K, multiplier, probability, certificate, threshold, candidate, (((\operatorname{checkSeparatorPricing}(coupling, K, multiplier, certificate)) = (true)) \land ((\operatorname{branchValue}(coupling, K, multiplier, certificate, \operatorname{winner}(certificate))) \le (threshold)) \land (\forall i, (\operatorname{linearObjective}(\lambda table, \operatorname{ite}(\operatorname{table}(i), 1, 0), \operatorname{mass}(candidate))) = (\operatorname{probability}(i))) \land ((\operatorname{completeMediatorBenefit}(coupling, candidate)) = ((threshold) + (\sum_{i} ((\operatorname{multiplier}(i)) \cdot (\operatorname{probability}(i))))))) \Rightarrow (\operatorname{IsGreatest}(\operatorname{setOf}(\lambda value, \exists law, (\forall i, (\operatorname{linearObjective}(\lambda table, \operatorname{ite}(\operatorname{table}(i), 1, 0), \operatorname{mass}(law))) = (\operatorname{probability}(i))) \land ((\operatorname{completeMediatorBenefit}(coupling, law)) = (value))), \operatorname{completeMediatorBenefit}(coupling, candidate)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checked_separator_master_isGreatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual normalized nonnegative candidate law, all original marginal rows, exact primal/dual equality and the checked global stop certify the full endpoint. The original mediator coupling stays fixed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.SeparatorPricingCertificate`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.branchValue`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checkSeparatorPricing`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checkSeparatorPricing_sound`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checked_separator_causal_bound`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checked_separator_master_isGreatest`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.checked_separator_stopping_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.winningTable`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction](MediatorPricingRestriction.md)
