# BipartiteMediatorPricing

## Abstract

Actual complete-mediator pricing is reduced to a checked minimum cut, and the same certificate closes the full outcome-marginal master problem.

Mediator is an arbitrary finite type with decidable equality. coupling is the existing normalized rational law on Mediator times Mediator. color and table map Mediator to Bool; multiplier and probability map Mediator to Q; law and candidate are existing FiniteResponseLaw values on complete Boolean tables. certificate is the existing STCutCertificate. All formula quantifiers carry these types; finite sums cover every indicated carrier. The selected graph condition concerns the off-diagonal support of coupling.

**Definition 1.1 (Color the actual off-diagonal support).**

$$\forall Mediator, coupling, color, (\operatorname{OffDiagonalBipartite}(coupling, color)) \Leftrightarrow (\forall i, j, (((i) \neq (j)) \land ((\operatorname{mass}(coupling, \operatorname{pair}(i, j))) \neq (0))) \Rightarrow ((\operatorname{color}(i)) \neq (\operatorname{color}(j))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.OffDiagonalBipartite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph is the cross-world mediator coupling support, not the causal DAG. Diagonal mass is allowed.

**Definition 1.2 (A bijective color-class flip).**

$$\forall Mediator, color, table, i, (\operatorname{flipTable}(color, table, i)) = (\operatorname{ite}(\operatorname{color}(i), \operatorname{not}(\operatorname{table}(i)), \operatorname{table}(i)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.flipTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each complete table remains an actual response table after the deterministic flip.

**Theorem 1.3 (Recover every original column).**

$$\forall Mediator, color, table, (\operatorname{flipTable}(color, \operatorname{flipTable}(color, table))) = (table)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.flipTable_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The involution ensures the cut optimization covers all original columns.

**Definition 1.4 (Remove harmless loop mass).**

$$\forall Mediator, coupling, (\operatorname{offDiagonalMass}(coupling)) = (\sum_{pair} (\operatorname{ite}((\operatorname{fst}(pair)) \neq (\operatorname{snd}(pair)), \operatorname{mass}(coupling, pair), 0)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.offDiagonalMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Loops never generate benefit and must not be included in the constant cut offset.

**Definition 1.5 (Retain the full vertex field).**

$$\forall Mediator, coupling, multiplier, i, (\operatorname{pricingField}(coupling, multiplier, i)) = (((\operatorname{rightResponseMarginal}(\operatorname{mass}(coupling), i)) - (\operatorname{leftResponseMarginal}(\operatorname{mass}(coupling), i))) - ((2) \cdot (\operatorname{multiplier}(i))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the actual field in the previously proved pricing identity, with no stationarity assumption.

**Definition 1.6 (Signed field after the flip).**

$$\forall Mediator, coupling, color, multiplier, i, (\operatorname{switchedField}(coupling, color, multiplier, i)) = (\operatorname{ite}(\operatorname{color}(i), (0) - (\operatorname{pricingField}(coupling, multiplier, i)), \operatorname{pricingField}(coupling, multiplier, i)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.switchedField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The color class changes the sign of its vertex field.

**Definition 1.7 (Nonnegative internal capacities).**

$$\forall Mediator, coupling, i, j, (\operatorname{pricingCapacity}(coupling, i, j)) = ((\operatorname{mass}(coupling, \operatorname{pair}(i, j))) + (\operatorname{mass}(coupling, \operatorname{pair}(j, i))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingCapacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both directions are retained. Each actual cut counts only the direction crossing from true to false.

**Definition 1.8 (Source terminal capacity).**

$$\forall Mediator, coupling, color, multiplier, i, (\operatorname{pricingSourceCapacity}(coupling, color, multiplier, i)) = (\operatorname{max}(0, \operatorname{switchedField}(coupling, color, multiplier, i)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingSourceCapacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive switched field penalizes placement on the sink side.

**Definition 1.9 (Sink terminal capacity).**

$$\forall Mediator, coupling, color, multiplier, i, (\operatorname{pricingSinkCapacity}(coupling, color, multiplier, i)) = (\operatorname{max}(0, (0) - (\operatorname{switchedField}(coupling, color, multiplier, i))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingSinkCapacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The negative switched field penalizes placement on the source side.

**Definition 1.10 (All additive constants).**

$$\forall Mediator, coupling, color, multiplier, (\operatorname{pricingOffset}(coupling, color, multiplier)) = (((\operatorname{offDiagonalMass}(coupling)) + (\sum_{i} (\operatorname{ite}(\operatorname{color}(i), \operatorname{pricingField}(coupling, multiplier, i), 0)))) + (\sum_{i} (\operatorname{pricingSourceCapacity}(coupling, color, multiplier, i))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retaining these constants is essential to compute the original reduced cost, including its factor of two.

**Theorem 1.11 (Original pricing equals offset minus cut).**

$$\forall Mediator, coupling, color, table, multiplier, (\operatorname{OffDiagonalBipartite}(coupling, color)) \Rightarrow (((2) \cdot (\operatorname{completeMediatorPricingScore}(coupling, multiplier, \operatorname{flipTable}(color, table)))) = ((\operatorname{pricingOffset}(coupling, color, multiplier)) - (\operatorname{stCutValue}(\operatorname{pricingCapacity}(coupling), \operatorname{pricingSourceCapacity}(coupling, color, multiplier), \operatorname{pricingSinkCapacity}(coupling, color, multiplier), table))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricing_cut_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality holds on every complete table. It retains asymmetric mediator masses, arbitrary dual multipliers and loop handling.

**Definition 1.12 (Check the graph contract and optimal flow).**

$$\forall Mediator, coupling, color, multiplier, certificate, (\operatorname{checkBipartitePricing}(coupling, color, multiplier, certificate)) = (\operatorname{and}(\operatorname{decide}(\operatorname{OffDiagonalBipartite}(coupling, color)), \operatorname{checkSTCutCertificate}(\operatorname{pricingCapacity}(coupling), \operatorname{pricingSourceCapacity}(coupling, color, multiplier), \operatorname{pricingSinkCapacity}(coupling, color, multiplier), certificate)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.checkBipartitePricing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both tests are on the actual input; a claimed bipartite shape or solver optimality status is insufficient.

**Definition 1.13 (Return to the original scale).**

$$\forall Mediator, coupling, color, multiplier, certificate, (\operatorname{certifiedPricingValue}(coupling, color, multiplier, certificate)) = (\frac{(\operatorname{pricingOffset}(coupling, color, multiplier)) - (\operatorname{flowValue}(certificate))}{2})$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.certifiedPricingValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is recomputed from the checked flow and the original coefficient offset.

**Theorem 1.14 (A real column and a global maximum).**

$$\forall Mediator, coupling, color, multiplier, certificate, ((\operatorname{checkBipartitePricing}(coupling, color, multiplier, certificate)) = (true)) \Rightarrow (((\operatorname{completeMediatorPricingScore}(coupling, multiplier, \operatorname{flipTable}(color, \operatorname{side}(certificate)))) = (\operatorname{certifiedPricingValue}(coupling, color, multiplier, certificate))) \land (\operatorname{IsGreatest}(\operatorname{range}(\operatorname{completeMediatorPricingScore}(coupling, multiplier)), \operatorname{certifiedPricingValue}(coupling, color, multiplier, certificate))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.checked_pricing_isGreatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The flipped cut realizes the global price bound. The conclusion covers every Boolean column, without enumerating them in the checker.

**Theorem 1.15 (Exact stopping criterion).**

$$\forall Mediator, coupling, color, multiplier, certificate, normalizationMultiplier, ((\operatorname{checkBipartitePricing}(coupling, color, multiplier, certificate)) = (true)) \Rightarrow ((\forall table, (\operatorname{completeMediatorPricingScore}(coupling, multiplier, table)) \le (normalizationMultiplier)) \Leftrightarrow ((\operatorname{certifiedPricingValue}(coupling, color, multiplier, certificate)) \le (normalizationMultiplier)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.checked_no_improving_column_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the full no-positive-reduced-cost condition, not a test only on already generated columns.

**Theorem 1.16 (Rejoin the original causal objective).**

$$\forall Mediator, coupling, multiplier, law, (\operatorname{completeMediatorBenefit}(coupling, law)) = ((\operatorname{linearObjective}(\operatorname{completeMediatorPricingScore}(coupling, multiplier), \operatorname{mass}(law))) + (\sum_{i} ((\operatorname{multiplier}(i)) \cdot (\operatorname{linearObjective}(\lambda table, \operatorname{ite}(\operatorname{apply}(table, i), 1, 0), \operatorname{mass}(law))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.completeMediatorBenefit_eq_pricing_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This expectation identity holds on any fixed coupling, with no bipartite or fair-marginal premise.

**Theorem 1.17 (Bound every canonical outcome law).**

$$\forall Mediator, coupling, multiplier, probability, bound, law, ((\forall table, (\operatorname{completeMediatorPricingScore}(coupling, multiplier, table)) \le (bound)) \land (\forall i, (\operatorname{linearObjective}(\lambda table, \operatorname{ite}(\operatorname{apply}(table, i), 1, 0), \operatorname{mass}(law))) = (\operatorname{probability}(i)))) \Rightarrow ((\operatorname{completeMediatorBenefit}(coupling, law)) \le ((bound) + (\sum_{i} ((\operatorname{multiplier}(i)) \cdot (\operatorname{probability}(i))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricing_bound_implies_causal_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization and the original marginal rows transport the global column bound to a causal upper bound.

**Theorem 1.18 (Certify the full sharp endpoint).**

$$\forall Mediator, coupling, color, multiplier, probability, normalizationMultiplier, certificate, candidate, (((\operatorname{checkBipartitePricing}(coupling, color, multiplier, certificate)) = (true)) \land ((\operatorname{certifiedPricingValue}(coupling, color, multiplier, certificate)) \le (normalizationMultiplier)) \land (\forall i, (\operatorname{linearObjective}(\lambda table, \operatorname{ite}(\operatorname{apply}(table, i), 1, 0), \operatorname{mass}(candidate))) = (\operatorname{probability}(i))) \land ((\operatorname{completeMediatorBenefit}(coupling, candidate)) = ((normalizationMultiplier) + (\sum_{i} ((\operatorname{multiplier}(i)) \cdot (\operatorname{probability}(i))))))) \Rightarrow (\operatorname{IsGreatest}(\operatorname{setOf}(\lambda value, \exists law, (\forall i, (\operatorname{linearObjective}(\lambda table, \operatorname{ite}(\operatorname{apply}(table, i), 1, 0), \operatorname{mass}(law))) = (\operatorname{probability}(i))) \land ((\operatorname{completeMediatorBenefit}(coupling, law)) = (value))), \operatorname{completeMediatorBenefit}(coupling, candidate)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.checked_restricted_master_isGreatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A feasible restricted-master candidate with exact primal/dual equality becomes an attaining law for the full canonical problem when the global pricing check passes. The mediator coupling is fixed throughout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.OffDiagonalBipartite`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.certifiedPricingValue`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.checkBipartitePricing`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.checked_no_improving_column_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.checked_pricing_isGreatest`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.checked_restricted_master_isGreatest`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.completeMediatorBenefit_eq_pricing_expectation`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.flipTable`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.flipTable_involutive`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.offDiagonalMass`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingCapacity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingField`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingOffset`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingSinkCapacity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricingSourceCapacity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricing_bound_implies_causal_bound`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.pricing_cut_identity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing.switchedField`
- Dependency: [D5/S0/Certificates/RationalSTCutCertificate](../../../S0/Certificates/RationalSTCutCertificate.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds](CompleteMediatorCutSharpBounds.md)
