# MediatorPricingRestriction

## Abstract

Original causal pricing is preserved exactly under finite response-coordinate restriction.

M is finite with decidable equality. coupling is the existing normalized rational law on M times M; K is a Finset M; branch maps the subtype K to Bool; table and color map M to Bool; multiplier maps M to Q. All sums are over the whole M carrier.

**Definition 1.1 (Extend the selected response assignment).**

$$\forall M, K, branch, i, (\operatorname{pinTable}(K, branch, i)) = (\operatorname{ite}((i) \in (K), \operatorname{branch}(i), false))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.pinTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The branch is defined on the finite subtype K. The application branch(i) on membership uses the corresponding subtype witness; all other coordinates are false.

**Definition 1.2 (Reassemble an original response column).**

$$\forall M, K, branch, table, i, (\operatorname{clampTable}(K, branch, table, i)) = (\operatorname{ite}((i) \in (K), \operatorname{apply}(\operatorname{pinTable}(K, branch), i), \operatorname{table}(i)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.clampTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fixed coordinates use the selected branch and all free coordinates retain the supplied original table values.

**Theorem 1.3 (Every original column has a branch).**

$$\forall M, K, table, (\operatorname{clampTable}(K, \lambda i, \operatorname{table}(i), table)) = (table)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.clampTable_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here i in the restriction lambda ranges over K, with its underlying mediator value used by table. No original complete table is excluded.

**Definition 1.4 (Redirect removed mass to the diagonal).**

$$\forall M, K, pair, (\operatorname{absorbPair}(K, pair)) = (\operatorname{ite}((\operatorname{not}((\operatorname{fst}(pair)) \in (K))) \land (\operatorname{not}((\operatorname{snd}(pair)) \in (K))), pair, \operatorname{pair}(\operatorname{fst}(pair), \operatorname{fst}(pair))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.absorbPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Free/free pairs are unchanged. All other pairs retain their mass on a diagonal pair. This is a computational map, not conditioning the mediator law.

**Definition 1.5 (Keep the normalized response-law API).**

$$\forall M, coupling, K, (\operatorname{residualCoupling}(coupling, K)) = (\operatorname{pushforwardResponseLaw}(coupling, \operatorname{absorbPair}(K)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.residualCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deterministic pushforward stays on the full mediator-pair carrier and preserves normalization and nonnegativity. Its changed marginal values are not substituted into the original data constraints.

**Theorem 1.6 (Compute the residual off-diagonal coefficients).**

$$\forall M, coupling, K, i, j, ((i) \neq (j)) \Rightarrow ((\operatorname{mass}(\operatorname{residualCoupling}(coupling, K), \operatorname{pair}(i, j))) = (\operatorname{ite}((\operatorname{not}((i) \in (K))) \land (\operatorname{not}((j) \in (K))), \operatorname{mass}(coupling, \operatorname{pair}(i, j)), 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.residualCoupling_offDiagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Outside the diagonal, the residual keeps exactly the original coefficients with both endpoints free.

**Theorem 1.7 (Identify the exact graph condition).**

$$\forall M, coupling, K, color, (\operatorname{OffDiagonalBipartite}(\operatorname{residualCoupling}(coupling, K), color)) \Leftrightarrow (\forall i, j, ((\operatorname{not}((i) \in (K))) \land (\operatorname{not}((j) \in (K))) \land ((i) \neq (j)) \land ((\operatorname{mass}(coupling, \operatorname{pair}(i, j))) \neq (0))) \Rightarrow ((\operatorname{color}(i)) \neq (\operatorname{color}(j))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.residualCoupling_bipartite_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bipartiteness concerns the original support after removing K, including both directed orientations. Original self-loops impose no condition.

**Definition 1.8 (Retain both oriented boundary contributions).**

$$\forall M, coupling, K, branch, multiplier, i, (\operatorname{branchMultiplier}(coupling, K, branch, multiplier, i)) = (((\operatorname{ite}((i) \in (K), 0, \operatorname{multiplier}(i))) + (\sum_{j} (\operatorname{ite}((\operatorname{not}((i) \in (K))) \land ((j) \in (K)) \land ((\operatorname{apply}(\operatorname{pinTable}(K, branch), j)) = (true)), \operatorname{mass}(coupling, \operatorname{pair}(i, j)), 0)))) - (\sum_{j} (\operatorname{ite}(((j) \in (K)) \land (\operatorname{not}((i) \in (K))) \land ((\operatorname{apply}(\operatorname{pinTable}(K, branch), j)) = (false)), \operatorname{mass}(coupling, \operatorname{pair}(j, i)), 0))))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.branchMultiplier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Free-to-fixed-one edges add to the multiplier; fixed-zero-to-free edges subtract. Fixed-coordinate multipliers become zero in the residual problem and stay in the branch offset.

**Definition 1.9 (Compute the constant in the original objective).**

$$\forall M, coupling, K, branch, multiplier, (\operatorname{branchOffset}(coupling, K, branch, multiplier)) = (\operatorname{completeMediatorPricingScore}(coupling, multiplier, \operatorname{pinTable}(K, branch)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.branchOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The offset includes fixed/fixed benefit, free-zero/fixed-one benefit and all original fixed-coordinate multiplier contributions.

**Theorem 1.10 (Exact original-to-residual pricing equality).**

$$\forall M, coupling, K, branch, multiplier, table, (\operatorname{completeMediatorPricingScore}(coupling, multiplier, \operatorname{clampTable}(K, branch, table))) = ((\operatorname{branchOffset}(coupling, K, branch, multiplier)) + (\operatorname{completeMediatorPricingScore}(\operatorname{residualCoupling}(coupling, K), \operatorname{branchMultiplier}(coupling, K, branch, multiplier), table)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.pricing_restriction_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds before any bipartite assumption. No removed mass is renormalized, and reassembly gives one actual original outcome-response table.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.absorbPair`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.branchMultiplier`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.branchOffset`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.clampTable`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.clampTable_restrict`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.pinTable`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.pricing_restriction_identity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.residualCoupling`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.residualCoupling_bipartite_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MediatorPricingRestriction.residualCoupling_offDiagonal`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing](BipartiteMediatorPricing.md)
