# A continuous source lift for triangle inflation

## Abstract

Measurable stochastic triangle responses generate a finite observable law on genuinely independent continuous source copies.

Let Copy and Node be finite types. Sources are pairs (e,i), with e in {alpha,beta,gamma} and i in Copy. Each coordinate has Lebesgue measure restricted to [0,1], and the common source carrier is the full function space from Sources to Real with the finite product measure. An inflation specification assigns each node a party v in {A,B,C} and copies of its two incident sources: A reads beta,gamma, B reads gamma,alpha, and C reads alpha,beta. The source types are fixed by the party, so the specification cannot wire an A node to alpha.

A response model consists of the three measurable nonnegative stochastic responses with four outcomes. For a complete observable assignment o, its conditional weight is the product over nodes of the actual response probability evaluated on that node's incident source copies. The inflation mass q(o) is the integral of this weight over the common continuous product-source carrier. No finite source discretization, supplied lifted law, or premise asserting the desired inflation constraints is used.

**Theorem 1.1 (Every observable cell has nonnegative mass).**

$$\operatorname{Nonnegative}\left(\operatorname{InflationMass}\left(S, R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.inflationMass_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each response is nonnegative. Its finite product remains nonnegative, and integration over the source product measure preserves the inequality.

**Theorem 1.2 (The lifted observable cells have total mass one).**

$$\operatorname{TotalMass}\left(\operatorname{InflationMass}\left(S, R\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.inflationMass_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every response lies between zero and one, so each measurable cell weight is integrable. Interchange the finite sum over observable assignments with integration. Finite distributivity turns the sum of conditional product weights into the product of the individual response sums. Every response sum equals one and the continuous source product measure is a probability measure.

**Theorem 1.3 (The original local model supplies the responses).**

$$\operatorname{Implies}\left(\operatorname{IsTriangleLocal}\left(p\right), \operatorname{ExistsRepresentingResponseModel}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.isTriangleLocal_responseModel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unpack the original continuous local-model witness. Its three measurable, nonnegative normalized responses give the response model R, and their original three-source integral is exactly Represents R p. This covers the existing continuous local predicate without adding a finite hidden-variable restriction.

**Theorem 1.4 (Summing the unobserved outcomes gives the retained marginal).**

$$\operatorname{SumUnobserved}\left(q, J, o\right) = \operatorname{MarginalMass}\left(S, R, J, o\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.inflationMass_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite retained node block J and every assignment o on J, sum q over all extensions on the complement. Split the finite product into retained and unobserved nodes. Normalization of each unobserved response removes its factor, leaving the integral of the retained response product.

**Theorem 1.5 (A retained observable can also be marginalized).**

$$\operatorname{SumInsertedOutcome}\left(J, v\right) = \operatorname{MarginalMass}\left(S, R, J, o\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_sum_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When v is outside J, summing the marginal on J union {v} over v's four outcomes gives the marginal on J. The proof uses actual stochastic-response normalization and finite-sum interchange with integration.

**Theorem 1.6 (Blocks using disjoint sources factor).**

$$\operatorname{MarginalMass}\left(\operatorname{Union}\left(J, K\right)\right) = \operatorname{MarginalMass}\left(J\right) \cdot \operatorname{MarginalMass}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_disjoint_source_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the node blocks J and K are disjoint and their exact incident source supports are disjoint. Product-source coordinate independence gives independence of the two source groups and hence of their measurable response products. Integrating their product yields the product of the two marginal masses. The second factor can be an unknown retained marginal of the same full inflation law.

**Theorem 1.7 (One source copy of each type has the original continuous law).**

$$\operatorname{MapTriangleSources}\left(SourceMeasure\right) = \operatorname{Product}\left(UnitSource, \operatorname{Product}\left(UnitSource, UnitSource\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.sourceMeasure_map_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary chosen alpha, beta and gamma copy labels, the triple of their real source coordinates has the product of three uniform [0,1] measures. All unused source copies disappear under this actual measure pushforward; this also permits unequal copy counts embedded in the common finite Copy type.

**Theorem 1.8 (A correctly wired copied triangle has distribution p).**

$$\operatorname{MarginalMass}\left(CopiedTriangle\right) = \operatorname{p}\left(a, b, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume R represents p. If A reads the chosen beta,gamma copies, B reads gamma,alpha and C reads alpha,beta, their three-node marginal equals p(a,b,c). Project to the three actual source coordinates, reuse the continuous triple law, and recover exactly the original restricted-volume integral.

**Theorem 1.9 (The A-node marginal is the observed one-party marginal).**

$$\operatorname{MarginalMass}\left(A\right) = \operatorname{SumBC}\left(p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_singleton_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same correctly wired triangle hypotheses, the A-node marginal equals the sum of p(a,b,c) over b and c. Sum out C and then B from the derived triangle marginal; no one-party distribution is supplied as a premise.

**Theorem 1.10 (The B-node marginal is the observed one-party marginal).**

$$\operatorname{MarginalMass}\left(B\right) = \operatorname{SumAC}\left(p, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_singleton_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a correctly wired copied triangle represented by R, the B-node marginal is the sum of p(a,b,c) over a and c. This follows by summing the actual A and C response factors, with no party symmetry assumption.

**Theorem 1.11 (The C-node marginal is the observed one-party marginal).**

$$\operatorname{MarginalMass}\left(C\right) = \operatorname{SumAB}\left(p, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_singleton_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a correctly wired copied triangle represented by R, the C-node marginal is the sum of p(a,b,c) over a and b. Sum out A and B under the same continuous lift; arbitrary raw responses need not be symmetric.

**Theorem 1.12 (Reindexing identical source copies preserves q).**

$$\operatorname{InflationMass}\left(\operatorname{Compose}\left(o, pi\right)\right) = \operatorname{InflationMass}\left(o\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.inflationMass_copy_symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A node permutation pi preserving party labels, paired with a source-coordinate permutation tau carrying both incident sources to those of each permuted node, preserves every observable cell mass. The finite product-source measure is preserved by coordinate reindexing. This is copy symmetry; no symmetry of arbitrary raw party responses is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.inflationMass_copy_symmetry`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.inflationMass_marginal`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.inflationMass_nonnegative`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.inflationMass_normalized`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.isTriangleLocal_responseModel`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_disjoint_source_factorization`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_singleton_A`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_singleton_B`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_singleton_C`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_sum_insert`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.marginalMass_triangle`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInflationSoundness.sourceMeasure_map_triangle`
- Dependency: [D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation](TriangleSymmetricLocalRefutation.md)
