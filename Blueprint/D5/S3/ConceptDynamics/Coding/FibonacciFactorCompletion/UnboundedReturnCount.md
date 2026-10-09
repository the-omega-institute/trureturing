# Unbounded positive return counts

## Abstract

Positive return lists are in bijection with their weighted binary middle words.

A return has positive integer exponents m and r and contributes six m plus twenty r original windows. Execution order reverses the external source order: the nonempty execution word has the form c W u, corresponding to U W C externally. The existing maximal-run parser identifies every such word with exactly one positive return list. No bound on either exponent, block boundaries supplied to a decoder, or finite-memory language is assumed.

**Definition 1.1 (halfWeight).**

$$\operatorname{halfWeight}\left(\operatorname{nil}\left(CuLetter\right)\right) = 0 \land \left(\left(\forall w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{halfWeight}\left(\operatorname{cons}\left(c, w\right)\right) = \operatorname{add}\left(10, \operatorname{halfWeight}\left(w\right)\right)\right) \land \left(\forall w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{halfWeight}\left(\operatorname{cons}\left(u, w\right)\right) = \operatorname{add}\left(3, \operatorname{halfWeight}\left(w\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.halfWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The half length gives weight ten to c and three to u.

**Definition 1.2 (middleWords).**

$$\forall n \in Nat,\; \operatorname{middleWords}\left(n\right) = \operatorname{union}\left(\operatorname{ifThenElse}\left(n = 0, \operatorname{singleton}\left(\operatorname{nil}\left(CuLetter\right)\right), \operatorname{emptyFinset}\left(\operatorname{List}\left(CuLetter\right)\right)\right), \operatorname{union}\left(\operatorname{ifThenElse}\left(\operatorname{le}\left(3, n\right), \operatorname{image}\left((w : \operatorname{List}\left(CuLetter\right) \mapsto \operatorname{cons}\left(u, w\right)), \operatorname{middleWords}\left(\operatorname{subtract}\left(n, 3\right)\right)\right), \operatorname{emptyFinset}\left(\operatorname{List}\left(CuLetter\right)\right)\right), \operatorname{ifThenElse}\left(\operatorname{le}\left(10, n\right), \operatorname{image}\left((w : \operatorname{List}\left(CuLetter\right) \mapsto \operatorname{cons}\left(c, w\right)), \operatorname{middleWords}\left(\operatorname{subtract}\left(n, 10\right)\right)\right), \operatorname{emptyFinset}\left(\operatorname{List}\left(CuLetter\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.middleWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set enumerates exactly the binary words with the specified half length. Its three branches distinguish the empty word and the first letter.

**Definition 1.3 (ReturnFiber).**

$$\forall n \in Nat,\; \operatorname{ReturnFiber}\left(n\right) = \operatorname{subtype}\left((xs : \operatorname{List}\left(Return\right) \mapsto \operatorname{ne}\left(xs, \operatorname{nil}\left(Return\right)\right) \land \operatorname{listWeight}\left(xs\right) = \operatorname{multiply}\left(2, n\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.ReturnFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only nonempty actual positive return lists with original length twice n belong to this fiber.

**Definition 1.4 (returnCount).**

$$\forall n \in Nat,\; \operatorname{returnCount}\left(n\right) = \operatorname{NatCard}\left(\operatorname{ReturnFiber}\left(n\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.returnCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the cardinality of the original list fiber, independently of its word enumeration.

**Theorem 1.5 (actual count middle).**

$$\forall n \in Nat,\; \operatorname{Finite}\left(\operatorname{ReturnFiber}\left(n\right)\right) \land \operatorname{returnCount}\left(n\right) = \operatorname{ifThenElse}\left(\operatorname{le}\left(13, n\right), \operatorname{card}\left(\operatorname{middleWords}\left(\operatorname{subtract}\left(n, 13\right)\right)\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_middle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forced endpoints have half length thirteen. Removing them preserves weight and gives the finite middle-word dictionary; the inverse uses complete run decomposition.

**Theorem 1.6 (actual count recurrence).**

$$\forall n \in Nat,\; \operatorname{returnCount}\left(n\right) = \operatorname{add}\left(\operatorname{add}\left(\operatorname{ifThenElse}\left(\operatorname{le}\left(3, n\right), \operatorname{returnCount}\left(\operatorname{subtract}\left(n, 3\right)\right), 0\right), \operatorname{ifThenElse}\left(\operatorname{le}\left(10, n\right), \operatorname{returnCount}\left(\operatorname{subtract}\left(n, 10\right)\right), 0\right)\right), \operatorname{ifThenElse}\left(n = 13, 1, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The disjoint first-middle-letter partition subtracts three or ten. The empty middle contributes the pulse at thirteen. The guards implement zero extension, including indices below a delay.

**Theorem 1.7 (actual count support).**

$$\forall n \in Nat,\; \operatorname{lt}\left(0, \operatorname{returnCount}\left(n\right)\right) \Leftrightarrow \left(\exists a \in Nat, b \in Nat,\; n = \operatorname{add}\left(\operatorname{add}\left(13, \operatorname{multiply}\left(3, a\right)\right), \operatorname{multiply}\left(10, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact support is thirteen plus the semigroup generated by three and ten. In particular thirty is unsupported, whereas every index from thirty-one onward is supported.

**Theorem 1.8 (actual count window).**

$$\forall x \in Real,\; \left(\operatorname{lt}\left(0, x\right) \land \left(\operatorname{lt}\left(x, 1\right) \land \operatorname{add}\left(\operatorname{power}\left(x, 3\right), \operatorname{power}\left(x, 10\right)\right) = 1\right)\right) \Rightarrow \left(\left(\forall n \in Nat,\; \operatorname{le}\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{returnCount}\left(n\right)\right), \operatorname{power}\left(x, n\right)\right), \operatorname{power}\left(x, 13\right)\right)\right) \land \left(\forall n \in Nat,\; \operatorname{le}\left(31, n\right) \Rightarrow \operatorname{le}\left(\operatorname{power}\left(x, 40\right), \operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{returnCount}\left(n\right)\right), \operatorname{power}\left(x, n\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scaling the recurrence by x to the index gives a convex combination. All indices thirty-one through forty are positive; the complete ten-index window has lower bound x to the fortieth power, which strong induction preserves. The upper bound starts at the pulse x to the thirteenth power.

**Definition 1.9 (criticalX).**

$$criticalX = \operatorname{choose}\left(\exists x \in Real,\; \operatorname{lt}\left(0, x\right) \land \left(\operatorname{lt}\left(x, 1\right) \land \operatorname{add}\left(\operatorname{power}\left(x, 3\right), \operatorname{power}\left(x, 10\right)\right) = 1\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.criticalX` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The radius is chosen in the open unit interval where its third and tenth powers sum to one. Continuity and the endpoint values zero and two establish existence.

**Definition 1.10 (alphaInfinity).**

$$alphaInfinity = \operatorname{divide}\left(\operatorname{negate}\left(\operatorname{logb}\left(2, criticalX\right)\right), 2\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.alphaInfinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Dividing the negative base-two radius logarithm by two converts half lengths to original-window lengths.

**Theorem 1.11 (actual count log bounds).**

$$\operatorname{lt}\left(0, alphaInfinity\right) \land \left(\forall n \in Nat,\; \operatorname{le}\left(31, n\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{toReal}\left(\operatorname{returnCount}\left(n\right)\right)\right) \land \left(\operatorname{le}\left(\operatorname{subtract}\left(\operatorname{multiply}\left(\operatorname{multiply}\left(2, alphaInfinity\right), \operatorname{toReal}\left(n\right)\right), \operatorname{multiply}\left(80, alphaInfinity\right)\right), \operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{returnCount}\left(n\right)\right)\right)\right) \land \operatorname{le}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{returnCount}\left(n\right)\right)\right), \operatorname{subtract}\left(\operatorname{multiply}\left(\operatorname{multiply}\left(2, alphaInfinity\right), \operatorname{toReal}\left(n\right)\right), \operatorname{multiply}\left(26, alphaInfinity\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The count is positive from thirty-one onward. Its base-two logarithm lies between twice alpha times n minus eighty alpha and twice alpha times n minus twenty-six alpha. These fixed errors apply on the even original-length lattice.

**Theorem 1.12 (actual even rate).**

$$\operatorname{IsBigO}\left(atTop, (n : Nat \mapsto \operatorname{subtract}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{returnCount}\left(n\right)\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(2, alphaInfinity\right), \operatorname{toReal}\left(n\right)\right)\right)), \operatorname{constantFunction}\left(Nat, Real, 1\right)\right) \land \operatorname{Tendsto}\left((n : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{returnCount}\left(n\right)\right)\right), \operatorname{multiply}\left(2, \operatorname{toReal}\left(n\right)\right)\right)), atTop, \operatorname{nhds}\left(alphaInfinity\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_even_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic error is bounded by a constant. Dividing the two explicit logarithmic bounds by twice n gives the limit alpha along the even original-length lattice. This limit counts the specified actual family.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.ReturnFiber`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_log_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_middle`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_recurrence`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_support`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_count_window`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.actual_even_rate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.alphaInfinity`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.criticalX`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.halfWeight`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.middleWords`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.returnCount`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion](Completion.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Operations](Operations.md)
