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

The formal-series application of actual_count_recurrence takes F in the ring of formal power series over the integers, with coefficient n equal to returnCount n. The guards are precisely the zero coefficients below the two delays. Comparing coefficients gives (1-X^3-X^10)F=X^13. The denominator has constant coefficient one, so PowerSeries.invOfUnit supplies its inverse and F=X^13 invOfUnit(1-X^3-X^10,1). Quotient notation for this identity means multiplication by this formal unit inverse; no analytic evaluation or convergence is assumed.

For original return length k, define c_k as the cardinality of actual nonempty positive return lists xs with listWeight xs=k. The finite fibers of actual_count_middle and actual_list_weight_even give c_(2n)=returnCount n and c_(2n+1)=0. PowerSeries.expand by two sends F to T with these exact coefficients. It sends X^3 and X^10 to z^6 and z^20, and the pulse X^13 to z^26. Thus (1-z^6-z^20)T=z^26 and T=z^26 invOfUnit(1-z^6-z^20,1), or z^26/(1-z^6-z^20) in formal quotient notation. This counts nonempty lists; its constant coefficient is zero.

The empty list contributes one separately. paired_source_reconstruction identifies the original history length as 26+listWeight xs, while complete_execution_word_parser makes history .original injective on the actual lists. Consequently the coefficient at k of z^26(1+T) is exactly the number of these actual histories of length k. The empty list is the unique history at length 26, and every history has even length. The 26-window outer stem is distinct from the forced 26-window endpoints of a nonempty return list. The construction retains the same prescribed sources, execution reversal and fixed tails.

For every natural original return-length horizon N, let C(N) be the number of actual nonempty positive lists with listWeight xs at most N. The same even-weight map identifies this finite fiber with the disjoint union of ReturnFiber n over n in Fin(N/2+1). Hence C(N) is the sum of returnCount n for 0 through floor(N/2). Here N/2 is natural-number division, not real division. No odd-length fiber is included implicitly. Adding the empty list gives exactly 1+C(N), which matches the cumulative convention in source section 55.3 because returnCount 0 is zero.

Fix 0<x<1 with x^3+x^10=1, and put q=x inverse, A=x^40 and B=x^13 q/(q-1). These constants are positive and q>1. Applying actual_count_window to each fiber and the finite geometric-sum identity gives C(N) at most B q^floor(N/2) for every N. For N at least 62, the last fiber index is at least 31, so its lower window bound gives A q^floor(N/2) at most C(N). Thus for N at least 62, A q^floor(N/2) is at most 1+C(N), which is at most (B+1)q^floor(N/2). Since floor(N/2) lies between N/2-1 and N/2, the same bounds also give x^41 x^(-N/2) at most C(N), which is at most B x^(-N/2), for N at least 62; the exponents in this last expression are real powers. The lower bound has no positive all-N extension for nonempty lists: C(N)=0 when N<26. This finite initial range has no effect on the limiting rate.

Taking base-two logarithms of the positive bounds and dividing by N squeezes log2(C(N))/N between log2(A)/N plus floor(N/2)/N times log2(q), and the analogous expression with B. The floor ratio tends to one half, so the limit over all integer N is -log2(x)/2. The bound C(N) at most 1+C(N) at most 2C(N), valid from N=62, proves the same limit for the empty-list convention. Specializing x to criticalX gives alphaInfinity. The positive root is unique; zStar=sqrt(x) lies in (0,1), satisfies zStar^6+zStar^20=1, and -log2(zStar)=-log2(x)/2. These radius identities do not assert analytic convergence of the formal series.

For complete original histories with horizon N, the cumulative count is zero for N<26 and exactly 1+C(N-26) for N at least 26. For N at least 88 the displayed bounds apply with floor((N-26)/2). Composing the return-length rate with N minus 26 and multiplying by (N-26)/N proves that the history cumulative rate is also alphaInfinity over all integer horizons. Exact odd-length return counts remain zero; this all-integer statement concerns cumulative counts. The cumulative argument is not used to mix unequal histories in the equal-checkpoint storage injection.

These are consequences of the existing actual count, parity, parser and source-length declarations together with formal-series, finite geometric-sum and limit identities. They do not provide a decoder with free boundaries or positions. Section 55.2's endpoint sharpness, actual inner-slot costs, minimum family budget, lack of a uniform positive family margin and necessary subcritical cap require their own actual-source bridges. The universal representation of Definition 36.9 and the closed-observation online construction of section 33.13, including finite updates and complete linear workspace, control and counter accounting, remain separate obligations. Neither an attainable lower coefficient nor a globally optimal coefficient or matching optimal memory order follows from these applications.

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
