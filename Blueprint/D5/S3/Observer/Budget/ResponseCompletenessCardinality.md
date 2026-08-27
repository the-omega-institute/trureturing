# Response-Completeness Cardinality Bound

## Abstract

Response completeness forces enough protocol response classes for every table.

**Theorem 1.1 (Complete response columns satisfy the finite counting bound).**

$$\begin{gathered}\forall X, P, Lambda: Type,\\{}\operatorname{Fintype}(X), \operatorname{Fintype}(Lambda),\\{}e: X \to P \to Lambda,\\{}{\forall f: X \to Lambda, \exists p: P, \forall x: X, \operatorname{e}(x, p) = \operatorname{f}(x)} \Rightarrow\\{}\operatorname{card}(Lambda)^{\operatorname{card}(X)} \leq \operatorname{card}(\operatorname{Quotient}(\operatorname{ker}((p \mapsto (x \mapsto \operatorname{e}(x, p)))))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ResponseCompletenessCardinality.response_complete_card_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluation channel sends each protocol to its complete response column on X. Response completeness makes this map surjective onto all Lambda-valued response tables.

The equality-kernel quotient is canonically equivalent to the realized range, so it has at least card(Lambda)^card(X) classes. The proof uses the kernel quotient itself rather than choosing representatives.

The source assumes card(X) at least one and card(Lambda) at least two. Neither numerical bound is needed for this counting implication, so the machine theorem also covers empty or singleton carriers.

## References

- Truth anchor: `D5/S3/Observer/Budget/ResponseCompletenessCardinality.response_complete_card_lower_bound`
- Dependency: [D5/S3/Observer/Completion/DoubleExtensionalQuotientUniversality](../Completion/DoubleExtensionalQuotientUniversality.md)
