# Finite atom upper bounds

## Abstract

Finite native-test readouts through the exceptional parity quotient.

**Theorem 1.1 (Three finite native-test carriers).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.result`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite family of distinct parameters strictly between zero and one, every root probability strictly between zero and one, and positive component weights summing to one, the number of components satisfying alpha equals (one minus alpha) times the parameter is at most one. If alpha is at least one half, the exceptional component count is zero.

The retained-root interface admits a finite carrier of cardinality four times the component count plus two; the emitted-root interface admits cardinality four times the component count plus one. The raw interface admits cardinality four times the component count minus twice the exceptional component count plus one. Every carrier has nonnegative joint output-successor matrices whose columns sum to one across all outputs and successors.

For every measurable independent old seed, causal policy, finite acquired history and measurable old-seed event with positive original joint mass, the feature is nonnegative and normalized. Every finite output-adaptive residual test has its original acceptance mass equal to that conditioning mass times the fixed linear readout. Native events are independently defined by actual source execution. A fresh independent probability seed may sample any measurable family of finite tests; integrating each fixed test row gives the same original-source randomized acceptance probability. For each positive-mass native output, the new history feature is the joint output matrix applied to the old feature, divided by its total output mass. The actual conditional output mass is the total matrix pushforward mass. For a specified next query j, scaling the new feature by the joint mass of its output event gives the old event mass times the unnormalized matrix pushforward. The next query is fixed in this relation; the event is not the complete next-history event under the original randomized policy.

In each exceptional raw component the parity pairs zero-zero and one-one share the even coordinate, while one-zero and zero-one share the odd coordinate. This quotient preserves marker rates, flips even and odd on a zero reply, and sends every marker to the shared terminal coordinate. Pushing the full feature through this quotient preserves every finite output-adaptive test row and every normalized output-successor update. Under the source mixture, almost every source couples the recovered terminal bit to its original root for every causal policy, seed value and finite stopping history.

**Theorem 1.2 (Finite test rows descend through the raw quotient).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_row_descends`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_row_descends` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite component family, strictly positive unit-interval alpha, finite test and full raw coordinate, the test row at its encoded raw coordinate equals the full carrier test row at the original coordinate.

**Theorem 1.3 (Cardinality of one raw component).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_component_card`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_component_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-interval alpha and component parameter q, the raw canonical parity pairs number two if alpha equals (one minus alpha) times q, and four otherwise.

**Theorem 1.4 (Concrete raw test readouts).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_native_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_native_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite component family, strictly positive alpha and component parameters, and positive weights summing to one, the concrete rawModel and rawFeature preserve all original-history conditional native finite-test probabilities, with normalized nonnegative history features.

**Theorem 1.5 (Concrete raw feature updates).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_feature_updates`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_feature_updates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same positivity and weight normalization assumptions, the concrete raw feature updates by normalized joint output-successor transport for every history, queried arm and source whose output matrix mass is positive.

**Theorem 1.6 (Raw carrier cardinality).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_card`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite component family and unit-interval alpha, the concrete raw carrier has exactly four times the component count minus twice the exceptional component count plus one coordinates.

**Theorem 1.7 (Raw probability columns).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_probability`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite component family and strictly positive alpha, the concrete raw joint output-successor matrices are nonnegative and each action column sums to one over all outputs and successor coordinates.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_card`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_component_card`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_feature_updates`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_native_bridge`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_probability`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.raw_row_descends`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.result`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization](FiniteAtomLinearRealization.md)
