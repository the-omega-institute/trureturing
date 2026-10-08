# Native tests and finite joint masses

## Abstract

Linear readouts of finite native tests in a shared-parameter marker source.

**Theorem 1.1 (Linear tests and normalized successors).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.result`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite component family, task, strictly positive root parameter and component parameters, and strictly positive weights summing to one, the full carrier has exactly four times the component count plus the task terminal count coordinates. Its action-output columns are normalized and nonnegative, and it preserves every native finite-test probability. For every current history, chosen arm and original source, a native step with positive matrix output mass updates the history feature by dividing its joint matrix pushforward by that output mass. This includes zero replies, marker replies and terminal rejection.

**Theorem 1.2 (Native feature updates).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_feature_updates`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_feature_updates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite component family, task, strictly positive alpha and component parameters, and positive weights summing to one, the concrete full feature follows the normalized joint output-successor matrix for every history, queried arm and source whenever that output has positive matrix mass.

**Theorem 1.3 (Measurable native marker response).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.measurable_marker_response`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.measurable_marker_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each arm and natural edge count, its native marker response is a measurable function of the original source.

**Theorem 1.4 (Measurable native test acceptance).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.measurable_native_accept`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.measurable_native_accept` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every task, finite test and acquired history, native test acceptance is a measurable Boolean function of the original source.

**Theorem 1.5 (Positive posterior denominator).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.denominator_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.denominator_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha and q in the closed unit interval, if alpha is strictly positive then the denominator alpha plus (one minus alpha) times q to the sum of the two parity bits is strictly positive for every parity pair.

**Theorem 1.6 (Terminal rows agree with terminal execution).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_terminal_row`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_terminal_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every component count, task, alpha, parameter family, terminal coordinate and finite test, its fixed test row at that coordinate equals the zero-or-one decision obtained by terminal execution in that coordinate's mode.

**Theorem 1.7 (Active row recursion).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_active_row`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_active_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every component, parity pair, queried arm and output continuation, the active test row is the zero-output successor row weighted by one minus the component marker rate, plus the terminal continuation decision weighted by the marker rate. The output and terminal mode obey the selected task and the selected parity bit.

**Theorem 1.8 (Lawful full finite carrier).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_model_probability`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_model_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite component family and task, with strictly positive alpha, the full carrier has four times the component count plus the terminal count coordinates, every joint output-successor entry is nonnegative, and each action column sums to one across all outputs and successor coordinates.

**Theorem 1.9 (Original-history conditional probabilities have fixed linear readouts).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.native_finite_test_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.native_finite_test_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha and every component parameter q lie in the unit interval and be strictly positive. Let the finitely many real component weights be strictly positive and sum to one. Each component generates two complete conditionally independent Markov arms at the same parameter and root. The source law is the finite mixture of these full source laws.

For every measurable seed space, independent probability seed law, causal policy, finite time, acquired history and measurable seed event having positive joint mass, the history feature is a nonnegative vector with total mass one. Every finite residual test has original-source joint acceptance mass equal to the conditioning-event mass times the feature vector paired with its fixed test row.

A test may inspect the current mode, query either arm and branch on the newly acquired output, or finish with a Boolean decision. It reads no old seed or archive. Native queries call the original marker response on the next unread arm edge. The retained-root interface preserves the recovered root after stopping; the emitted-root interface exposes it only in the marker output; the raw interface emits the marker alone. Further terminal queries reject without reading the source.

The full carrier has four active parity coordinates per component and two shared terminal coordinates for the retained-root interface, or one shared terminal coordinate for the other interfaces. Its cardinality is exactly four times the component count plus the terminal count. Every matrix entry is nonnegative, and for each action and source coordinate the sum over all outputs and successor coordinates is one. Its joint output-successor matrices do not depend on the old history, time or seed. Backward finite-test evaluation gives a single fixed linear row. Original acceptance events and matrix rows are defined independently.

The proof separates the old seed replay fiber from its original all-zero source cylinder. At a fixed root, extending a cylinder either produces the next all-zero cylinder or its marker complement. After a marker, the residual acceptance decision is source-independent. Root-weight transport and finite mixture summation then identify the native event with the linear row.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.denominator_pos`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_active_row`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_feature_updates`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_model_probability`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.full_terminal_row`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.measurable_marker_response`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.measurable_native_accept`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.native_finite_test_realization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.result`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails](AdaptiveMarkerStoppingTails.md)
