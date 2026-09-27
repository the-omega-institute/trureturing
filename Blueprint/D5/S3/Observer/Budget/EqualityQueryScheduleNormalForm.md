# Equality Query Schedule Normal Form

## Abstract

A terminating equality-query protocol that identifies finite candidates admits a distinct exhaustive schedule with no greater query count at any target. The final candidate is identified without an additional query.

An equality query at a center returns true exactly when the target equals that center. Protocols use the canonical PassiveProtocol tree and runPassiveProtocol executor. The scan of an empty or singleton list stops immediately; otherwise it queries the first candidate, stops on true, and scans the remaining list on false. Positions idxOf are zero based, and subtraction in the formulas is natural subtraction.

**Theorem 1.1 (Identification and the exact stopping count of a schedule).**

$$\begin{aligned}\forall A: \operatorname{Type}, [\operatorname{DecidableEq}\left(A\right)],\\\forall L: \operatorname{List}\left(A\right), \operatorname{Nodup}\left(L\right) \Rightarrow\\(\forall x \in L, \forall y \in L, \operatorname{runPassiveProtocol}\left(equalityReadout, \operatorname{scan}\left(L\right), x\right) = \operatorname{runPassiveProtocol}\left(equalityReadout, \operatorname{scan}\left(L\right), y\right) \Rightarrow x = y) \land\\(\forall x \in L, \operatorname{length}\left(\operatorname{runPassiveProtocol}\left(equalityReadout, \operatorname{scan}\left(L\right), x\right)\right) = \operatorname{min}\left(\operatorname{idxOf}\left(L, x\right) + 1, \operatorname{length}\left(L\right) - 1\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/EqualityQueryScheduleNormalForm.scan_identifies_with_exact_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the list separates a successful first query from its negative continuation. Distinctness ensures identification. The query count is the one-based position capped at length minus one, so a singleton costs zero and the last two positions of a longer list have the same cost.

**Theorem 1.2 (Every identifying tree admits a pointwise faster schedule).**

$$\begin{aligned}\forall A: \operatorname{Type}, [\operatorname{DecidableEq}\left(A\right)],\\\forall T: \operatorname{PassiveProtocol}\left(A, (c \mapsto \operatorname{Bool})\right), S: \operatorname{Finset}\left(A\right),\\(\forall x \in S, \forall y \in S, \operatorname{runPassiveProtocol}\left(equalityReadout, T, x\right) = \operatorname{runPassiveProtocol}\left(equalityReadout, T, y\right) \Rightarrow x = y) \Rightarrow\\\exists L: \operatorname{List}\left(A\right), \operatorname{Nodup}\left(L\right) \land \operatorname{toFinset}\left(L\right) = S \land\\(\forall x \in S, \forall y \in S, \operatorname{runPassiveProtocol}\left(equalityReadout, \operatorname{scan}\left(L\right), x\right) = \operatorname{runPassiveProtocol}\left(equalityReadout, \operatorname{scan}\left(L\right), y\right) \Rightarrow x = y) \land\\(\forall x \in S, \operatorname{length}\left(\operatorname{runPassiveProtocol}\left(equalityReadout, \operatorname{scan}\left(L\right), x\right)\right) = \operatorname{min}\left(\operatorname{idxOf}\left(L, x\right) + 1, \operatorname{card}\left(S\right) - 1\right)) \land\\(\forall x \in S, \operatorname{length}\left(\operatorname{runPassiveProtocol}\left(equalityReadout, \operatorname{scan}\left(L\right), x\right)\right) \leq \operatorname{length}\left(\operatorname{runPassiveProtocol}\left(equalityReadout, T, x\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/EqualityQueryScheduleNormalForm.equality_protocol_schedule_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction follows the original tree's negative branch. A center in the candidate set is placed first and removed from the remaining candidates; a center outside the set is discarded. At most one remaining candidate requires no query. The resulting list is distinct and exhaustive, and its stopping count is bounded separately at every target. Consequently every nonnegative weighted sum of stopping counts also weakly decreases.

## References

- Truth anchor: `D5/S3/Observer/Budget/EqualityQueryScheduleNormalForm.equality_protocol_schedule_normal_form`
- Truth anchor: `D5/S3/Observer/Budget/EqualityQueryScheduleNormalForm.scan_identifies_with_exact_depth`
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound](../../ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.md)
