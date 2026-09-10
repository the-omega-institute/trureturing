# Version B twelve-pile refutation

## Abstract

A kernel-checked losing position contradicts an explicit threshold-and-parity next-player prediction for Version B.

**Definition 1.1 (Position).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Position`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplicities represent the closed subgame with pile sizes one through six.

**Definition 1.2 (pileCount).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.pileCount`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.pileCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six multiplicities sum to the number of nonempty piles.

**Definition 1.3 (tokens).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.tokens`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.tokens` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Weighting each multiplicity by its pile size gives the total token count.

**Definition 1.4 (singleSuccessors).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.singleSuccessors`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.singleSuccessors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A single-pile move removes one token from a present pile and deletes a pile when it reaches zero.

**Definition 1.5 (allSuccessor).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.allSuccessor`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.allSuccessor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A simultaneous removal shifts the size counts down and deletes size-one piles.

**Definition 1.6 (SingleMove).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.SingleMove`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.SingleMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership in the single-pile successor list defines the first move relation.

**Definition 1.7 (AllMove).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.AllMove`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.AllMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The simultaneous move requires a nonempty starting position.

**Definition 1.8 (Move).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Move`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Move` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A legal move is a single-pile removal or a simultaneous removal.

**Theorem 1.9 (move decreases).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.move_decreases`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.move_decreases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each legal move strictly decreases total tokens.

**Definition 1.10 (Losing).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Losing`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Losing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Well-founded recursion declares a position losing exactly when every legal successor is not losing.

**Theorem 1.11 (losing iff).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.losing_iff`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.losing_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursive definition unfolds to the normal-play losing condition.

**Theorem 1.12 (empty losing).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.empty_losing`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.empty_losing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The player to move loses in the empty position.

**Theorem 1.13 (losing iff certificate).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.losing_iff_certificate`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.losing_iff_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on tokens identifies the checked bit certificate with Losing for every position with at most twelve piles.

**Definition 1.14 (target).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target consists of six piles of five and six piles of six.

**Theorem 1.15 (target losing).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target_losing`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target_losing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target is a previous-player win, so the player to move loses.

**Definition 1.16 (Criterion).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Criterion`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Criterion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every present pile exceeds the ceiling of one third of the pile count, and the count of odd piles is even.

**Theorem 1.17 (target criterion).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target_criterion`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target has twelve piles, each exceeding four tokens, and six odd piles.

**Definition 1.18 (PredictedClassification).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.PredictedClassification`

*Formalization.* `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.PredictedClassification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit prediction asserts that every nonempty position satisfying Criterion is not losing.

**Theorem 1.19 (predicted classification refuted).**

Lean statement: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.predicted_classification_refuted`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.predicted_classification_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The losing target satisfies Criterion and contradicts the explicit prediction.

## References

- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.AllMove`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Criterion`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Losing`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Move`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.Position`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.PredictedClassification`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.SingleMove`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.allSuccessor`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.empty_losing`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.losing_iff`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.losing_iff_certificate`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.move_decreases`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.pileCount`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.predicted_classification_refuted`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.singleSuccessors`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target_criterion`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.target_losing`
- Truth anchor: `D5/S0/Certificates/Games/VersionBTwelvePileRefutation.tokens`
