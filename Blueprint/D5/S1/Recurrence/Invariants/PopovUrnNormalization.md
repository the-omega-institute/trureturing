# First-use normalization of urn histories

## Abstract

First-use words classify chronological urn histories under arbitrary relabelings.

A raw history assigns each of t chronological marble positions a pair consisting of an urn label in Fin(A) and a slot label in Fin(m). A repeated slot requires its own urn to be full. A move to a fresh urn requires all started urns to be full. An orbit allows an arbitrary urn permutation and a slot permutation for each original urn. All permutations fix every marble position. Used(x) is the finite set of distinct values of x.

**Definition 1.1 (The chronological orbit quotient).**

$$\forall A \in \mathbb{N}, \forall m \in \mathbb{N}, \forall t \in \mathbb{N}, 0 < m \land t \le A \implies \operatorname{Arrangements}\left(A, m, t\right) \sim \operatorname{Word}\left(m, t\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/PopovUrnNormalization.quotientEquivWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Arrangements is the quotient of legal raw histories by the indicated orbit relation. A legal word starts with no ranks. With p ranks in use, it may introduce rank p or reuse a rank strictly below m times the integer quotient of p by m. Replay takes quotient and remainder by m at each marble position.

**Theorem 1.2 (Equality of words is equality of raw orbits).**

$$\forall A \in \mathbb{N}, \forall m \in \mathbb{N}, \forall t \in \mathbb{N}, 0 < m \land t \le A \implies \forall x \in \operatorname{Raw}\left(A, m, t\right), \forall y \in \operatorname{Raw}\left(A, m, t\right), \operatorname{normalize}\left(x\right) = \operatorname{normalize}\left(y\right) \iff \operatorname{Orbit}\left(x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PopovUrnNormalization.normalize_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prefix induction aligns each new address with its first-use rank. When the next address is fresh, the required permutation can be adjusted on unused labels. The same-compartment relation determines each legal word uniquely.

**Theorem 1.3 (Normalizing a replay recovers the word).**

$$\forall A \in \mathbb{N}, \forall m \in \mathbb{N}, \forall t \in \mathbb{N}, 0 < m \land t \le A \implies \forall w \in \operatorname{Word}\left(m, t\right), \operatorname{normalize}\left(\operatorname{replay}\left(w\right)\right) = w$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PopovUrnNormalization.normalize_replay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The replay is legal, including for the empty word. Replaying a normalization lies in the original raw orbit.

**Theorem 1.4 (Actual occupied ranks at every prefix).**

$$\forall A \in \mathbb{N}, \forall m \in \mathbb{N}, \forall t \in \mathbb{N}, 0 < m \land t \le A \implies \forall x \in \operatorname{Raw}\left(A, m, t\right), \forall s \in \mathbb{N}, s \le t \implies \operatorname{used}\left(\operatorname{prefix}\left(\operatorname{normalize}\left(x\right), s\right)\right) = \operatorname{range}\left(\operatorname{card}\left(\operatorname{used}\left(\operatorname{prefix}\left(x, s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PopovUrnNormalization.normalized_prefix_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here range(p) is the half-open interval from zero to p. The cardinality on the right counts actual distinct raw pairs in the prefix. Rank within an urn starts at slot zero. The rank at first use of a compartment is the actual number of distinct pairs in the preceding prefix.

Restricting the quotient equivalence to an occupied-count fiber preserves that count. Any two finite ambient urn sets with at least t labels give equivalent fibers by passing through the same words.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/PopovUrnNormalization.normalize_eq_iff`
- Truth anchor: `D5/S1/Recurrence/Invariants/PopovUrnNormalization.normalize_replay`
- Truth anchor: `D5/S1/Recurrence/Invariants/PopovUrnNormalization.normalized_prefix_interval`
- Truth anchor: `D5/S1/Recurrence/Invariants/PopovUrnNormalization.quotientEquivWord`
