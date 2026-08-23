# Negative-Prefix Trident Preservation

## Abstract

Lucas-gap core classifications survive the initial-value shifts that lift a core to the full negative-prefix occurrence set.

**Theorem 1.1 (Lucas-gap sequences translate with their initial value).**

$$\forall j, n,\ \operatorname{v}\left(a, b, r, n\right)+j=\operatorname{v}\left(a, b, r+j, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation.v_translate_initial_value_proved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding a natural offset to every value of any of the three Lucas-gap families is identical to adding that offset to the initial value. The proof follows the common second-order recurrence.

**Theorem 1.2 (The three shifted core arms are pairwise disjoint).**

$$\forall i,j\in\{0,1,2\},\ i \neq j \Rightarrow \operatorname{Disjoint}\left(\operatorname{Range}\left(\operatorname{v}\left(r+i\right)\right), \operatorname{Range}\left(\operatorname{v}\left(r+j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation.three_arms_pairwise_disjoint_proved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prefix headed by zero, unique lifting of each occurrence back to a core point and one of the offsets zero, one, or two forces distinct offset arms to be disjoint.

**Theorem 1.3 (The Lucas-gap classification lifts from the core to all occurrences).**

$$w_0=1\Rightarrow \operatorname{Occ}\left(w\right)=\operatorname{Range}\left(\operatorname{v}\left(r\right)\right),\\{}w_0=0\Rightarrow \operatorname{Occ}\left(w\right)=\operatorname{union}_{j=0}^2 \operatorname{Range}\left(\operatorname{v}\left(r+j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation.occurrenceSet_lucas_gap_classification_proved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prefix headed by one has a single occurrence arm. A prefix headed by zero has exactly the union of the three translated arms, and the preceding disjointness theorem keeps that union pairwise disjoint.

## References

- Truth anchor: `D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation.occurrenceSet_lucas_gap_classification_proved`
- Truth anchor: `D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation.three_arms_pairwise_disjoint_proved`
- Truth anchor: `D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation.v_translate_initial_value_proved`
