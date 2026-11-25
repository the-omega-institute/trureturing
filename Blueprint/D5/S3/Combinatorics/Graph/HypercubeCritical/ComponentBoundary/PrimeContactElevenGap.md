# Seven-cycle coordinate rigidity and the eleven-column exclusion

## Abstract

Seven-cycle coordinate rigidity and the eleven-column exclusion

**Theorem 1.1 (A seven-cycle with no triangle on a cycle edge has at most one chord).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactElevenGap.seven_cycle_chord_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactElevenGap.seven_cycle_chord_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Label each edge by the two changed axes. Consecutive labels are disjoint, and each used axis occurs exactly twice by closure of the seven-cycle. A distance-three chord requires equality of the first and third labels. Two such equal pairs contradict the allowed label pattern or give a triangle containing a cycle edge.

**Theorem 1.2 (The two-contact cube cannot have eleven columns).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactElevenGap.card_ne_eleven_of_twoContact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactElevenGap.card_ne_eleven_of_twoContact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted order counts and triangle incidence leave two possible graphs after triangle edges are removed. A four-cycle needs twelve distinct columns because its triangle attachments cannot overlap. A seven-cycle requires at least two chords, contradicting coordinate rigidity.

Together with the preceding cardinality gap this gives nine or at least twelve columns in the two-contact branch of Hong, Wu and Xia's open problem. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactElevenGap.card_ne_eleven_of_twoContact`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactElevenGap.seven_cycle_chord_unique`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap](PrimeContactCardinalityGap.md)
