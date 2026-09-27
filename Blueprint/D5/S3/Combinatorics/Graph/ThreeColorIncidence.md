# Three-color incidence and population reduction

## Abstract

Exact mixed-incidence counts reduce the reciprocal potential of a properly three-colored graph to two expressions in its unrestricted ordinary and mixed populations.

**Definition 1.1 (Finite neighborhoods).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.neighborhood`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorIncidence.neighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The neighborhood of a vertex is the set of vertices in the specified finite set adjacent to it. The ambient type need not be finite.

**Definition 1.2 (Mixed vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.Mixed`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorIncidence.Mixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex is mixed if two of its neighbors have different colors. For a proper coloring with three colors these are the two colors different from the vertex color.

**Definition 1.3 (Ordinary populations).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.ordinary`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorIncidence.ordinary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary population U(i,j) consists of the nonisolated vertices of color i all of whose neighbors have color j. A nonisolated vertex is either mixed or lies in exactly one ordinary population.

**Definition 1.4 (Mixed populations by color).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.mixedColor`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorIncidence.mixedColor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mixed population of color i is the set of mixed vertices having that color. Its cardinality is denoted by m(i).

**Definition 1.5 (Reciprocal potential).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.potential`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorIncidence.potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The potential is the sum of the three reciprocals of color-class sizes plus one, together with one half the sum of the reciprocals of degrees plus one. All terms are rational, and empty classes contribute one.

**Definition 1.6 (Available mixed incidences).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.incoming`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorIncidence.incoming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the ordinary population U(i,j), the available mixed incidences are m(j) when U(j,i) is nonempty and the natural-number difference m(j)-m(i) otherwise. The latter case follows from equality of the two counts of edges between the colors.

**Definition 1.7 (Attachment-charge expression).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.chargedLower`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorIncidence.chargedLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This expression includes the class reciprocals, one sixth of the total mixed population, and one half the sum over distinct i,j of x(i,j)/(x(j,i)+1) minus m(j)/((x(j,i)+1)(x(j,i)+2)). Each mixed incidence is charged the loss caused by a first attachment.

**Definition 1.8 (Cauchy expression).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.quadraticLower`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorIncidence.quadraticLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This expression includes the class reciprocals, one sixth of the total mixed population, and one half the sum of x(i,j) squared divided by x(i,j)(x(j,i)+1) plus the available mixed incidences. Empty ordinary populations contribute zero.

**Theorem 1.9 (Exact balance and incidence bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.incidence_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ThreeColorIncidence.incidence_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the adjacency relation is symmetric on the finite vertex set, the three-coloring is proper, and every mixed vertex has degree two. For distinct colors i,j, let D(i,j) be the sum of degrees in U(i,j). Then D(i,j)+m(i)=D(j,i)+m(j), and D(i,j) is at most x(i,j)x(j,i)+m(j). In addition, the total number of mixed neighbors counted from U(i,j) is at most m(j), and each individual degree is at most x(j,i) plus its number of mixed neighbors. Every mixed vertex has exactly one neighbor in each of the other two colors. Counting the same edges in both directions gives the balance identity.

**Theorem 1.10 (Reduction to actual populations).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.population_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ThreeColorIncidence.population_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the preceding graph assumptions, also suppose every vertex is nonisolated. Set m(i) to the actual mixed population and x(i,j) to the actual ordinary population. Then x(i,i)=0, and x(i,j)=0 implies m(j)+x(j,i) is at most m(i). Both the attachment-charge expression and the Cauchy expression are lower bounds for the potential. The class sizes and the mixed contribution follow from the complete vertex partition. The ordinary estimates use, respectively, the discrete decrease of the reciprocal under attachments and Cauchy inequality with the actual degree sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.Mixed`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.chargedLower`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.incidence_reduction`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.incoming`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.mixedColor`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.neighborhood`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.ordinary`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.population_reduction`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorIncidence.quadraticLower`
