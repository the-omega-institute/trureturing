# Cycle-clique unions and the prime optimum

## Abstract

Cycle-clique unions and their prime-order regular induced subgraphs define the extremal problem of Dyson and McKay.

**Definition 1.1 (Vertices indexed by components and bags).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.Vert`

*Formalization.* `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.Vert` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

For a finite list of pairs (r,s), a vertex consists of a component index, a cycle position from zero through r-1, and a clique position from zero through s-1. Thus the component with parameters (r,s) has rs vertices.

**Definition 1.2 (Equal or adjacent cycle positions).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.CycleClose`

*Formalization.* `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.CycleClose` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

Two positions a and b are close on the cycle of length r when a = b, when a+1 is congruent to b modulo r, or when b+1 is congruent to a modulo r.

**Definition 1.3 (The union of cycle-clique products).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.unionGraph`

*Formalization.* `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.unionGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

For each component (r,s), replace every vertex of C_r by a clique K_s and join all vertices in consecutive bags. Distinct vertices are adjacent precisely when they belong to the same component and their cycle positions are equal or adjacent. Different components have no edges between them. In particular, C_3[K_s] is K_{3s}.

**Definition 1.4 (A regular induced subgraph of prescribed order).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.HasRegularInduced`

*Formalization.* `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.HasRegularInduced` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

A union has a regular induced subgraph of order p when there is a vertex set of cardinality p and a nonnegative integer d such that every selected vertex has exactly d neighbours among the selected vertices. The selected subgraph may be disconnected, and degree zero is permitted.

**Definition 1.5 (The component parameter range).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.Admissible`

*Formalization.* `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

Every component has cycle length r at least three and clique size s at least one. A finite list satisfying these inequalities specifies the class of disjoint unions of products C_r[K_s]. The empty list is included.

**Definition 1.6 (The total number of vertices).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.order`

*Formalization.* `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.order` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

The order of a union is the sum of rs over all component pairs (r,s), counting repeated pairs with their multiplicities.

**Definition 1.7 (The order of the prime constructions).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.bound`

*Formalization.* `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.bound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

The extremal order is 9(p-1)^2/8 when p is congruent to one or five modulo twelve, (p-1)(9p-7)/8 when p is congruent to seven modulo twelve, and (p-1)(9p-11)/8 otherwise. Division is integer division. For primes p at least thirteen, the remaining residue is eleven and every displayed quotient is an integer.

**Definition 1.8 (The prime optimality assertion).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.claim`

*Formalization.* `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

For every prime p at least thirteen, every finite union of products C_r[K_s] with r at least three and s at least one that has no regular induced subgraph on exactly p vertices has order at most the stated bound. For each such p, a union in this class has exactly that order and still has no regular induced subgraph on p vertices.

## References

- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.Admissible`
- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.CycleClose`
- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.HasRegularInduced`
- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.Vert`
- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.bound`
- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.order`
- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.unionGraph`
