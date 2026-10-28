# Every positive order and the full successive ratio

## Abstract

Every positive order and the full successive ratio

**Definition 1.1 (Actual finite simple graph).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/EveryOrder.FiniteGraph`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/EveryOrder.FiniteGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

An object consists of an actual vertex type with a Fintype enumeration, decidable equality, a SimpleGraph on that type and decidable adjacency. SimpleGraph imposes symmetry and excludes loops; there are no weights. The empty vertex type is permitted by the structure.

**Definition 1.2 (The full minimal-fort count).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/EveryOrder.count`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/EveryOrder.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every FiniteGraph A, count(A) is the cardinality of minimalForts(A.graph). It filters every actual vertex subset by the reused nonempty fort predicate and inclusion-minimality over all fort subsets. It counts neither equivalence classes nor a chosen subclass.

**Theorem 1.3 (Every positive order and the full successive ratio).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/EveryOrder.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/EveryOrder.result` (`✓ std3`). ∎

*Resolves.* `Problems/becker-cameron-hanely-ong-previte-conjecture-31` (proved) by `D5/S3/Combinatorics/MinimalForts/EveryOrder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"becker-cameron-hanely-ong-previte-conjecture-31","declaration_gid":"D5/S3/Combinatorics/MinimalForts/EveryOrder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

There exists a sequence of actual finite simple undirected loopless unweighted graphs indexed by every natural n. For every positive n the vertex count is exactly n, the graph is connected, and its entire minimal-fort count A(n) is positive. Along the entire sequence n tending to infinity, A(n)/(3/2)^n tends to one and A(n+1)/A(n) tends to three halves. The real cube root of three is strictly less than three halves, which is strictly less than two. The first two positive orders use complete graphs. For n at least three, write n-3=6k+r with 0<=r<6 and use the mixed graph from the feasible sequence for residue r. Simultaneous convergence over all six residues gives the full limit, rather than only a block subsequence or a limit superior. The successive-ratio limit follows from the normalization and positivity. This proves the mathematical existence and ratio assertion of arXiv:2404.05963v1, Section 6, Conjecture 31, with the additional every-order and connectedness requirements. The source sentence itself does not separately impose vertex count n at index n.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/EveryOrder.FiniteGraph`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/EveryOrder.count`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/EveryOrder.result`
- Dependency: [D5/S3/Combinatorics/MinimalForts/CountAsymptotics](CountAsymptotics.md)
