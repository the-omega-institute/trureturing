# The uniform undirected completion law

## Abstract

Uniform transport from actual oriented lifts to completed undirected cycle graphs.

**Theorem 1.1 (Uniformity on labelled undirected cycle completions).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/UndirectedCycleCompletionLaw.uniform_undirected_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/UndirectedCycleCompletionLaw.uniform_undirected_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Catherine Greenhill; Svante Janson; Jeong Han Kim; Nicholas C. Wormald (2002). *Permutation pseudographs and contiguity*. DOI: [10.1017/S0963548301005065](https://doi.org/10.1017/S0963548301005065).

*Commentary.*

Let F be a simple graph on a finite labelled vertex type with at least three vertices. Assume that at least one connected two-regular simple graph on the same type contains F. An actual lift consists of a full-cycle successor permutation and a direction for each edge of F consistent with that permutation. The shadow sends each lift to the graph consisting of the underlying undirected cycle edges.

There is a uniform probability mass on the lifts and a uniform probability mass on the completed graphs. Pushing the former along the shadow gives the latter. Each mass assigns the reciprocal of its own finite carrier cardinality to each point.

A connected degree-two graph admits a cyclic labelling. Starting with a chosen outgoing direction, agreement of successor permutations propagates along the cycle. The possible permutations over the graph are the forward cycle and its inverse. Each forces the direction of every prescribed edge. Thus every graph has exactly two lifts, and summing the uniform point mass over a fiber gives uniform transport.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/UndirectedCycleCompletionLaw.uniform_undirected_completion`
- Dependency: [D5/S0/Diagonal/Probability/EquivariantEscape](../../../../S0/Diagonal/Probability/EquivariantEscape.md)
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/General](../Brooks/General.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](../../PerfectMatchings/FiniteBandSwitch.md)
