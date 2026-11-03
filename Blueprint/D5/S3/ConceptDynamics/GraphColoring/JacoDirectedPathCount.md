# Directed paths and their cardinality

## Abstract

Actual shortest directed paths in the finite Jaco truncations.

**Definition 1.1 (The source directed graph).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.directed`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.directed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertices are the positive natural labels. There is exactly one arrow from a to b when a < b and b is at most jacoRight a, and no arrow otherwise. The imported endpoint_recurrence identifies jacoRight with twice the label minus the number of earlier positive endpoints reaching it. Thus these are the original directed arcs, with no symmetrization.

**Definition 1.2 (Paths in an induced truncation).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.TruncatedPath`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.TruncatedPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TruncatedPath r a b consists of actual Quiver.Path objects from a to b whose entire vertex list lies at labels at most r. This is the induced truncation on labels 1 through r: every edge is an original directed edge and every intermediate vertex remains in the truncation. Path length counts edges; the path of length zero at label one is included.

**Definition 1.3 (The actual shortest paths).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.Shortest`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.Shortest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Shortest n is the subtype of TruncatedPath n 1 n with edge length no larger than every other such path. Distinctness is equality of directed edge sequences. There is at most one arrow per pair of labels, so this agrees with distinct vertex sequences.

**Definition 1.4 (Minimum-path cardinality).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.psi`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive natural n, psi n is Nat.card of Shortest n; psi zero is only an unused extension. No recurrence defines this count. The theorem below proves finiteness and positivity rather than assuming either property of Nat.card.

**Definition 1.5 (Infinite directed outdegree).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.outdegree`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.outdegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

outdegree n is jacoRight n minus n. The imported endpoint_eq_beatty identifies it with beattyOut n. It counts the full outgoing interval in the infinite graph, even when a shortest path is counted in its own finite truncation.

**Definition 1.6 (The original all-index question).**

$$\forall k \in \mathrm{Nat},\; (7 \le k) \Rightarrow (\forall i \in \mathrm{Nat},\; ((\operatorname{fib}\left(i\right) < k) \land (k \le \operatorname{fib}\left(i + 1\right))) \Rightarrow (((\operatorname{outdegree}\left(k - 1\right) \ne \operatorname{outdegree}\left(k\right)) \land (\operatorname{outdegree}\left(k\right) \ne \operatorname{outdegree}\left(k + 1\right))) \Leftrightarrow ((\operatorname{psi}\left(k - 1\right) \ne \operatorname{psi}\left(k\right)) \land (\operatorname{psi}\left(k\right) \ne \operatorname{psi}\left(k + 1\right)))))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.claim` (`✓ std3`).

*Citation.* Johan Kok, Paul Fisher, Bettina Wilkens, Mokhwetha Mabula, Vivian Mukungunugwa (2014). *Characteristics of Jaco Graphs, J_infinity(a), a in N*. URL: <https://arxiv.org/abs/1404.1714v1>.

*Commentary.*

This is Proposition 4.4 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, Characteristics of Jaco Graphs, arXiv:1404.1714v1, Section 4. Both chains mean the conjunction of the two adjacent inequalities. Every k at least seven and every Fibonacci bracket index remain quantified. The result below establishes this complete equivalence from actual directed path cardinalities. The original Proposition 4.3 converse is not used.

**Theorem 1.7 (Finite positive cardinality and truncation invariance).**

$$\forall n \in \mathrm{PNat},\; (\operatorname{Finite}\left(\operatorname{Shortest}\left(n\right)\right)) \land ((\operatorname{Nonempty}\left(\operatorname{Shortest}\left(n\right)\right)) \land ((0 < \operatorname{psi}\left(\operatorname{val}\left(n\right)\right)) \land (\forall r \in \mathrm{Nat},\; (\operatorname{val}\left(n\right) \le r) \Rightarrow (\exists e \in \operatorname{Equiv}\left(\operatorname{TruncatedPath}\left(r, 1, n\right), \operatorname{TruncatedPath}\left(\operatorname{val}\left(n\right), 1, n\right)\right),\; \forall p \in \operatorname{TruncatedPath}\left(r, 1, n\right),\; \operatorname{length}\left(\operatorname{underlying}\left(\operatorname{e}\left(p\right)\right)\right) = \operatorname{length}\left(\operatorname{underlying}\left(p\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.path_count_foundations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An induction on the terminal positive label decomposes each nonempty directed path into its last predecessor and its prefix. Every predecessor has strictly smaller label, and the outgoing edge is unique, giving a finite set of paths. Consecutive forward arcs supply a path to each positive label; the least attained edge length therefore exists. Every vertex of a forward path is between its endpoints. Erasing or inserting the truncation proof gives inverse maps on paths in any truncation ending beyond the target, and preserves edge length exactly. These arguments concern actual path objects and their cardinality, without a recurrence replacement for psi.

**Theorem 1.8 (The exact Fibonacci distance threshold).**

$$\forall l \in \mathrm{Nat},\; \forall n \in \mathrm{PNat},\; ((\exists p \in \operatorname{TruncatedPath}\left(\operatorname{val}\left(n\right), 1, n\right),\; \operatorname{length}\left(\operatorname{underlying}\left(p\right)\right) \le l) \Leftrightarrow (\operatorname{val}\left(n\right) \le \operatorname{fib}\left(l + 2\right))) \land (\forall p \in \operatorname{Shortest}\left(n\right),\; (\operatorname{length}\left(\operatorname{underlying}\left(\operatorname{underlying}\left(p\right)\right)\right) \le l) \Leftrightarrow (\operatorname{val}\left(n\right) \le \operatorname{fib}\left(l + 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.fibonacci_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative edge budget l and every positive target n, a path in the target's own truncation has at most l edges exactly when n is at most Fibonacci(l+2). Every shortest path has the same threshold. Strict increase of the original endpoint sequence and beatty_threshold give beattyOut(jacoRight m)=m. Induction then gives jacoRight(Fibonacci(l+2))=Fibonacci(l+3). Another induction proves that the reachable set at edge budget l is precisely that positive prefix: one more edge cannot pass the endpoint of the prefix, and every new label in the next prefix is reached directly from the previous endpoint. No compressed distance claim from the source is assumed.

**Theorem 1.9 (Complete original Proposition 4.4).**

$$\forall k \in \mathrm{Nat},\; (7 \le k) \Rightarrow (\forall i \in \mathrm{Nat},\; ((\operatorname{fib}\left(i\right) < k) \land (k \le \operatorname{fib}\left(i + 1\right))) \Rightarrow (((\operatorname{outdegree}\left(k - 1\right) \ne \operatorname{outdegree}\left(k\right)) \land (\operatorname{outdegree}\left(k\right) \ne \operatorname{outdegree}\left(k + 1\right))) \Leftrightarrow ((\operatorname{psi}\left(k - 1\right) \ne \operatorname{psi}\left(k\right)) \land (\operatorname{psi}\left(k\right) \ne \operatorname{psi}\left(k + 1\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/kok-jaco-directed-path-count` (proved) by `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kok-jaco-directed-path-count","declaration_gid":"D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok, Paul Fisher, Bettina Wilkens, Mokhwetha Mabula, Vivian Mukungunugwa (2014). *Characteristics of Jaco Graphs, J_infinity(a), a in N*. URL: <https://arxiv.org/abs/1404.1714v1>.

*Commentary.*

For every j at least three and every target n with Fibonacci(j) < n <= Fibonacci(j+1), removing the final edge of an actual shortest directed path gives precisely a predecessor h in the interval [beattyOut n, Fibonacci(j)] together with an actual shortest path to h. A shorter prefix would shorten the original path. The distance threshold excludes later predecessors, while the endpoint threshold excludes earlier ones. Appending the unique final edge is the inverse, including both proof-carrying truncations. The resulting dependent-sum equivalence gives psi n as the sum of the positive actual cardinalities psi h over that interval.

The endpoint threshold and consecutive endpoint growth show that beattyOut(n+1) is either beattyOut n or beattyOut n plus one. Within one Fibonacci distance layer the suffix sums therefore agree exactly in the first case. In the second case the lower summand psi(beattyOut n), which is positive by the cardinality foundations, is removed, so the counts differ strictly.

The endpoint identities also give beattyOut(Fibonacci(t+1))=Fibonacci(t) for every t at least two. The shortest path to label two is unique. The singleton suffix at successive Fibonacci endpoints then gives psi(Fibonacci(t))=1 for every t at least three. At every boundary Fibonacci(t), t at least five, the next lower predecessor is Fibonacci(t-1)+1. Its suffix contains at least two labels, and each has positive actual shortest-path cardinality. Consequently psi(Fibonacci(t)+1) is at least two, while both the infinite outdegree and the path count differ across the boundary.

Every label n at least five lies in a Fibonacci bracket. Combining the within-layer and boundary cases gives outdegree n = outdegree(n+1) exactly when psi n = psi(n+1). Applying this at k-1 and k, negating the two equality equivalences and conjoining proves the stated iff for every k at least seven. The original universal Fibonacci-bracket index is retained; no bracket, upper cutoff, converse from Proposition 4.3 or unproved reachability premise is added.

The source is arXiv:1404.1714v1, Section 4, with its original forward directed arc convention and each target counted in its own induced truncation. This result is the mathematical event stated there. It does not certify worldwide literature coverage, priority or a physical interpretation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.Shortest`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.TruncatedPath`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.claim`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.directed`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.fibonacci_distance`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.outdegree`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.path_count_foundations`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.psi`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty](JacoEndpointBeatty.md)
