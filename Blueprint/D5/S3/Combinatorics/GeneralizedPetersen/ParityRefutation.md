# The Triangular Prism Refutes Pandey's Parity Conjecture

## Abstract

A Lean formalization of the earlier public refutation: the triangular prism has real-rooted independence polynomial 1+6X+6X^2 and odd step size.

Conjecture 4.1 (Parity Conjecture), page 4 of arXiv:2601.03293v1, states: "For all integers n ≥ 2k+1, the independence polynomial I(GP(n,k),x) has only real roots if and only if k is even." Definition 2.1 supplies n >= 3 and 1 <= k < n/2. The separate computational range 20 <= n <= 30 does not restrict that conjecture.

**Definition 1.1 (Generalized Petersen graphs).**

$$\operatorname{gp}\left(n, k\right) = \operatorname{fromRel}\left(\operatorname{R}\left(n, k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.gp` (`✓ std3`).

*Citation.* Rohan Pandey (2026). *Parity-Dependent Real-Rootedness in Independence Polynomials of Generalized Petersen Graphs*. URL: <https://arxiv.org/abs/2601.03293v1>.

*Commentary.*

The vertex type is Bool x Fin n. The false layer represents u and the true layer represents v. The relation R consists of u_i to u_(i+1), v_i to v_(i+k), and u_i to v_i, with indices modulo n. The fromRel construction makes these edges undirected and removes loops. The parameter domain below is exactly the source graph domain.

**Definition 1.2 (The full parity assertion).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (3 \le n) \Rightarrow ((1 \le k) \Rightarrow ((2\cdot k < n) \Rightarrow ((\forall z \in \mathrm{Complex},\; (\operatorname{I}\left(\operatorname{gp}\left(n, k\right), z\right) = 0) \Rightarrow (\operatorname{im}\left(z\right) = 0)) \Leftrightarrow (\operatorname{Even}\left(k\right))))))$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.claim` (`✓ std3`).

*Citation.* Rohan Pandey (2026). *Parity-Dependent Real-Rootedness in Independence Polynomials of Generalized Petersen Graphs*. URL: <https://arxiv.org/abs/2601.03293v1>.

*Commentary.*

Here I(G,z) denotes complex evaluation, by the integer cast ring homomorphism, of IndependentPartitionDeletion.independencePolynomial on all vertices of G. That polynomial is the sum of X to the cardinality of S over all actual independent vertex sets S. Real-rootedness means that every complex zero has imaginary part zero. The strict natural-number inequality 2k < n is equivalent to n >= 2k+1 and avoids truncated division.

**Theorem 1.3 (An odd-step real-rooted graph).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/pandey-parity-conjecture-refutation` (refuted) by `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pandey-parity-conjecture-refutation","declaration_gid":"D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.result","resolution_kind":"refuted"} -->

*Citation.* demonstrandum-research/artifacts (repository publisher) (2026). *Refutation of the Parity Conjecture for Independence Polynomials of Generalized Petersen Graphs (arXiv:2601.03293, Conjecture 4.1)*. URL: <https://github.com/demonstrandum-research/artifacts/blob/94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3/problems/p2-factory/kills/pandey-parity/WRITEUP.md>.

*Commentary.*

For n=3 and k=1 the graph is the triangular prism. Its independent sets are the empty set, six singletons, and six pairs u_i,v_j with i different from j. There are no larger independent sets. Thus its actual polynomial evaluates to 1+6z+6z^2. If z=a+bi is a zero, its imaginary part gives 6b(1+2a)=0. If b is nonzero then a=-1/2, and the real part gives -1/2-6b^2=0, contradicting nonnegativity of b^2. Every zero is real, but k=1 is not even, contradicting the forward direction of the asserted biconditional.

The earlier public refutation in demonstrandum-research/artifacts, commit 94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3, problems/p2-factory/kills/pandey-parity/WRITEUP.md, already gives this exact counterexample. Its provider commit timestamp is 2026-06-13T01:23:03Z; its internal June 11 date is unverified. The separate prior-refutation Library note pins that source. That note also explains the published map u_j to v'_(3j mod 7), v_j to u'_(3j mod 7), an isomorphism GP(7,2) to GP(7,3). Equal independence polynomials and opposite step parity contradict the full biconditional without computing roots. No external enumeration, Sturm, checker, or audit claims are adopted here.

This Lean theorem formalizes the already published refutation; it is not a newly resolved open problem. The graph and conjecture are due to Pandey; the refutation is due to the distinct earlier public note cited above.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.gp`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.result`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](../../StatisticalMechanics/HardCore/IndependentPartitionDeletion.md)
