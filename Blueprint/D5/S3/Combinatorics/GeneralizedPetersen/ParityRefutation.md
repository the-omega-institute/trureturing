# The Triangular Prism Refutes Pandey's Parity Conjecture

## Abstract

The triangular prism has real-rooted independence polynomial 1+6X+6X^2 and odd step size.

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

*Source.* Repository-derived.

*Acknowledgement.* Rohan Pandey (2026). *Parity-Dependent Real-Rootedness in Independence Polynomials of Generalized Petersen Graphs*. URL: <https://arxiv.org/abs/2601.03293v1>.

*Commentary.*

For n=3 and k=1 the graph is the triangular prism. Its independent sets are the empty set, six singletons, and six pairs u_i,v_j with i different from j. There are no larger independent sets. Thus its actual polynomial evaluates to 1+6z+6z^2. If z=a+bi is a zero, its imaginary part gives 6b(1+2a)=0. If b is nonzero then a=-1/2, and the real part gives -1/2-6b^2=0, contradicting nonnegativity of b^2. Every zero is real, but k=1 is not even, contradicting the forward direction of the asserted biconditional.

The prism and its real-rooted polynomial are classical ingredients. The prism is claw-free, so its real-rootedness also follows from the Chudnovsky-Seymour theorem cited by Pandey. The argument here uses direct finite counting and elementary arithmetic; it claims no new graph family or root-location technique. It addresses the literal later conjecture, without classifying other parameter pairs.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.gp`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.result`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](../../StatisticalMechanics/HardCore/IndependentPartitionDeletion.md)
