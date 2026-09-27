# A Colored-Path Determinant Counterexample

## Abstract

A seven-vertex colored path pair refutes Conjecture 5.3 on determinant equality.

**Definition 1.1 (Labelled colored paths).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall m \in \mathrm{Nat},\; \operatorname{ColoredPath}\left(V, E, m\right) = \{vertexColor: \operatorname{Fin}\left(m\right) \to V; edgeColor: \operatorname{Fin}\left(m - 1\right) \to E\}$$

*Formalization.* `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.ColoredPath` (`✓ std3`).

*Citation.* Hannah Göbel, Pratik Misra (2025). *Linear relations of colored Gaussian cycles*. DOI: [10.48550/arXiv.2506.23936](https://doi.org/10.48550/arXiv.2506.23936). URL: <https://arxiv.org/abs/2506.23936v1>.

*Commentary.*

A colored path on m vertices has a vertex-color function Fin(m) to V and an edge-color function Fin(m-1) to E. The distinct types V and E keep the vertex- and edge-color sets disjoint. A zero-based vertex index i represents the one-based position i.val+1.

**Definition 1.2 (Generic concentration matrix).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall m \in \mathrm{Nat},\; \forall P \in \operatorname{ColoredPath}\left(V, E, m\right),\; \forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{entry}\left(\operatorname{concentration}\left(P\right), i, j\right) = \begin{cases}\operatorname{X}\left(\operatorname{inl}\left(\operatorname{vertexColor}\left(P, i\right)\right)\right) & i = j\\\operatorname{X}\left(\operatorname{inr}\left(\operatorname{edgeColor}\left(P, Fin.mk\left(\operatorname{val}\left(i\right)\right)\right)\right)\right) & \operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right)\\\operatorname{X}\left(\operatorname{inr}\left(\operatorname{edgeColor}\left(P, Fin.mk\left(\operatorname{val}\left(j\right)\right)\right)\right)\right) & \operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right)\\0 & \mathrm{otherwise}\end{cases}$$

*Formalization.* `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.concentration` (`✓ std3`).

*Citation.* Hannah Göbel, Pratik Misra (2025). *Linear relations of colored Gaussian cycles*. DOI: [10.48550/arXiv.2506.23936](https://doi.org/10.48550/arXiv.2506.23936). URL: <https://arxiv.org/abs/2506.23936v1>.

*Commentary.*

For a colored path P, concentration(P) is a matrix over the integer multivariable polynomial ring on V+E. Its diagonal entry (i,i) is X(inl(vertexColor(P,i))). Its adjacent entries (i,i+1) and (i+1,i) are X(inr(edgeColor(P,i))); every other entry is zero. Thus equal colors produce equal matrix entries exactly as in color constraints (1)-(3) on printed page 5. The coefficients are integers, and the coefficient embedding from integers into reals is injective, so polynomial equality here is the same formal identity as over the reals.

**Definition 1.3 (Path reflection).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall m \in \mathrm{Nat},\; \forall P \in \operatorname{ColoredPath}\left(V, E, m\right),\; (\forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{vertexColor}\left(\operatorname{reflect}\left(P\right), i\right) = \operatorname{vertexColor}\left(P, Fin.mk\left(m - 1 - \operatorname{val}\left(i\right)\right)\right)) \land (\forall i \in \operatorname{Fin}\left(m - 1\right),\; \operatorname{edgeColor}\left(\operatorname{reflect}\left(P\right), i\right) = \operatorname{edgeColor}\left(P, Fin.mk\left(m - 2 - \operatorname{val}\left(i\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.reflect` (`✓ std3`).

*Citation.* Hannah Göbel, Pratik Misra (2025). *Linear relations of colored Gaussian cycles*. DOI: [10.48550/arXiv.2506.23936](https://doi.org/10.48550/arXiv.2506.23936). URL: <https://arxiv.org/abs/2506.23936v1>.

*Commentary.*

Reflection preserves color labels while reversing positions. On zero-based indices it sends a vertex index i to m-1-i.val and an edge index i to m-2-i.val. In one-based positions these are r to m+1-r for vertices and r to m-r for edges.

**Definition 1.4 (Theorem 3.6 configuration).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall m \in \mathrm{Nat},\; \forall P \in \operatorname{ColoredPath}\left(V, E, m\right),\; \forall Q \in \operatorname{ColoredPath}\left(V, E, m\right),\; (\operatorname{Config36}\left(P, Q\right)) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(m - 1\right),\; \operatorname{edgeColor}\left(P, i\right) = \operatorname{edgeColor}\left(Q, i\right)) \land \left((\forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; ((\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 0) \land (\operatorname{mod}\left(\operatorname{val}\left(j\right), 2\right) = 0)) \Rightarrow ((\operatorname{vertexColor}\left(P, i\right) = \operatorname{vertexColor}\left(P, j\right)) \land (\operatorname{vertexColor}\left(Q, i\right) = \operatorname{vertexColor}\left(Q, j\right)))) \land \left((\forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; ((\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 1) \land (\operatorname{mod}\left(\operatorname{val}\left(j\right), 2\right) = 1)) \Rightarrow ((\operatorname{vertexColor}\left(P, i\right) = \operatorname{vertexColor}\left(P, j\right)) \land (\operatorname{vertexColor}\left(Q, i\right) = \operatorname{vertexColor}\left(Q, j\right)))) \land (\forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; ((\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 0) \land (\operatorname{mod}\left(\operatorname{val}\left(j\right), 2\right) = 1)) \Rightarrow ((\operatorname{vertexColor}\left(P, i\right) = \operatorname{vertexColor}\left(Q, j\right)) \land (\operatorname{vertexColor}\left(P, j\right) = \operatorname{vertexColor}\left(Q, i\right))))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.Config36` (`✓ std3`).

*Citation.* Hannah Göbel, Pratik Misra (2025). *Linear relations of colored Gaussian cycles*. DOI: [10.48550/arXiv.2506.23936](https://doi.org/10.48550/arXiv.2506.23936). URL: <https://arxiv.org/abs/2506.23936v1>.

*Commentary.*

Theorem 3.6 states the following clauses verbatim: “(1) lambda({p_i, p_{i+1}}) = lambda({q_i, q_{i+1}}) for every i in {1, 2, ..., m-1}, (2) lambda(p_1) = lambda(p_{2n+1}) and lambda(q_1) = lambda(q_{2n+1}) for every n in {1, 2, ..., m/2-1} (odd vertices have the same color), (3) lambda(p_2) = lambda(p_{2n}) and lambda(q_2) = lambda(q_{2n}) for every n in {1, 2, ..., m/2} (even vertices have the same color), (4) lambda(p_1) = lambda(q_2) and lambda(p_2) = lambda(q_1).” Config36 writes the monochromatic clauses symmetrically over all positions. Under those clauses, its two cross equalities are equivalent to clause (4). One-based odd position means val(i) mod 2 = 0; mod denotes natural-number remainder.

**Definition 1.5 (Theorem 3.8 configuration).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall m \in \mathrm{Nat},\; \forall P \in \operatorname{ColoredPath}\left(V, E, m\right),\; \forall Q \in \operatorname{ColoredPath}\left(V, E, m\right),\; (\operatorname{Config38}\left(P, Q\right)) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; ((\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 0) \land (\operatorname{mod}\left(\operatorname{val}\left(j\right), 2\right) = 0)) \Rightarrow ((\operatorname{vertexColor}\left(P, i\right) = \operatorname{vertexColor}\left(P, j\right)) \land \left((\operatorname{vertexColor}\left(P, i\right) = \operatorname{vertexColor}\left(Q, j\right)) \land (\operatorname{vertexColor}\left(Q, i\right) = \operatorname{vertexColor}\left(Q, j\right))\right))) \land \left((\forall i \in \operatorname{Fin}\left(m\right),\; (\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 1) \Rightarrow (\operatorname{vertexColor}\left(P, i\right) = \operatorname{vertexColor}\left(Q, i\right))) \land \left((\forall i \in \operatorname{Fin}\left(m - 1\right),\; \forall j \in \operatorname{Fin}\left(m - 1\right),\; ((\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 0) \land (\operatorname{mod}\left(\operatorname{val}\left(j\right), 2\right) = 1)) \Rightarrow (\operatorname{edgeColor}\left(P, i\right) = \operatorname{edgeColor}\left(Q, j\right))) \land (\forall i \in \operatorname{Fin}\left(m - 1\right),\; \forall j \in \operatorname{Fin}\left(m - 1\right),\; ((\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 0) \land (\operatorname{mod}\left(\operatorname{val}\left(j\right), 2\right) = 1)) \Rightarrow (\operatorname{edgeColor}\left(P, j\right) = \operatorname{edgeColor}\left(Q, i\right)))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.Config38` (`✓ std3`).

*Citation.* Hannah Göbel, Pratik Misra (2025). *Linear relations of colored Gaussian cycles*. DOI: [10.48550/arXiv.2506.23936](https://doi.org/10.48550/arXiv.2506.23936). URL: <https://arxiv.org/abs/2506.23936v1>.

*Commentary.*

Theorem 3.8 states the following clauses verbatim: “(1) lambda(p_1) = lambda(p_{2n+1}) = lambda(q_1) = lambda(q_{2n+1}) for every n in {1, 2, ..., (m-1)/2}, (2) lambda(p_{2n}) = lambda(q_{2n}) for every n in {1, 2, ..., (m-1)/2}, (3) lambda({p_i, p_{i+1}}) = lambda({q_j, q_{j+1}}) and lambda({p_j, p_{j+1}}) = lambda({q_i, q_{i+1}}), for all odd i in {1, 2, ..., m} and all even j in {1, 2, ..., m}.” The printed range in clause (3) reaches m, but the edge {p_m,p_{m+1}} does not exist. Config38 therefore quantifies over the actual edge positions 1 through m-1. One-based parity is expressed by val(i) mod 2, with zero for odd positions and one for even positions.

**Definition 1.6 (Conjecture 5.3).**

$$(claim) \Leftrightarrow (\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall m \in \mathrm{Nat},\; \forall P \in \operatorname{ColoredPath}\left(V, E, m\right),\; \forall Q \in \operatorname{ColoredPath}\left(V, E, m\right),\; (\operatorname{det}\left(\operatorname{concentration}\left(P\right)\right) = \operatorname{det}\left(\operatorname{concentration}\left(Q\right)\right)) \Rightarrow ((Q = P) \lor \left((Q = \operatorname{reflect}\left(P\right)) \lor \left(((\operatorname{Even}\left(m\right)) \land ((\operatorname{Config36}\left(P, Q\right)) \lor \left((\operatorname{Config36}\left(\operatorname{reflect}\left(P\right), Q\right)) \lor \left((\operatorname{Config36}\left(P, \operatorname{reflect}\left(Q\right)\right)) \lor (\operatorname{Config36}\left(\operatorname{reflect}\left(P\right), \operatorname{reflect}\left(Q\right)\right))\right)\right))) \lor ((\operatorname{Odd}\left(m\right)) \land ((\operatorname{Config38}\left(P, Q\right)) \lor \left((\operatorname{Config38}\left(\operatorname{reflect}\left(P\right), Q\right)) \lor \left((\operatorname{Config38}\left(P, \operatorname{reflect}\left(Q\right)\right)) \lor (\operatorname{Config38}\left(\operatorname{reflect}\left(P\right), \operatorname{reflect}\left(Q\right)\right))\right)\right)))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.claim` (`✓ std3`).

*Citation.* Hannah Göbel, Pratik Misra (2025). *Linear relations of colored Gaussian cycles*. DOI: [10.48550/arXiv.2506.23936](https://doi.org/10.48550/arXiv.2506.23936). URL: <https://arxiv.org/abs/2506.23936v1>.

*Commentary.*

Conjecture 5.3 reads verbatim: “Let P and Q be two colored paths on m vertices with det(K_P) = det(K_Q). (1) If m is even, then one of the following conditions holds: • Q is identical to P, • Q is a reflection of P, • P and Q satisfy the color configuration stated in Theorem 3.6 or is a reflection of the same. (2) Similarly, if m is odd, then one of the following conditions holds: • Q is identical to P, • Q is a reflection of P, • P and Q satisfy the color configuration stated in Theorem 3.8 or is a reflection of the same.” The displayed claim reads the final reflection phrase in its widest form: neither path, P alone, Q alone, or both paths may be reflected.

**Theorem 1.7 (Conjecture 5.3 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gobel-misra-colored-path-determinant-refutation` (refuted) by `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gobel-misra-colored-path-determinant-refutation","declaration_gid":"D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take one vertex color a, two edge colors u and v, and m=7. The edge sequences P=(u,v,v,u,u,v) and Q=(u,u,v,u,v,v) have the common determinant a^7-3a^5u^2-3a^5v^2+2a^3u^4+6a^3u^2v^2+2a^3v^4-2au^4v^2-2au^2v^4. They are neither identical nor reflections. The four Config38 variants all fail their edge clause: for (P,Q), e_1(P)=u differs from e_6(Q)=v; for (reflect(P),Q), e_1(reflect(P))=v differs from e_2(Q)=u; for (P,reflect(Q)), e_3(P)=v differs from e_6(reflect(Q))=u; and for the double reflection, e_1(reflect(P))=v differs from e_6(reflect(Q))=u.

## References

- Truth anchor: `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.ColoredPath`
- Truth anchor: `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.Config36`
- Truth anchor: `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.Config38`
- Truth anchor: `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.concentration`
- Truth anchor: `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.reflect`
- Truth anchor: `D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.result`
