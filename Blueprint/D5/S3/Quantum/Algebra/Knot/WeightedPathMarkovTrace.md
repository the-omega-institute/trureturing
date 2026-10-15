# Weighted Path Tower and Markov Trace

## Abstract

Finite Perron path algebras admit a trace-preserving tower and an exact last-generator compression law.

**Theorem 1.1 (The actual finite path tower).**

$$\begin{gathered}\operatorname{FinitePerronData}\left(L, R, d, delta\right)\\\forall n \in \mathbb{N},\; \forall s \in L,\; \operatorname{UnitalInjectiveStarAlgebraInclusion}\left(\operatorname{iota}\left(n, s\right)\right)\\\forall t \in L,\; \forall u \in L,\; \operatorname{R}\left(t, u\right)\Rightarrow \operatorname{adjoint}\left(\operatorname{J}\left(t, u\right)\right) \cdot \operatorname{J}\left(t, u\right) = 1\\\forall t \in L,\; \forall v \in L,\; \forall u \in L,\; \operatorname{DistinctLegalPredecessors}\left(t, v, u\right)\Rightarrow \operatorname{adjoint}\left(\operatorname{J}\left(t, u\right)\right) \cdot \operatorname{J}\left(v, u\right) = 0\\\forall t \in L,\; \forall u \in L,\; \forall Y \in \operatorname{C}\left(n+1, s\right),\; \operatorname{R}\left(t, u\right)\Rightarrow \operatorname{adjoint}\left(\operatorname{J}\left(t, u\right)\right) \cdot \operatorname{block}\left(Y, u\right) \cdot \operatorname{J}\left(t, u\right) = \operatorname{appendSubmatrix}\left(Y, t, u\right)\\\forall X \in \operatorname{C}\left(n, s\right),\; \operatorname{F}\left(n, s, \operatorname{iota}\left(n, s, X\right)\right) = X; \forall Y \in \operatorname{C}\left(n+1, s\right),\; \operatorname{tau}\left(n, s, \operatorname{F}\left(n, s, Y\right)\right) = \operatorname{tau}\left(n+1, s, Y\right)\\\forall A \in \operatorname{C}\left(n, s\right),\; \forall B \in \operatorname{C}\left(n, s\right),\; \forall Y \in \operatorname{C}\left(n+1, s\right),\; \operatorname{F}\left(n, s, \operatorname{iota}\left(n, s, A\right) \cdot Y \cdot \operatorname{iota}\left(n, s, B\right)\right) = A \cdot \operatorname{F}\left(n, s, Y\right) \cdot B\\\forall X \in \operatorname{C}\left(n, s\right),\; \operatorname{tau}\left(n+1, s, \operatorname{iota}\left(n, s, X\right)\right) = \operatorname{tau}\left(n, s, X\right); \operatorname{tau}\left(n, s, 1\right) = 1\\\operatorname{Positive}\left(n\right)\Rightarrow (\operatorname{F}\left(n, s, \operatorname{e}\left(n\right)\right) = \frac{1}{delta^{2}} \cdot 1; \forall X \in \operatorname{C}\left(n, s\right),\; \operatorname{tau}\left(n+1, s, \operatorname{iota}\left(n, s, X\right) \cdot \operatorname{e}\left(n\right)\right) = \frac{1}{delta^{2}} \cdot \operatorname{tau}\left(n, s, X\right); \operatorname{adjoint}\left(\operatorname{e}\left(n\right)\right) = \operatorname{e}\left(n\right); \operatorname{e}\left(n\right) \cdot \operatorname{e}\left(n\right) = \operatorname{e}\left(n\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.weighted_path_markov_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be a finite vertex type, R a symmetric decidable relation, d a strictly positive real weight at every vertex, and delta a strictly positive real number. Assume the Perron equality sum of d(u) over R(t,u) equals delta d(t) at every t. Fix a start s. P(n,s,t) is the literal LegalPath R n s t of WeightedLegalPathTemperleyLieb; C(n,s) is the product over t of complex matrices on P(n,s,t). Empty endpoint fibers are included.

Appending the last edge t to u gives an injective map a(t,u) from P(n,s,t) into P(n+1,s,u). The rectangular matrix J(t,u) has entry one at (a(t,u)(x),x), and zero elsewhere. Splitting a long path into its predecessor endpoint and prefix identifies P(n+1,s,u) with the disjoint union of P(n,s,t) over R(t,u). In these coordinates iota(X) is the block diagonal matrix with blocks X(t). The compression F(Y)(t) is the sum over R(t,u) of d(u)/(delta d(t)) times J(t,u) conjugate-transpose Y(u) J(t,u).

The trace is tau(n,s)(X) = sum over t of d(t) trace(X(t)), divided by delta to the n times d(s). The theorem proves the append decomposition, the unital faithful star algebra inclusion, retraction and bimodule law of compression, trace preservation and normalization. For n positive, e(n) in C(n+1,s) is the exact old pathProjection R d delta (n+1) s t n in each endpoint block. Its compressed kernel vanishes off the diagonal. On a diagonal prefix, only the neighbor equal to the preceding vertex survives, and its Perron weight cancels the local denominator to give delta to the minus two.

In the displayed statement, FinitePerronData denotes precisely the hypotheses above. DistinctLegalPredecessors(t,v,u) means t differs from v and both R(t,u) and R(v,u) hold. Adjoint is conjugate transpose, block(Y,u) is Y(u), and appendSubmatrix(Y,t,u) has entry Y(u)(a(t,u)(x),a(t,u)(y)). UnitalInjectiveStarAlgebraInclusion means an injective complex-linear algebra homomorphism preserving one and adjoint. Positive(n) means zero is less than n.

The local Temperley-Lieb relations are reused from weighted_legal_path_temperley_lieb. Trace compatibility requires the additional finite predecessor-fiber reindexing and Perron equality. The tower and trace begin at n=0; the last-generator identity begins at n=1. No connectedness or nonempty-fiber assumption is made.

This is classical path-model background. Aharonov, Jones and Landau, A Polynomial Quantum Algorithm for Approximating the Jones Polynomial, arXiv:quant-ph/0511096v2, Definition 3.3 and Claim 3.6, give the explicit line-graph endpoint trace and its local Markov calculation. AJL uses unnormalized Temperley-Lieb generators with Markov coefficient one over delta. Multiplying the present literal projection by delta recovers that normalization, so its Markov coefficient is one over delta squared. Here the statement treats arbitrary finite positive Perron data and the entire endpoint-block algebra. This tower does not construct a geometric closure map, prove geometric Markov equivalence, or produce a knot with a prescribed Jones polynomial.

**Theorem 1.2 (Scalar linearity of the same endpoint trace).**

$$\forall n \in \mathbb{N},\; \forall s \in L,\; \forall c \in \mathbb{C},\; \forall X \in \operatorname{C}\left(n, s\right),\; \operatorname{tau}\left(n, s, \operatorname{SMul}\left(c, X\right)\right) = c \cdot \operatorname{tau}\left(n, s, X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.tau_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable L, arbitrary relation R, real weights d and real delta, every n and start s, every complex c and every X in C(R,n,s), tau(c times X) equals c tau(X). Positivity, symmetry and the Perron equality are not needed for this scalar identity. The Artin and signed Markov proofs consume this scalar-linearity helper at its source owner. It follows from matrix-trace scalar linearity and finite-sum distribution; it is a consumed helper rather than new independent mathematical content.

**Theorem 1.3 (Splitting an appended legal path).**

Lean statement: `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.split_append_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.split_append_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable L, relation R, natural n, endpoints s,t,u, edge R(t,u) and x in LegalPath(R,n,s,t), splitPath of append(x,u) is the sigma pair of the legal predecessor t and x. This is the original private proof exposed through a directly consumed alias, retaining its frozen private identity for the returning-block matrix-unit proof; it is a consumed helper and makes no independent mathematical claim.

**Theorem 1.4 (Appending preserves path distinctions).**

Lean statement: `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.append_isInjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.append_isInjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable L, relation R, natural n, endpoints s,t,u and legal edge R(t,u), append from LegalPath(R,n,s,t) to LegalPath(R,n+1,s,u) is injective. The existing proof is exposed through a directly consumed alias and its frozen private identity is retained and consumed by the returning-block matrix-unit proof. No positivity, symmetry or Perron condition is needed.

**Theorem 1.5 (The inclusion in literal append coordinates).**

Lean statement: `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.iota_append_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.iota_append_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable L, relation R, natural n, endpoints s,t,u, legal edge R(t,u), X in the full C(R,n,s), and x,y in LegalPath(R,n,s,t), the u-block entry of iota(X) at append(x,u),append(y,u) equals X(t)(x,y). This is the original private proof exposed through a directly consumed alias, retaining its frozen private identity and directly consumed by the new returning-block derivation. It is a helper, not an independent formalization gain.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.append_isInjective`
- Truth anchor: `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.iota_append_entry`
- Truth anchor: `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.split_append_coordinates`
- Truth anchor: `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.tau_smul`
- Truth anchor: `D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace.weighted_path_markov_trace`
- Dependency: [D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb](../WeightedLegalPathTemperleyLieb.md)
