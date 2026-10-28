# The Actual Biased Boundary Operator

## Abstract

The original infinite biased trace has dense range. Its free-root form has a densely defined self-adjoint realization, a compact resolvent, exactly the constant zero modes and a multiplicity-preserving positive covariance eigenspace identification.

**Definition 1.1 (centeredTrace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.centeredTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.centeredTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the original C=Pi J with codomain the actual mean-zero subspace G0 of L2(M). Its domain is the original infinite edge ell2. The product law M has the original golden biased probabilities.

**Definition 1.2 (boundaryCovariance).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryCovariance`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The boundary covariance is CC* acting on the original ambient L2(M). It maps into G0 and annihilates constants. It is distinct from the edge covariance Sigma=C*C, whose kernel can be large.

**Definition 1.3 (boundaryResolvent).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryResolvent`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryResolvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Writing A=CC*, positivity gives the bounded inverse T=(I+A)^(-1). The actual resolvent is constG composed with mean, plus A composed with T. The theorem proves its two-sided inverse graph equation for the same boundaryOperator, rather than assuming resolvent data.

**Definition 1.4 (boundaryEigenspace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryEigenspace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryEigenspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real lambda, this is the submodule of actual G consisting of u for which (u,lambda u) belongs to the entire graph of the original boundaryOperator. It includes the operator domain condition.

**Definition 1.5 (covarianceEigenEquiv).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.covarianceEigenEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.covarianceEigenEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each positive mu, this linear equivalence sends a vector z in the full mu eigenspace of the original Sigma=C*C to Cz in the mu^(-1) eigenspace of the actual H. Its inverse sends u to mu^(-1) C*u. It acts on the complete eigenspaces, allowing repeated eigenvalues.

**Definition 1.6 (boundaryOperator).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryOperator`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The boundary operator is the partially defined linear map obtained from the exact graph mean(h)=0 and Pi(u)=CC*h. Its graph is proved to equal the weak variational graph of the original domain D={constG(c)+Jz} and the pairing of the attained original increment energy. Its definition assumes no operator realization or spectral conclusion.

**Theorem 1.7 (Self-Adjoint Realization of the Original Form).**

$$(\operatorname{DenseRange}\left(J\right))\land(\operatorname{DenseRange}\left(centeredTrace\right))\land(\neg \operatorname{FiniteDimensional}\left(\mathbb{R}, G_{0}\right))\land(\operatorname{Dense}\left(D\right))\land(\operatorname{Dense}\left(\operatorname{domain}\left(boundaryOperator\right)\right))\land(\operatorname{IsSelfAdjoint}\left(boundaryOperator\right))\land(\forall u: G, (\forall h: G, (\operatorname{pair}\left(u, h\right)\in \operatorname{graph}\left(boundaryOperator\right)\iff \operatorname{weakGraph}\left(u, h\right))))\land(\forall u: G, (\operatorname{pair}\left(u, 0\right)\in \operatorname{graph}\left(boundaryOperator\right)\iff \exists c: \mathbb{R}, u=\operatorname{constG}\left(c\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.actual_self_adjoint_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prefix cylinder is measurable, and the prefix cylinders form a generating pi-system for the sigma algebra of the original infinite ray space. For coordinate i and a prescribed bit, its inverse image is the union of the prefix cylinders of length i+1 carrying that bit. A vector annihilated by J* has zero integral on every nonempty cylinder because each cylinder indicator is the trace of an original single edge increment. The two first cylinders also give zero integral on the entire boundary. Uniqueness of vector measures on a generating pi-system forces the vector to vanish almost everywhere. Thus J has dense range, and projection gives dense range of the actual centered trace in G0. The original form domain is dense as it contains every Jz.

The actual stopping spaces establish infinite dimension. If G0 had dimension d, choose the stopping threshold 1/(d+2). The mass lower bound gives at least d+2 stopping cylinders, and their mean-zero span has dimension at least d+1. Its natural inclusion into G0 is injective, contradicting dimension d.

The weak graph is single-valued: CC*h=0 with mean(h)=0 implies C*h=0, and density of the original trace implies h=0. Constants and the pairs (CC*k,Pi k) belong to the graph. Testing them shows that its domain has trivial orthogonal complement and is dense. The same tests identify the orthogonal adjoint graph with the graph itself, giving self-adjointness as a partially defined Hilbert-space operator. The graph equality identifies this operator with the self-adjoint realization of the original free-root energy. At zero output, the graph equation is Pi(u)=0, so precisely the real constants are zero modes.

The polar unitary, its range and domain identities and global counting bounds require further results. The subsequent theorems establish compact resolvent and ordered positive modes directly on the same operator.

**Theorem 1.8 (Compact Resolvent of the Actual Operator).**

$$(\operatorname{IsCompactOperator}\left(boundaryResolvent\right))\land(\forall u: G, (\forall h: G, (\operatorname{pair}\left(u, h\right)\in \operatorname{graph}\left(boundaryOperator\right)\iff boundaryResolvent\left((u+h)\right)=u)))\land(\forall lambda: \mathbb{R}, (0<lambda\implies \forall u: G, (\operatorname{pair}\left(u, \operatorname{smul}\left(lambda, u\right)\right)\in \operatorname{graph}\left(boundaryOperator\right)\iff (\operatorname{mean}\left(u\right)=0)\land(boundaryCovariance\left(u\right)=\operatorname{smul}\left(\operatorname{inverse}\left(lambda\right), u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.actual_compact_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A=CC* on the actual boundary L2 space. The pairing of (I+A)x with x is the sum of the squared norms of x and C*x. The pinned coercivity theorem therefore gives a bounded inverse T=(I+A)^(-1). Put R=constG composed with mean, plus A composed with T. Since C is the original stopping-derived compact map, A is compact. The constant part of R has rank at most one, so R is compact.

The exact weak graph implies (I+A)u=constG(mean(u+h))+A(u+h). Conversely that equation implies mean(h)=0 and Pi(u)=Ah. Injectivity of I+A then proves that (u,h) belongs to the actual operator graph exactly when R(u+h)=u. Thus R is the actual two-sided inverse of H+I, including the constant mode. This proves compact resolvent without assuming a polar unitary or a spectral-counting target.

For each positive real lambda, the actual eigenvector equation (u,lambda u) in graph(H) is equivalent to mean(u)=0 and Au=lambda^(-1)u. This is the inverse eigenvalue correspondence with the actual boundary covariance CC*. The following theorems identify the complete eigenspaces with the original edge covariance C*C and construct an ordered complete sequence. The literal polar expression in source equation (2.3) requires additional results.

**Theorem 1.9 (The Original Covariance and Operator Eigenspaces).**

$$\forall mu: \mathbb{R}, (0<mu\implies (\forall z: \operatorname{eigenspace}\left(Sigma, mu\right), (z\in K))\land(\forall z: \operatorname{eigenspace}\left(Sigma, mu\right), (\operatorname{covarianceEigenEquiv}\left(mu\right)\left(z\right)=\operatorname{C}\left(z\right)))\land(\forall u: \operatorname{boundaryEigenspace}\left(\operatorname{inverse}\left(mu\right)\right), (\operatorname{inverse}\left(\operatorname{covarianceEigenEquiv}\left(mu\right)\right)\left(u\right)=\operatorname{smul}\left(\operatorname{inverse}\left(mu\right), \operatorname{adjoint}\left(C, u\right)\right)))\land(\operatorname{FiniteDimensional}\left(\mathbb{R}, \operatorname{boundaryEigenspace}\left(\operatorname{inverse}\left(mu\right)\right)\right))\land(\forall z: \operatorname{eigenspace}\left(Sigma, mu\right), (z\neq 0\implies mu\leq phi))\land(\forall u: \operatorname{boundaryEigenspace}\left(\operatorname{inverse}\left(mu\right)\right), (u\neq 0\implies \operatorname{inverse}\left(phi\right)\leq \operatorname{inverse}\left(mu\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.actual_covariance_eigenspaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive mu, intertwining CC* with C*C sends each original covariance eigenvector z to Cz. The inverse eigenvalue equation puts this trace in the actual boundary operator domain with eigenvalue mu^(-1). Conversely an actual operator eigenvector u at that value gives CC*u=mu u; applying C* and scaling gives the edge eigenvector mu^(-1)C*u. The two maps compose to the identity on both full eigenspaces. This is an explicit linear equivalence, so multiplicities are preserved without assuming simplicity.

Each positive edge eigenvector is mu^(-1)C*Cz and hence lies in K, since the original adjoint range lies in K. Thus these are precisely the effective edge modes relevant to the source. The original stopping-derived compactness of Sigma and the pinned finite-eigenspace theorem make its nonzero eigenspaces finite dimensional. The explicit equivalence transfers this property to the actual operator eigenspaces. At the empty prefix, the inherited suffix Hardy estimate gives the squared centered-trace norm bound with coefficient phi. On a nonzero mu eigenvector its covariance quadratic form is mu times its squared increment norm, so mu is at most phi. Consequently every nonzero actual operator eigenvector at mu^(-1) has eigenvalue at least phi^(-1). This proves the eigenvector gap; it does not define or settle the original spectral counting function.

The following theorem constructs complete ordered positive modes. The polar range and domain identities, source equation (2.3) in its literal W form and the global counting inequalities require further results.

**Theorem 1.10 (Complete Ordered Positive Spectral Modes).**

$$\exists b: \operatorname{HilbertBasis}\left(\operatorname{Nat}\left(\right), \operatorname{Real}\left(\right), \operatorname{Gzero}\left(\right)\right), \exists k: \operatorname{HilbertBasis}\left(\operatorname{Nat}\left(\right), \operatorname{Real}\left(\right), K\right), \exists mu: \operatorname{Function}\left(\operatorname{Nat}\left(\right), \operatorname{Real}\left(\right)\right), (\forall i: \operatorname{Nat}\left(\right), (0<mu\left(i\right)))\land(\operatorname{Antitone}\left(mu\right))\land(\operatorname{TendstoZero}\left(mu\right))\land(\operatorname{Monotone}\left(\operatorname{reciprocalFamily}\left(mu\right)\right))\land(\operatorname{TendstoInfinity}\left(\operatorname{reciprocalFamily}\left(mu\right)\right))\land(\forall i: \operatorname{Nat}\left(\right), (\operatorname{boundaryCovariance}\left(b\left(i\right)\right)=\operatorname{smul}\left(mu\left(i\right), b\left(i\right)\right)))\land(\forall i: \operatorname{Nat}\left(\right), (\operatorname{pair}\left(b\left(i\right), \operatorname{smul}\left(\operatorname{inverse}\left(mu\left(i\right)\right), b\left(i\right)\right)\right)\in \operatorname{graph}\left(boundaryOperator\right)))\land(\forall i: \operatorname{Nat}\left(\right), (\operatorname{Sigma}\left(k\left(i\right)\right)=\operatorname{smul}\left(mu\left(i\right), k\left(i\right)\right)))\land(\forall i: \operatorname{Nat}\left(\right), (\operatorname{C}\left(k\left(i\right)\right)=\operatorname{smul}\left(\operatorname{sqrt}\left(mu\left(i\right)\right), b\left(i\right)\right)))\land(\forall a: \operatorname{Real}\left(\right), (0<a\implies \operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), \operatorname{boundaryEigenspace}\left(\operatorname{inverse}\left(a\right)\right)\right)))\land(\forall a: \operatorname{Real}\left(\right), (0<a\implies \operatorname{finrank}\left(\operatorname{Real}\left(\right), \operatorname{boundaryEigenspace}\left(\operatorname{inverse}\left(a\right)\right)\right)=\operatorname{cardinality}\left(\operatorname{fiber}\left(mu, a\right)\right)))\land(\forall epsilon: \operatorname{Real}\left(\right), (0<epsilon\implies \operatorname{Finite}\left(\operatorname{superlevel}\left(mu, epsilon\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.actual_positive_spectral_exhaustion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict the actual boundary covariance CC* to the closed mean-zero space G0. Its quadratic form is the squared norm of C*u, strictly positive for nonzero u by density of the original trace. Compactness is inherited from the actual centered trace. The compact symmetric Hilbert-basis theorem assembles all its eigenspaces, so no basis or spectral exhaustion is assumed.

For each positive epsilon, only finitely many basis indices can have covariance weight at least epsilon. Otherwise their images under the actual compact covariance admit a convergent subsequence, while orthogonality makes the squared distance of any distinct pair the sum of the two squared weights, at least twice epsilon squared. Order the full index by decreasing weight, resolving ties with a fixed linear order. Every initial interval is finite, so the infinite index is order-isomorphic to Nat. This lists every basis vector once, including every repeated eigenvalue. The weights decrease to zero and their reciprocals increase to infinity. Lean index i corresponds to source index j=i+1.

Normalize C* applied to each boundary basis vector by the reciprocal square root of its covariance weight. These vectors lie in the original K, are orthonormal and have dense span: a vector orthogonal to all of them has trace orthogonal to the entire boundary basis, hence zero trace and zero effective increment. They therefore form a full Hilbert basis of K, with Sigma eigenvalue mu and trace equal to sqrt(mu) times the boundary basis vector. The exact inverse eigenvalue graph equation puts each boundary mode in the original operator domain with eigenvalue 1/mu.

For any positive a, symmetry forces a covariance eigenvector's coordinates to vanish outside the indices with weight a. This full eigenspace is exactly the span of those basis vectors. The coordinate family is independent, so its cardinality equals the finite dimension of the full actual H eigenspace at 1/a. Thus the enumeration preserves finite multiplicities without a simplicity assumption. The global counting estimates, trial-space inequality, polar domain and range identities and literal polar resolvent formula are separate conclusions.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.actual_compact_resolvent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.actual_covariance_eigenspaces`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.actual_positive_spectral_exhaustion`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.actual_self_adjoint_realization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryCovariance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryEigenspace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryOperator`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.boundaryResolvent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.centeredTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.covarianceEigenEquiv`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm](BiasedBoundaryFreeRootForm.md)
- Dependency: [D5/S3/Quantum/Analysis/CompactEigenbasis](../../../Quantum/Analysis/CompactEigenbasis.md)
