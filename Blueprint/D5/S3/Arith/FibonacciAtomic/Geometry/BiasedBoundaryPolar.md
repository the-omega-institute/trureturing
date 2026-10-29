# The Actual Real Polar Realization

## Abstract

Let G be the original real biased boundary L2 space, let G0 be its mean-zero subspace, and let K be the orthogonal complement of the original edge covariance kernel. The paired Hilbert bases identify K and G0 by the real linear isometry equivalence W that preserves every coefficient. No scalar extension is used.

**Definition 1.1 (The Paired Basis Isometry).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.polar`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.polar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real isometry from K to G0 is k.repr followed by the inverse of b.repr. It preserves all coefficients of the paired Hilbert bases.

**Definition 1.2 (The Original Covariance on K).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.covarianceK`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.covarianceK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

covarianceK is Sigma restricted to K and codomain-restricted to K using the adjoint range inclusion. Its coefficient formula relates the original covariance to the boundary graph.

**Theorem 1.3 (Paired Isometry Coefficients).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.polar_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.polar_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x in K and every index i, the b coefficient of polar(b,k)(x) equals the k coefficient of x.

**Theorem 1.4 (Covariance Coefficients on the Same Family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.covariance_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.covariance_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For paired bases b,k and positive mu with the original Sigma and C basis actions, every x in K has covarianceK coefficient mu(i) times its k coefficient. The heat uses this formula on the same ordered spectral family as its eigenvalue bounds.

**Theorem 1.5 (The Parameterized Original Graph).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.graph_polar`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.graph_polar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same paired bases and covariance actions, an arbitrary pair (u,h) of ambient boundary vectors belongs to boundaryOperator.graph exactly when some x in K has h=polar(x) and Pi(u)=polar(covarianceK(x)), with the original inclusions into G. This identity describes the entire graph and its domain.

**Theorem 1.6 (The Actual Real Polar Realization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.actual_polar_domains_resolvent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.actual_polar_domains_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be the original real biased boundary L2 space, let G0 be its mean-zero subspace, and let K be the orthogonal complement of the original edge covariance kernel. The paired Hilbert bases identify K and G0 by the real linear isometry equivalence W that preserves every coefficient. No scalar extension is used.

The bounded operator S is the centered trace on K transported back by W. The paired basis and the original adjoint show on every vector that S multiplies coefficient i by sqrt(mu(i)). The operator T is the original Sigma restricted to K and multiplies coefficient i by mu(i). Thus S squared equals T and the actual centered trace is W composed with S. Their strictly positive diagonal coefficients make both S and T injective, so their inverses on their respective ranges are unambiguous. On centered boundary vectors the original adjoint is S composed with W inverse, followed by the inclusion into the original edge space.

A centered boundary vector belongs to the original free-root form domain exactly when it is W(S(x)) for some x in K. It belongs to the original operator domain exactly when it is W(T(x)). The original operator graph consists precisely of pairs (u,h) with h=W(x) and Pi(u)=W(T(x)), with each centered vector included into G. Hence the operator on G0 is the inverse of T transported by W; the inverse is used on the range of T. The analogous inverse of S is used on the range of S.

The original least increment lift retains its root coefficient mean(F)-mean(J(lift(F))). The domain identification uses that original representation and its attained least energy; it does not identify the energy of an arbitrary extension with the minimum.

The bounded operator R multiplies every K coefficient by 1/(1+mu(i)). Both R(x)+T(R(x))=x and R(x+T(x))=x hold on all of K. In contrast with the inverse of T, this inverse of I+T is total.

For every F in G, the original resolvent equals constG(mean(F)) plus W(T(R(W inverse(Pi(F))))), included in G. This is the literal sum of the projection onto constants and W T (I+T) inverse W adjoint on the centered summand. The proof constructs a pair in the original weak graph whose sum is F and applies the already established inverse characterization of the resolvent. The original compact-resolvent and simple-zero-mode results therefore concern this same operator.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.actual_polar_domains_resolvent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.covarianceK`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.covariance_coeff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.graph_polar`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.polar`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPolar.polar_coeff`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySpectralForm](BiasedBoundarySpectralForm.md)
