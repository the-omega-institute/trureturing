# Diagonal Hamiltonian and Strong Heat

## Abstract

The actual algebraic diagonal operator has a self-adjoint closure and a positive whole-space heat with precisely its full negative generator graph.

**Definition 1.1 (The finite algebraic operator).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.finiteOperator`

*Formalization.* `D5/S3/Quantum/Analysis/DiagonalHeat.finiteOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every full complex Hilbert basis e of a complete Hilbert space and every real family h, this partial complex linear map has domain exactly the algebraic span of the range of e. LinearIndependent.repr supplies its finite coefficients; Finsupp.linearCombination synthesizes the basis vectors weighted by h.

**Definition 1.2 (The actual closure).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.hamiltonian`

*Formalization.* `D5/S3/Quantum/Analysis/DiagonalHeat.hamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary full basis e and real family h, the Hamiltonian is the actual LinearPMap closure of finiteOperator e h. The main theorem proves self-adjointness for nonnegative h and identifies the entire graph and weighted-l2 domain.

**Definition 1.3 (The bounded full-space multiplier).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier`

*Formalization.* `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary full basis e, real coefficients a, nonnegative real M and a proof that every absolute coefficient is at most M, transport the actual bounded l2 diagonal multiplier through e.repr. The resulting map is a bounded complex linear endomorphism of the entire ambient Hilbert space.

**Definition 1.4 (The whole-space heat).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.heat`

*Formalization.* `D5/S3/Quantum/Analysis/DiagonalHeat.heat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary full basis e and nonnegative real family h, at each nonnegative-real time t take the full-space multiplier with coefficient exp(-t*h(i)) and bound one. Zero eigenvalues give coefficient one and zero time gives the identity.

**Theorem 1.5 (The exact finite-span basis action).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.finite_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/DiagonalHeat.finite_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual full complex Hilbert basis e, arbitrary real coefficient family h and index i, finiteOperator e h maps the genuine domain vector e(i) to h(i) times e(i). The finite representation of e(i) is the single coefficient one at i. This exact action supplies both the self-adjoint closure theorem and the finite graph approximants used for the lower quadratic-form bound.

**Theorem 1.6 (Actual bounded coordinate action).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complete complex Hilbert space and e an actual full Hilbert basis indexed by any type I. Let a be a real family with absolute value at most the nonnegative real M. Transport multiplication by a through the isometric coefficient map from H to l2(I,Complex). This defines a bounded complex linear operator on all of H. For every vector x and every i, its i-th coefficient is a(i) times the coefficient of x. The bound is proved on the actual l2 multiplier before extending the action to H.

**Theorem 1.7 (Basis vectors remain genuine eigenvectors).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same assumptions, the actual multiplier sends e(i) to a(i) times e(i). Coordinate injectivity and the single-coordinate expansion prove the equality, including zero and repeated coefficients. These coordinate and vector identities also determine the heat and resolvent operators.

**Theorem 1.8 (Positivity on the whole Hilbert space).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If all a(i) are nonnegative, the actual bounded multiplier is positive. Parseval expresses its quadratic form as the genuinely convergent sum of a(i) times the squared modulus of the coefficient of x. Each term is real and nonnegative. This proves positivity and self-adjointness on the entire space, without a finite-dimensional hypothesis.

**Theorem 1.9 (The real exponential right derivative).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.scalar_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/DiagonalHeat.scalar_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real normed vector space V, every real scalar a and every vector z, the right limit at zero through nonnegative real times of t inverse times (exp(-t*a) times z minus z) equals minus a times z. No complex scalar structure, completeness or sign condition on a is required. The ordinary real exponential derivative and the right-slope limit give the result. It supplies finite-mode derivatives and coordinate derivatives in the full generator argument.

**Theorem 1.10 (The same closure has the full strong heat generator).**

Lean statement: `D5/S3/Quantum/Analysis/DiagonalHeat.diagonal_heat`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/DiagonalHeat.diagonal_heat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h(i) be finite nonnegative real coefficients. Define T0 on exactly the algebraic span of the full basis: apply LinearIndependent.repr to obtain finite coefficients and then Finsupp.linearCombination to synthesize the h-weighted basis vectors. Set K to the genuine partial-map closure of T0. The accepted real-eigenbasis closure theorem proves K self-adjoint and densely defined. Its full graph consists precisely of pairs (x,y) satisfying c(i,y)=h(i)*c(i,x) for every i. Its actual operator domain consists precisely of x whose h-weighted coefficients belong to l2. This domain need not be all of H.

For nonnegative time t, define T(t) as the bounded multiplier exp(-t*h(i)). It is positive, complex linear and contractive on all of H. There exists a strongly continuous contraction semigroup S whose real operators are exactly the scalar restrictions of T(t). Thus T(0) is the identity, T(s+t)=T(s) composed with T(t), and every orbit is continuous, including at zero.

For all ambient vectors x and v, the right strong limit of (T(t)x-x)/t as t tends to zero exists and equals v if and only if (x,-v) belongs to the graph of this same K. The forward implication uses each continuous coefficient functional and the scalar exponential derivative. For the reverse implication, the full graph-core theorem gives simultaneous finite-vector and operator-image approximants; closedness of the semigroup generator passes the finite derivatives to their graph limit. Any other strongly continuous contraction semigroup with this full generator graph equals S by the accepted generator uniqueness theorem.

All basis index types, empty and finite cases, repeated coefficients and zero eigenspaces are retained. No heat trace at time zero is asserted. The proof adapts the generic private heat construction in PhysicalHeatGenerator and uses the public general ContractionSemigroup closedness and uniqueness suppliers selected from Scott Armstrong with their Apache-2.0 source attribution. This is a standard diagonal operator construction, not a common-reference theorem for a family of quantum states.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.diagonal_heat`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.finiteOperator`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.finite_basis`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.hamiltonian`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.heat`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_basis`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_coeff`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.multiplier_positive`
- Truth anchor: `D5/S3/Quantum/Analysis/DiagonalHeat.scalar_derivative`
- Dependency: [D5/S3/Quantum/Analysis/ContractionSemigroup](ContractionSemigroup.md)
- Dependency: [D5/S3/Quantum/Analysis/EigenbasisGraphCore](EigenbasisGraphCore.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/GeneralProduct](TraceClass/GeneralProduct.md)
