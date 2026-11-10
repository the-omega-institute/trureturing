# MatrixUnitGenerator

## Abstract

The computed averaged derivative generates every moving logical matrix unit. A real differentiable-path adapter derives the tangent hypotheses. Dyson convergence, global ODE existence, and physical implementability are not assumed or certified by these declarations.

**Theorem 1.1 (matrix unit transport generator).**

Lean statement: `D5/S3/Quantum/Transport/MatrixUnitGenerator.matrix_unit_transport_generator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/MatrixUnitGenerator.matrix_unit_transport_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tosio Kato (1950). *On the Adiabatic Theorem of Quantum Mechanics*. DOI: [10.1143/JPSJ.5.435](https://doi.org/10.1143/JPSJ.5.435).

*Commentary.*

The computed averaged derivative generates every moving logical matrix unit. A real differentiable-path adapter derives the tangent hypotheses. Dyson convergence, global ODE existence, and physical implementability are not assumed or certified by these declarations.

**Theorem 1.2 (generator from real path).**

Lean statement: `D5/S3/Quantum/Transport/MatrixUnitGenerator.generator_from_real_path`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/MatrixUnitGenerator.generator_from_real_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tosio Kato (1950). *On the Adiabatic Theorem of Quantum Mechanics*. DOI: [10.1143/JPSJ.5.435](https://doi.org/10.1143/JPSJ.5.435).

*Commentary.*

The computed averaged derivative generates every moving logical matrix unit. A real differentiable-path adapter derives the tangent hypotheses. Dyson convergence, global ODE existence, and physical implementability are not assumed or certified by these declarations.

Euclidean operator-norm application. Let d and n be arbitrary finite index types, and let F and D be families of complex n by n matrices indexed by d by d. Assume only the full matrix-unit laws F(i,j)F(k,l) = delta(j,k)F(i,l) and F(i,j)* = F(j,i), where star is conjugate transpose and delta is the Kronecker delta. D is arbitrary. All matrix norms in this application are the operator norm on EuclideanSpace over the complex numbers, selected in Lean by Matrix.Norms.L2Operator.

Write P = unitSupport(F), the sum of F(i,i) over d, and V(D) = supportVelocity(D), the sum of D(i,i) over d. Write K(F,D) = transportGenerator(F,D) = Z - P V(D), where Z = averagedVelocity(F,D) is the complex reciprocal of card(d) times the double sum of D(i,j)F(j,i). These are the existing computed operators. Real and complex reciprocals are totalized, with the reciprocal of zero equal to zero.

In the formula, FiniteTypes denotes finite index types, MatrixFamily(d,n) denotes d -> d -> Matrix n n C, MatrixUnits(F) denotes precisely the two laws above, ComplexI is the imaginary unit, and h is the positive real parameter hbar. For every such family and every such h, the following bound follows from the existing C-star and norm inequalities; the two owner theorems above do not themselves state this estimate.

$\forall d, n \in \operatorname{FiniteTypes}\left(\right),\ \forall F, D \in \operatorname{MatrixFamily}\left(d, n\right),\ \forall h \in \mathbb{R},\ (\operatorname{MatrixUnits}\left(F\right) \land 0 < h) \implies \Vert \operatorname{ComplexI}\left(\right) h \operatorname{K}\left(F, D\right)\Vert \le h(\frac{1}{\operatorname{card}\left(d\right)} \sum_{i \in d} \sum_{j \in d} \Vert \operatorname{D}\left(i, j\right)\Vert + \Vert \operatorname{V}\left(D\right)\Vert)$

The multiplication and star laws make P and each F(j,j) self-adjoint idempotents. IsStarProjection.norm_le therefore gives norm(P) <= 1 and norm(F(j,j)) <= 1, including zero projections. Matrix.l2_opNorm_conjTranspose_mul_self, the matrix form of CStarRing.norm_star_mul_self, gives norm(F(i,j)) squared = norm(F(j,j)); hence every matrix unit has norm at most one. No equality to one is needed.

By Matrix.l2_opNorm_mul, each norm(D(i,j)F(j,i)) is at most norm(D(i,j)). Two applications of norm_sum_le and norm_smul bound norm(Z) by the real reciprocal of card(d) times the double sum of norm(D(i,j)). The same product inequality gives norm(P V(D)) <= norm(V(D)). Finally norm_sub_le bounds norm(K) by their sum, and norm_smul with norm(ComplexI times h) = h gives the displayed inequality. This is a direct application of the existing library estimates to the computed generator.

For a differentiable matrix-unit path, substitute its value at a time t for F and its entrywise derivative at t for D. Differentiating the finite diagonal sum identifies supportVelocity(D) with the derivative of P. Thus D = dot F and supportVelocity(D) = dot P give exactly the geometric-term bound in ST40.1. The norm estimate itself uses neither differentiated multiplication nor differentiated star hypotheses; the owner generator theorems use those additional relations to prove skew-adjointness and the commutator equations.

The definitions and estimate require neither index type to be nonempty. An empty logical index makes both sums, P, V and K zero. An empty physical index also gives zero matrices. A zero family F gives K = 0 for arbitrary D, and proper support is allowed. Faithfulness, full rank, full support and nonzero matrix units are unnecessary. For arbitrary D this estimate asserts no skew-adjointness, Hamiltonian realization or transport existence. It supplies no device bandwidth, energy cost, locality or physical attainability conclusion, and does not establish the remaining Hamiltonian and evolution assertions of ST40.1.

## References

- Truth anchor: `D5/S3/Quantum/Transport/MatrixUnitGenerator.generator_from_real_path`
- Truth anchor: `D5/S3/Quantum/Transport/MatrixUnitGenerator.matrix_unit_transport_generator`
- Dependency: [D5/S3/Quantum/Recovery/MatrixUnitDecoder](../Recovery/MatrixUnitDecoder.md)
