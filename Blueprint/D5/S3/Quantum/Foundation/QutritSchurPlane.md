# An affine four-plane of original pure qutrit quotient images

## Abstract

Original pure lifts fill the qutrit quotient four-plane.

**Theorem 1.1 (The full support-one section).**

$$\forall V \in Type,\; [\mathrm{NormedAddCommGroup}\left(V\right)] [\mathrm{NormedSpace}\left(\mathbb{R}, V\right)] [\mathrm{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \mathrm{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall g \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall F \in \mathrm{Face}\left(C\right),\; \forall J \in \mathrm{Face}\left(C\right),\; \forall B \in \mathrm{Face}\left(C\right),\; \forall eF \in \mathrm{LinearEquiv}\left(\mathbb{R}, \mathrm{span}\left(\mathbb{R}, F\right), \mathrm{HermitianMat}\left(\mathrm{Fin}\left(3\right), \mathbb{C}\right)\right),\; \forall eJ \in \mathrm{LinearEquiv}\left(\mathbb{R}, \mathrm{span}\left(\mathbb{R}, J\right), \mathrm{HermitianMat}\left(\mathrm{Fin}\left(3\right), \mathbb{C}\right)\right),\; \left(\left(\forall x \in V,\; \left(x \in C \land \left(\neg x = 0\right)\right) \Rightarrow 0 < u\left(x\right)\right) \land \left(\left(\forall x \in V,\; x \in C \Rightarrow \left(0 \le g\left(x\right) \land \left(g\left(x\right) = 0 \Leftrightarrow x \in F\right)\right)\right) \land \left(\mathrm{wholePairBalls}\left(C, u\right) \land \left(B = \mathrm{intersection}\left(F, J\right) \land \left(\mathrm{finrank}\left(\mathbb{R}, \mathrm{span}\left(\mathbb{R}, B\right)\right) = 4 \land \left(\left(\forall x \in \mathrm{span}\left(\mathbb{R}, F\right),\; \left(\mathrm{val}\left(x\right) \in F \Leftrightarrow 0 \le eF\left(x\right)\right) \land \mathrm{trace}\left(eF\left(x\right)\right) = u\left(\mathrm{val}\left(x\right)\right)\right) \land \left(\forall x \in \mathrm{span}\left(\mathbb{R}, J\right),\; \left(\mathrm{val}\left(x\right) \in J \Leftrightarrow 0 \le eJ\left(x\right)\right) \land \mathrm{trace}\left(eJ\left(x\right)\right) = u\left(\mathrm{val}\left(x\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\mathrm{inf}\left(\mathrm{span}\left(\mathbb{R}, F\right), \mathrm{span}\left(\mathbb{R}, J\right)\right) = \mathrm{span}\left(\mathbb{R}, B\right) \land \left(\exists gQ \in \mathrm{LinearMap}\left(\mathbb{R}, \mathrm{quotient}\left(V, \mathrm{span}\left(\mathbb{R}, F\right)\right), \mathbb{R}\right),\; \exists q0 \in \mathrm{quotient}\left(V, \mathrm{span}\left(\mathbb{R}, F\right)\right),\; \exists L \in \mathrm{LinearMap}\left(\mathbb{R}, \mathrm{functions}\left(\mathrm{Fin}\left(2\right), \mathbb{C}\right), \mathrm{quotient}\left(V, \mathrm{span}\left(\mathbb{R}, F\right)\right)\right),\; \mathrm{comp}\left(gQ, \mathrm{mkQ}\left(\mathrm{span}\left(\mathbb{R}, F\right)\right)\right) = g \land \left(\mathrm{Injective}\left(L\right) \land \left(\mathrm{finrank}\left(\mathbb{R}, \mathrm{range}\left(L\right)\right) = 4 \land \left(\mathrm{image}\left(\mathrm{mkQ}\left(\mathrm{span}\left(\mathbb{R}, F\right)\right), \mathrm{setOf}\left(r\mapsto \exists p \in \mathrm{pure}\left(C, u\right),\; \exists a \in \mathbb{R},\; \mathrm{val}\left(p\right) \in J \land \left(\left(\neg \mathrm{val}\left(p\right) \in F\right) \land \left(0 < a \land \left(r = \mathrm{smul}\left(a, \mathrm{val}\left(p\right)\right) \land g\left(r\right) = 1\right)\right)\right)\right)\right) = \mathrm{setOf}\left(q\mapsto q \in \mathrm{map}\left(\mathrm{mkQ}\left(\mathrm{span}\left(\mathbb{R}, F\right)\right), \mathrm{span}\left(\mathbb{R}, J\right)\right) \land gQ\left(q\right) = 1\right) \land \mathrm{setOf}\left(q\mapsto q \in \mathrm{map}\left(\mathrm{mkQ}\left(\mathrm{span}\left(\mathbb{R}, F\right)\right), \mathrm{span}\left(\mathbb{R}, J\right)\right) \land gQ\left(q\right) = 1\right) = \mathrm{affineSubspace}\left(q0, \mathrm{range}\left(L\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/QutritSchurPlane.original_qutrit_quotient_affine_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg; Leonardo A. Lessa; Rodolfo Soldati (2026). *Finite density states and strong subadditivity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/2725b6f621901d4cd330869e9b77105045c1582e/QuantumInfo/Entropy/SSA.lean>.

*Commentary.*

Let C be a pointed cone in a finite-dimensional real normed vector space V with real-linear unit u strictly positive off zero in C. An original pure state is an extreme point of the full u = 1 base. Every pair of distinct original pure states is assumed to generate an actual face with a whole affine ball chart. The actual cone faces F and J have real-linear coordinates on their whole spans carrying their cones to the full complex Hermitian three-by-three positive semidefinite cone and their normalization to the trace. Their actual intersection B has real span of dimension four. The real-linear g is nonnegative on C and its zero set in C is exactly F.

The span of each face D is written S(D). The map pi is the quotient by S(F), and gQ is the real-linear functional on the quotient with gQ composed with pi equal to g. The set R comprises all positive multiples of original pure states in J outside F for which g is one. The theorem gives the equality of the homogeneous intersection with S(B) and identifies the image of R with the whole gQ = 1 slice of pi(S(J)). This slice is an affine translate of the range of an injective real-linear map from two complex coordinates and has four real direction dimensions.

In J, the positive Hermitian representative of g can be diagonalized by a unitary change of coordinates. A positive eigenvalue gives a pivot. Positive matrices in B have zero pivot column by positivity of the quadratic form. Comparing dimensions shows that their real span fills the entire lower Hermitian block. The pivot reading therefore determines g on J, and the quotient kills the lower block. For each off-column, a rank-one outer product with the prescribed positive pivot gives the Schur completion. Trace normalization and faciality give an original pure state for this completion. Equality of two such quotient images implies equality of the original lifts by QutritPureLift, which recovers the off-column and determines the homogeneous intersection.

This supplies the local binary-intersection step for the carrier dimension seventeen route to XIII160.34. Its scope is static state geometry and quotient reconstruction. Global incidence, topology, dynamical laws, physical clocks, energy, and thermodynamic cost require separate results.

**Definition 1.2 (Hermitian reindexing).**

$$\forall iota \in Type,\; \forall kappa \in Type,\; \forall sigma \in \mathrm{Equiv}\left(iota, kappa\right),\; \mathrm{LinearEquiv}\left(\mathbb{R}, \mathrm{HermitianMat}\left(iota, \mathbb{C}\right), \mathrm{HermitianMat}\left(kappa, \mathbb{C}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/QutritSchurPlane.reindexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An equivalence of index types induces a real-linear equivalence on complex Hermitian matrices. Its forward map reindexes rows and columns by the given equivalence, and its inverse reindexes by the inverse equivalence.

**Definition 1.3 (Unitary congruence).**

$$\forall iota \in Type,\; [\mathrm{Fintype}\left(iota\right)] [\mathrm{DecidableEq}\left(iota\right)] \forall U \in \mathrm{unitaryGroup}\left(iota, \mathbb{C}\right),\; \mathrm{LinearEquiv}\left(\mathbb{R}, \mathrm{HermitianMat}\left(iota, \mathbb{C}\right), \mathrm{HermitianMat}\left(iota, \mathbb{C}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/QutritSchurPlane.unitaryEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a unitary matrix U on a finite index type with decidable equality, the map X ↦ U X U* is a real-linear equivalence of complex Hermitian matrices. Its inverse is X ↦ U* X U.

**Theorem 1.4 (The diagonal trace pairing).**

$$\forall iota \in Type,\; [\mathrm{Fintype}\left(iota\right)] [\mathrm{DecidableEq}\left(iota\right)] \forall d \in \mathrm{functions}\left(iota, \mathbb{R}\right),\; \forall X \in \mathrm{HermitianMat}\left(iota, \mathbb{C}\right),\; \mathrm{inner}\left(\mathbb{R}, \mathrm{diagonal}\left(\mathbb{C}, d\right), X\right) = \mathrm{sum}\left(iota, j\mapsto \mathrm{mul}\left(d\left(j\right), \mathrm{re}\left(\mathrm{entry}\left(X, j, j\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/QutritSchurPlane.diagonal_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairing a complex Hermitian matrix X with the real diagonal d gives the sum of d(i) times the real part of X(i,i), over the finite index type.

**Theorem 1.5 (Rank-one projectors lift to original pure states).**

$$\forall V \in Type,\; [\mathrm{NormedAddCommGroup}\left(V\right)] [\mathrm{NormedSpace}\left(\mathbb{R}, V\right)] \forall iota \in Type,\; [\mathrm{Fintype}\left(iota\right)] [\mathrm{DecidableEq}\left(iota\right)] \forall C \in \mathrm{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall J \in \mathrm{Face}\left(C\right),\; \forall I \in \mathrm{LinearMap}\left(\mathbb{R}, \mathrm{HermitianMat}\left(iota, \mathbb{C}\right), V\right),\; \left(\mathrm{Injective}\left(I\right) \land \left(\left(\forall y \in V,\; y \in J \Rightarrow y \in \mathrm{range}\left(I\right)\right) \land \left(\left(\forall X \in \mathrm{HermitianMat}\left(iota, \mathbb{C}\right),\; I\left(X\right) \in J \Leftrightarrow 0 \le X\right) \land \left(\forall X \in \mathrm{HermitianMat}\left(iota, \mathbb{C}\right),\; u\left(I\left(X\right)\right) = \mathrm{trace}\left(X\right)\right)\right)\right)\right) \Rightarrow \left(\forall v \in \mathrm{EuclideanSpace}\left(\mathbb{C}, iota\right),\; \mathrm{norm}\left(v\right) = 1 \Rightarrow I\left(\mathrm{rankOne}\left(v\right)\right) \in \mathrm{pure}\left(C, u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/QutritSchurPlane.unit_rankOne_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a face of the cone C. An injective real-linear map I from complex Hermitian matrices on a finite index type with decidable equality has J in its range, sends a matrix into J exactly when it is positive semidefinite, and satisfies u(I(X)) = trace(X) for every X. For each unit vector v, I sends its rank-one projector to an extreme point of the ambient u = 1 base.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/QutritSchurPlane.diagonal_read`
- Truth anchor: `D5/S3/Quantum/Foundation/QutritSchurPlane.original_qutrit_quotient_affine_plane`
- Truth anchor: `D5/S3/Quantum/Foundation/QutritSchurPlane.reindexEquiv`
- Truth anchor: `D5/S3/Quantum/Foundation/QutritSchurPlane.unit_rankOne_original`
- Truth anchor: `D5/S3/Quantum/Foundation/QutritSchurPlane.unitaryEquiv`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Foundation/QutritPureLift](QutritPureLift.md)
