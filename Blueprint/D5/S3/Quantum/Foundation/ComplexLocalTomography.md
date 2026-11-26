# Complex local tomography and two-particle exchange

## Abstract

Bipartite dimension counts and separation by local product observables.

**Definition 1.1 (Dyson dimension).**

$$\forall K \in Type,\; [\mathrm{Field}\left(K\right)] \forall b \in K,\; \forall d \in K,\; \mathrm{dysonDim}\left(b, d\right) = d + \frac{b}{2} \cdot d \cdot \left(d - 1\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/ComplexLocalTomography.dysonDim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parameter d counts diagonal entries. The index b counts real coordinates per unordered off-diagonal pair.

**Theorem 1.2 (Factored bipartite dimension gap).**

$$\forall K \in Type,\; [\mathrm{Field}\left(K\right)] [\mathrm{CharZero}\left(K\right)] \forall b \in K,\; \forall x \in K,\; \forall y \in K,\; \mathrm{dysonDim}\left(b, x \cdot y\right) - \mathrm{dysonDim}\left(b, x\right) \cdot \mathrm{dysonDim}\left(b, y\right) = \frac{b \cdot \left(2 - b\right)}{4} \cdot x \cdot y \cdot \left(x - 1\right) \cdot \left(y - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ComplexLocalTomography.dyson_bipartite_dimension_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract the product of the local counts from the count at the composite size and factor the difference over a field of characteristic zero.

**Theorem 1.3 (Multiplicativity at the classical and complex indices).**

$$\forall K \in Type,\; [\mathrm{Field}\left(K\right)] [\mathrm{CharZero}\left(K\right)] \forall b \in K,\; \forall x \in \mathbb{N},\; \forall y \in \mathbb{N},\; \left(2 \le x \land 2 \le y\right) \Rightarrow \left(\mathrm{dysonDim}\left(b, x \cdot y\right) = \mathrm{dysonDim}\left(b, x\right) \cdot \mathrm{dysonDim}\left(b, y\right) \Leftrightarrow \left(b = 0 \lor b = 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ComplexLocalTomography.dyson_local_tomography_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For integer sizes at least two, each size factor in the gap is nonzero. The classical index zero and the complex index two exhaust the vanishing cases.

**Theorem 1.4 (Sign and size of the gap).**

$$\forall b \in \mathbb{R},\; \forall x \in \mathbb{N},\; \forall y \in \mathbb{N},\; \left(2 \le x \land 2 \le y\right) \Rightarrow \left(\left(\left(\left(\left(0 < \mathrm{dysonDim}\left(b, x \cdot y\right) - \mathrm{dysonDim}\left(b, x\right) \cdot \mathrm{dysonDim}\left(b, y\right) \Leftrightarrow \left(0 < b \land b < 2\right)\right) \land \left(\mathrm{dysonDim}\left(b, x \cdot y\right) - \mathrm{dysonDim}\left(b, x\right) \cdot \mathrm{dysonDim}\left(b, y\right) = 0 \Leftrightarrow \left(b = 0 \lor b = 2\right)\right)\right) \land \left(\mathrm{dysonDim}\left(b, x \cdot y\right) - \mathrm{dysonDim}\left(b, x\right) \cdot \mathrm{dysonDim}\left(b, y\right) < 0 \Leftrightarrow \left(b < 0 \lor 2 < b\right)\right)\right) \land \mathrm{dysonDim}\left(1, x \cdot y\right) - \mathrm{dysonDim}\left(1, x\right) \cdot \mathrm{dysonDim}\left(1, y\right) = \frac{x \cdot \left(x - 1\right)}{2} \cdot \frac{y \cdot \left(y - 1\right)}{2}\right) \land \mathrm{dysonDim}\left(4, x \cdot y\right) - \mathrm{dysonDim}\left(4, x\right) \cdot \mathrm{dysonDim}\left(4, y\right) = -2 \cdot x \cdot y \cdot \left(x - 1\right) \cdot \left(y - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ComplexLocalTomography.dyson_sign_trichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The size factors are positive. At index one the real count exceeds the product by the product of the skew dimensions. At index four the quaternionic count falls below the product by twice the product of the four size factors.

**Theorem 1.5 (A symmetric tensor orthogonal to real product tests).**

$$\forall X \in Type,\; [\mathrm{Fintype}\left(X\right)] \forall Y \in Type,\; [\mathrm{Fintype}\left(Y\right)] \forall S \in \mathrm{Matrix}\left(X, X, \mathbb{R}\right),\; \forall A \in \mathrm{Matrix}\left(X, X, \mathbb{R}\right),\; \forall T \in \mathrm{Matrix}\left(Y, Y, \mathbb{R}\right),\; \forall B \in \mathrm{Matrix}\left(Y, Y, \mathbb{R}\right),\; \left(\left(\left(\mathrm{transpose}\left(S\right) = -S \land \mathrm{transpose}\left(T\right) = -T\right) \land \mathrm{transpose}\left(A\right) = A\right) \land \mathrm{transpose}\left(B\right) = B\right) \Rightarrow \left(\mathrm{transpose}\left(\mathrm{kron}\left(S, T\right)\right) = \mathrm{kron}\left(S, T\right) \land \mathrm{tr}\left(\mathrm{kron}\left(S, T\right) \cdot \mathrm{kron}\left(A, B\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ComplexLocalTomography.real_skew_kron_orthogonal_to_symmetric_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposition negates each skew factor and thereby fixes their Kronecker product. Each local trace of a skew factor times a symmetric test is its own negative. The Kronecker trace factors into those local traces.

**Theorem 1.6 (Orthogonal two-rebit states with equal local statistics).**

$$\forall J \in \mathrm{Matrix}\left(\mathrm{Fin}\left(2\right), \mathrm{Fin}\left(2\right), \mathbb{R}\right),\; \forall W \in \mathrm{Matrix}\left(\mathrm{Fin}\left(2\right) \times \mathrm{Fin}\left(2\right), \mathrm{Fin}\left(2\right) \times \mathrm{Fin}\left(2\right), \mathbb{R}\right),\; \forall U \in \mathrm{Matrix}\left(\mathrm{Fin}\left(2\right) \times \mathrm{Fin}\left(2\right), \mathrm{Fin}\left(2\right) \times \mathrm{Fin}\left(2\right), \mathbb{R}\right),\; \forall V \in \mathrm{Matrix}\left(\mathrm{Fin}\left(2\right) \times \mathrm{Fin}\left(2\right), \mathrm{Fin}\left(2\right) \times \mathrm{Fin}\left(2\right), \mathbb{R}\right),\; \left(\left(\left(J = \mathrm{matrixTwo}\left(0, -1, 1, 0\right) \land W = \mathrm{kron}\left(J, J\right)\right) \land U = \frac{1}{4} \cdot \left(1 + W\right)\right) \land V = \frac{1}{4} \cdot \left(1 - W\right)\right) \Rightarrow \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\mathrm{transpose}\left(W\right) = W \land W \cdot W = 1\right) \land \mathrm{tr}\left(W\right) = 0\right) \land W \ne 0\right) \land U \ne V\right) \land \mathrm{transpose}\left(U\right) = U\right) \land \mathrm{transpose}\left(V\right) = V\right) \land \mathrm{tr}\left(U\right) = 1\right) \land \mathrm{tr}\left(V\right) = 1\right) \land U \cdot V = 0\right) \land U \cdot U = \frac{1}{2} \cdot U\right) \land V \cdot V = \frac{1}{2} \cdot V\right) \land \mathrm{PSD}\left(U\right)\right) \land \mathrm{PSD}\left(V\right)\right) \land \left(\forall A \in \mathrm{Matrix}\left(\mathrm{Fin}\left(2\right), \mathrm{Fin}\left(2\right), \mathbb{R}\right),\; \forall B \in \mathrm{Matrix}\left(\mathrm{Fin}\left(2\right), \mathrm{Fin}\left(2\right), \mathbb{R}\right),\; \left(\mathrm{transpose}\left(A\right) = A \land \mathrm{transpose}\left(B\right) = B\right) \Rightarrow \mathrm{tr}\left(U \cdot \mathrm{kron}\left(A, B\right)\right) = \mathrm{tr}\left(V \cdot \mathrm{kron}\left(A, B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ComplexLocalTomography.two_rebit_hidden_orthogonal_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write J for the real two-by-two matrix with rows (0, -1) and (1, 0). Write W for its Kronecker square and U and V for one fourth of I + W and I - W. These are real four-by-four matrices indexed by pairs of two coordinates. The half-scaled square identities and symmetry give positive semidefiniteness. The product traces agree for every pair of symmetric local tests.

**Theorem 1.7 (Complex product tests separate matrices).**

$$\forall X \in Type,\; [\mathrm{Fintype}\left(X\right)] \forall Y \in Type,\; [\mathrm{Fintype}\left(Y\right)] \forall M \in \mathrm{Matrix}\left(X \times Y, X \times Y, \mathbb{C}\right),\; \forall N \in \mathrm{Matrix}\left(X \times Y, X \times Y, \mathbb{C}\right),\; \left(\forall A \in \mathrm{Matrix}\left(X, X, \mathbb{C}\right),\; \forall B \in \mathrm{Matrix}\left(Y, Y, \mathbb{C}\right),\; \left(\mathrm{adj}\left(A\right) = A \land \mathrm{adj}\left(B\right) = B\right) \Rightarrow \mathrm{tr}\left(M \cdot \mathrm{kron}\left(A, B\right)\right) = \mathrm{tr}\left(N \cdot \mathrm{kron}\left(A, B\right)\right)\right) \Leftrightarrow M = N$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ComplexLocalTomography.complex_local_tomography_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate index types X and Y may be empty. Each complex local matrix is its Hermitian real part plus the imaginary unit times its Hermitian imaginary part. Bilinearity extends equality of traces to arbitrary product factors. Tensor products of transposed local matrix units then probe each individual matrix entry.

**Definition 1.8 (Normalized trace extension on the extra summand).**

$$\forall X \in Type,\; [\mathrm{Fintype}\left(X\right)] \forall Y \in Type,\; [\mathrm{Fintype}\left(Y\right)] \forall Z \in Type,\; [\mathrm{DecidableEq}\left(Z\right)] \forall A \in \mathrm{Matrix}\left(X, X, \mathbb{C}\right),\; \forall B \in \mathrm{Matrix}\left(Y, Y, \mathbb{C}\right),\; \mathrm{T}\left(Z, A, B\right) = \mathrm{block}\left(\mathrm{kron}\left(A, B\right), 0, 0, \frac{\mathrm{tr}\left(A\right)}{\mathrm{card}\left(X\right)} \cdot \frac{\mathrm{tr}\left(B\right)}{\mathrm{card}\left(Y\right)} \cdot \mathrm{identity}\left(Z\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/ComplexLocalTomography.darkProductExt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here T denotes darkProductExt and card denotes the finite cardinality. The visible block is the product test. The dark block is the identity on Z scaled by the product of the two normalized traces. Division by zero is zero here, as in the complex field operations in Lean. If either local carrier is empty, the extension is the zero matrix.

**Theorem 1.9 (Orthogonal states with the same normalized trace readout).**

$$\forall X \in Type,\; [\mathrm{Fintype}\left(X\right)] [\mathrm{DecidableEq}\left(X\right)] [\mathrm{Nonempty}\left(X\right)] \forall Y \in Type,\; [\mathrm{Fintype}\left(Y\right)] [\mathrm{DecidableEq}\left(Y\right)] [\mathrm{Nonempty}\left(Y\right)] \forall Z \in Type,\; [\mathrm{Fintype}\left(Z\right)] [\mathrm{DecidableEq}\left(Z\right)] \forall r \in Z,\; \forall s \in Z,\; r \ne s \Rightarrow \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\mathrm{T}\left(Z, 1, 1\right) = 1 \land \left(\forall A \in \mathrm{Matrix}\left(X, X, \mathbb{C}\right),\; \forall B \in \mathrm{Matrix}\left(Y, Y, \mathbb{C}\right),\; \mathrm{adj}\left(\mathrm{T}\left(Z, A, B\right)\right) = \mathrm{T}\left(Z, \mathrm{adj}\left(A\right), \mathrm{adj}\left(B\right)\right)\right)\right) \land \left(\forall M \in \mathrm{Matrix}\left(X \times Y, X \times Y, \mathbb{C}\right),\; \forall A \in \mathrm{Matrix}\left(X, X, \mathbb{C}\right),\; \forall B \in \mathrm{Matrix}\left(Y, Y, \mathbb{C}\right),\; \mathrm{tr}\left(\mathrm{block}\left(M, 0, 0, 0\right) \cdot \mathrm{T}\left(Z, A, B\right)\right) = \mathrm{tr}\left(M \cdot \mathrm{kron}\left(A, B\right)\right)\right)\right) \land \mathrm{E}\left(r\right) \ne \mathrm{E}\left(s\right)\right) \land \mathrm{adj}\left(\mathrm{E}\left(r\right)\right) = \mathrm{E}\left(r\right)\right) \land \mathrm{adj}\left(\mathrm{E}\left(s\right)\right) = \mathrm{E}\left(s\right)\right) \land \mathrm{tr}\left(\mathrm{E}\left(r\right)\right) = 1\right) \land \mathrm{tr}\left(\mathrm{E}\left(s\right)\right) = 1\right) \land \mathrm{PSD}\left(\mathrm{E}\left(r\right)\right)\right) \land \mathrm{PSD}\left(\mathrm{E}\left(s\right)\right)\right) \land \mathrm{E}\left(r\right) \cdot \mathrm{E}\left(s\right) = 0\right) \land \left(\forall A \in \mathrm{Matrix}\left(X, X, \mathbb{C}\right),\; \forall B \in \mathrm{Matrix}\left(Y, Y, \mathbb{C}\right),\; \mathrm{tr}\left(\mathrm{E}\left(r\right) \cdot \mathrm{T}\left(Z, A, B\right)\right) = \mathrm{tr}\left(\mathrm{E}\left(s\right) \cdot \mathrm{T}\left(Z, A, B\right)\right) \land \mathrm{tr}\left(\mathrm{E}\left(r\right) \cdot \mathrm{T}\left(Z, A, B\right)\right) = \mathrm{tr}\left(\frac{1}{\mathrm{card}\left(X\right) \cdot \mathrm{card}\left(Y\right)} \cdot 1 \cdot \mathrm{kron}\left(A, B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ComplexLocalTomography.dark_sector_product_indistinguishable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take finite X, Y and Z with X and Y nonempty. For a dark index z, E(z) is the diagonal matrix unit at z on the direct sum. The extension T preserves the unit, adjoints and all visible pairings. Two distinct dark coordinate states both yield the statistics of the maximally mixed visible state for every product test.

**Theorem 1.10 (Symmetric and alternating exchange projections).**

$$\forall X \in Type,\; \forall S \in \mathrm{End}\left(X \times X, \mathbb{C}\right),\; \forall P \in \mathrm{End}\left(X \times X, \mathbb{C}\right),\; \forall Q \in \mathrm{End}\left(X \times X, \mathbb{C}\right),\; \left(\left(S = \mathrm{swap}\left(X\right) \land P = \frac{1}{2} \cdot \left(id + S\right)\right) \land Q = \frac{1}{2} \cdot \left(id - S\right)\right) \Rightarrow \left(\left(\left(\left(\left(\left(\left(P + Q = id \land P \circ Q = 0\right) \land Q \circ P = 0\right) \land P \circ P = P\right) \land Q \circ Q = Q\right) \land S \circ P = P\right) \land S \circ Q = -Q\right) \land \left(\forall v \in X \to \mathbb{C},\; v \ne 0 \Rightarrow \left(\left(\mathrm{Q}\left(\mathrm{squareTensor}\left(v\right)\right) = 0 \land \mathrm{P}\left(\mathrm{squareTensor}\left(v\right)\right) = \mathrm{squareTensor}\left(v\right)\right) \land \mathrm{squareTensor}\left(v\right) \ne 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ComplexLocalTomography.two_particle_exchange_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On V = X × X → C, let S interchange the two coordinates and P and Q be one half of id + S and id - S. The images have exchange eigenvalues +1 and -1. For w(i,j) = v(i)v(j), commutativity fixes w under S, and a nonzero coordinate v(i) gives a nonzero diagonal coordinate w(i,i).

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.complex_local_tomography_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.darkProductExt`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.dark_sector_product_indistinguishable`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.dysonDim`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.dyson_bipartite_dimension_gap`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.dyson_local_tomography_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.dyson_sign_trichotomy`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.real_skew_kron_orthogonal_to_symmetric_products`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.two_particle_exchange_decomposition`
- Truth anchor: `D5/S3/Quantum/Foundation/ComplexLocalTomography.two_rebit_hidden_orthogonal_states`
