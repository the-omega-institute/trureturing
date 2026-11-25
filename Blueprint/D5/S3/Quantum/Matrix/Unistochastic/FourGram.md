# Exact order-four phase completion

## Abstract

Two coupled planar Gram matrices characterize unistochasticity on the closed order-four Birkhoff polytope.

**Definition 1.1 (First row pair).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.q`

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/FourGram.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the real four by four matrix B and column i, qᵢ = B₀ᵢ B₁ᵢ.

**Definition 1.2 (Second row pair).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.p`

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/FourGram.p` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the real four by four matrix B and column i, pᵢ = B₂ᵢ B₃ᵢ.

**Definition 1.3 (The difference of the two phase Grams).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling`

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write the rows of B as vectors a, b, e, f. The coupling C is (aaᵀ + bbᵀ − eeᵀ − ffᵀ)/2 + diag(e + f − 1/2), with the scalar subtracted in every coordinate.

**Definition 1.4 (Feasibility of a common Gram witness).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.CoupledPlanarGrams`

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/FourGram.CoupledPlanarGrams` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exists a real four by four matrix S such that S and S + C are positive semidefinite and each has rank at most two, every row sum of S is zero, and Sᵢᵢ = qᵢ for every i.

**Theorem 1.5 (The second diagonal profile).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For bistochastic B and every i, Cᵢᵢ = pᵢ − qᵢ by the column sum equation.

**Theorem 1.6 (The second Gram also has zero row sums).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling_row_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For bistochastic B and every i, the sum of Cᵢⱼ over j is zero by the row and column sum equations.

**Theorem 1.7 (A unitary supplies the Gram witness).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupledPlanarGrams_of_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupledPlanarGrams_of_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any unitary U of order four, B = normSqMatrix(U) satisfies CoupledPlanarGrams. Take the real Gram matrices of the complex links U₀ⱼ conjugate(U₁ⱼ) and U₂ⱼ conjugate(U₃ⱼ). Each link family sums to zero by row orthogonality. For distinct columns, column orthogonality makes the partial inner products for the two row pairs opposite. Their equal squared moduli give the off-diagonal entries of C, and the link moduli give the diagonal.

**Theorem 1.8 (Reconstruction from the common witness).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.exists_unitary_of_coupledPlanarGrams`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/FourGram.exists_unitary_of_coupledPlanarGrams` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For bistochastic B, CoupledPlanarGrams(B) supplies a unitary U of order four with B = normSqMatrix(U). Factor S in the real plane and take its vectors as complex links. Their sum has squared norm zero. Realize the links with the first two prescribed rows, choosing the second entry freely at a zero first-row weight with its prescribed modulus. The resulting orthonormal rows extend to a unitary.

In the complementary rows, the Bloch vectors have Gram matrix ddᵀ + 4(S + C), where d = e − f. Factor S + C using two real coordinates and append d as the third coordinate after scaling the planar coordinates by two. The resulting vectors and the actual Bloch vectors have equal Gram matrices. An ambient isometry transports the third unit axis to a unit readout axis with inner products dᵢ. A two-row unitary rotation then realizes e, and column normalization supplies f. The factorizations and isometry include planar ranks zero, one and two.

**Theorem 1.9 (The coupled planar Gram criterion).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.unistochastic_iff_coupledPlanarGrams`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/FourGram.unistochastic_iff_coupledPlanarGrams` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

Every order-four bistochastic B is unistochastic exactly when CoupledPlanarGrams(B) holds. Unistochasticity means there exists a complex unitary U of order four with B = RHLinalg.normSqMatrix(U). Zero entries are allowed in every row and column.

Haagerup’s procedure, presented by Rajchel, Gąsiorowski and Życzkowski in arXiv:1804.10715v2, Appendix A, Eqs. (7.1)–(7.5), joins the first row and column quadrilaterals at a common phase and tests one remaining modulus after block completion. The coupled Gram criterion expresses the shared compatibility through two planar Gram matrices and reconstructs the last row pair by an isometry in the Bloch coordinates.

**Definition 1.10 (The third off-diagonal).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.thirdOffdiag`

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/FourGram.thirdOffdiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real x and y, set z = (q₃ − q₀ − q₁ − q₂)/2 − x − y. For a symmetric S with zero row sums and diagonal q, its leading three off-diagonals are x, y, z when S₀₁ = x and S₀₂ = y.

**Definition 1.11 (The first leading determinant).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.cubic`

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/FourGram.cubic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F = q₀q₁q₂ + 2xyz − q₀z² − q₁y² − q₂x² is the determinant of the leading three-by-three block of S.

**Definition 1.12 (The difference of leading determinants).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.conic`

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/FourGram.conic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set A = C₀₁, D = C₀₂ and E = C₁₂. The conic is the determinant with diagonal p₀, p₁, p₂ and off-diagonals x + A, y + D, z + E, minus F.

**Theorem 1.13 (Cancellation of the cubic part).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.conic_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/FourGram.conic_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all B, x and y the difference expands to p₀p₁p₂ − q₀q₁q₂ + 2(Ayz + Dxz + Exy + ADz + AEy + DEx + ADE) − p₀(z + E)² − p₁(y + D)² − p₂(x + A)² + q₀z² + q₁y² + q₂x². Since z is affine in x and y, the degree in those two variables is at most two.

**Definition 1.14 (Two equations with six minor inequalities).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.CubicConicFeasible`

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/FourGram.CubicConicFeasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are real x and y for which the cubic and conic vanish and x² ≤ q₀q₁, y² ≤ q₀q₂, z² ≤ q₁q₂, (x + A)² ≤ p₀p₁, (y + D)² ≤ p₀p₂, and (z + E)² ≤ p₁p₂.

**Theorem 1.15 (The leading blocks determine the full Grams).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupledPlanarGrams_iff_cubicConicFeasible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupledPlanarGrams_iff_cubicConicFeasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order-four bistochastic B, the coupled Gram criterion is equivalent to the cubic and conic feasibility criterion. With nonnegative diagonals, zero determinant and the three principal minors of order two characterize positive semidefiniteness and rank at most two in each leading block. The proof treats a zero pivot separately. Augmenting the blocks by zero row and column sums preserves positivity and the rank bound, and the last diagonal entry of S is fixed by the definition of z.

**Theorem 1.16 (The guarded cubic and conic criterion).**

Lean statement: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.unistochastic_iff_cubicConicFeasible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/FourGram.unistochastic_iff_cubicConicFeasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every order-four bistochastic B is unistochastic exactly when CubicConicFeasible(B) holds. The test concerns a common real solution of both equations and all six inequalities, including zeros of the weights, singular Gram blocks and degenerate conics. It gives a pointwise completion criterion for the flat-star-shapedness question, which asks for feasibility at every point on each segment from the flat matrix to a unistochastic endpoint.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.CoupledPlanarGrams`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.CubicConicFeasible`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.conic`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.conic_expansion`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupledPlanarGrams_iff_cubicConicFeasible`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupledPlanarGrams_of_unitary`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling_diag`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.coupling_row_sum`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.cubic`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.exists_unitary_of_coupledPlanarGrams`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.p`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.q`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.thirdOffdiag`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.unistochastic_iff_coupledPlanarGrams`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/FourGram.unistochastic_iff_cubicConicFeasible`
- Dependency: [D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion](../../../QuadraticForms/RankBoundedChordalPsdCompletion.md)
- Dependency: [D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic](../CirculantBraceletNonUnistochastic.md)
