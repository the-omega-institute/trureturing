# One-port heat does not identify the weighted complete graph

## Abstract

Equal one-port heat for all real times can coexist with full sampled visibility and distinct weighted graph laws.

Both networks have vertex set Fin 4, unit masses, six positive conductances, and excitation and measurement at coordinate 0. In the displayed statement M denotes the Lean matrix reflectedL.

**Definition 1.1 (Matrix space).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.Mat`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real matrices with rows and columns indexed by Fin 4.

**Definition 1.2 (First Laplacian).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.L`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rows of 6L are (25, −11, −8, −6), (−11, 25, −8, −6), (−8, −8, 22, −6), and (−6, −6, −6, 18).

**Definition 1.3 (Port-fixing reflection).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.U`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the column v = (0, 1, 1, −2), the matrix U is the identity minus vvᵀ/3. It fixes coordinate vector e₀ and the all-ones vector.

**Definition 1.4 (Reflected Laplacian).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.reflectedL`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.reflectedL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second Laplacian M is ULUᵀ. The rows of 54M are (225, −78, −51, −96), (−78, 202, −86, −38), (−51, −86, 193, −56), and (−96, −38, −56, 190).

**Definition 1.5 (Weighted complete Laplacian).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.IsK4Laplacian`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.IsK4Laplacian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsK4Laplacian requires symmetry, zero row sums, and strictly negative off-diagonal entries.

**Definition 1.6 (Heat evolution).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.heatStep`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.heatStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a real t the heat matrix for A is the matrix exponential of −tA.

**Definition 1.7 (Scalar heat at the port).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.boundaryHeat`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.boundaryHeat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function heat(A, t) is the (0, 0) entry of the heat matrix.

**Definition 1.8 (Sampled Krylov frame).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.krylovFrame`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.krylovFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Column j of frame(A, h), for j from 0 through 3, is the jth power of the heat matrix at h applied to e₀.

**Definition 1.9 (Edge conductance multiset).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.edgeConductances`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.edgeConductances` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the negatives of the six strictly upper-triangular entries, counting multiplicities.

**Definition 1.10 (Conductance value set).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.conductanceValues`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.conductanceValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take all values −Aᵢⱼ for distinct indices i and j.

**Definition 1.11 (Weighted graph isomorphism).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.IsWeightedIso`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.IsWeightedIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsWeightedIso(A, B) means that some permutation of all four vertices preserves each off-diagonal conductance. The permutation is arbitrary, including its action on vertex 0.

**Theorem 1.12 (Equal heat and full visibility with unequal graph weights).**

$$\operatorname{IsK4Laplacian}\left(L\right) \land \left(\operatorname{IsK4Laplacian}\left(M\right) \land \left(\left(\forall t \in \mathbb{R},\; \operatorname{heat}\left(L, t\right) = \operatorname{heat}\left(M, t\right)\right) \land \left(\left(\forall t \in \mathbb{R},\; \operatorname{heat}\left(L, t\right) = \frac{1}{4} + \frac{\operatorname{exp}\left(-4 \cdot t\right)}{12} + \frac{\operatorname{exp}\left(-5 \cdot t\right)}{6} + \frac{\operatorname{exp}\left(-6 \cdot t\right)}{2}\right) \land \left(\left(\forall h \in \mathbb{R},\; 0 < h \Rightarrow \left(\operatorname{det}\left(\operatorname{frame}\left(L, h\right)\right) \ne 0 \land \operatorname{det}\left(\operatorname{frame}\left(M, h\right)\right) \ne 0\right)\right) \land \left(\operatorname{IsGreatest}\left(\operatorname{conductanceValues}\left(L\right), \frac{11}{6}\right) \land \left(\operatorname{IsGreatest}\left(\operatorname{conductanceValues}\left(M\right), \frac{16}{9}\right) \land \left(\operatorname{edgeConductances}\left(L\right) \ne \operatorname{edgeConductances}\left(M\right) \land \left(\neg \operatorname{IsWeightedIso}\left(L, M\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.boundary_heat_full_visibility_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Florian Dörfler; Francesco Bullo (2013). *Kron Reduction of Graphs With Applications to Electrical Networks*. DOI: [10.1109/TCSI.2012.2215780](https://doi.org/10.1109/TCSI.2012.2215780). URL: <https://arxiv.org/abs/1102.2950>.

*Commentary.*

The proof diagonalizes L with eigenvalues 0, 4, 5 and 6. Their port spectral masses are 1/4, 1/12, 1/6 and 1/2. The matrix exponential respects U-conjugation and U fixes the port, so the scalar curves agree for every real t. For every h > 0 the four heat eigenvalues are distinct. The four columns factor through the eigenbasis, a diagonal of nonzero port coefficients and the Vandermonde matrix on the heat eigenvalues. Conjugation transports the invertible frame to M.

Direct entry checks give strictly positive conductances and zero row sums for each symmetric matrix. The largest conductances are 11/6 for L and 16/9 for M. A weighted isomorphism would preserve that maximum under any vertex permutation, which proves the obstruction even when the port label may move.

The 1966 paper by Ho and Kalman, Effective construction of linear state-variable models from input/output functions, supplies the classical realization context for sampled input-output data. Here the two fully visible realizations are orthogonally equivalent by U. The paper by Dörfler and Bullo supplies electrical-network background on Schur-complement elimination. The displayed result concerns the heat curve, the sampled Krylov frames and the graph weights.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.IsK4Laplacian`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.IsWeightedIso`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.L`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.Mat`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.U`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.boundaryHeat`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.boundary_heat_full_visibility_obstruction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.conductanceValues`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.edgeConductances`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.heatStep`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.krylovFrame`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.reflectedL`
