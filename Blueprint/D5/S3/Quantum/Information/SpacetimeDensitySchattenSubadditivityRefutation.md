# Temporal Schatten subadditivity is false

## Abstract

A rational pure state of three qubits violates Schatten subadditivity for a qubit observed at two times.

All Fin indices are zero based. Matrix multiplication is written with a star, conjugate transpose with a superscript H (ᴴ), and Matrix.kronecker denotes ⊗ₖ. Matrix.trace is the ordinary trace. A matrix numeral one is the identity on its stated index type. The symbols !![a,b;c,d] and ![a,b] denote a two-by-two matrix and a two-entry vector, respectively. Complex casts and function types are displayed explicitly.

**Definition 1.1 (Conjecture 1: temporal Schatten subadditivity).**

$$\left(\operatorname{claim}\right) \Leftrightarrow \left(\forall \left(a: \operatorname{Type}\right), \left(\forall \left(abar: \operatorname{Type}\right), \left(\forall \left(b: \operatorname{Type}\right), \left(\forall \left(bbar: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(abar\right)] [\operatorname{DecidableEq}\left(abar\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] [\operatorname{Fintype}\left(bbar\right)] [\operatorname{DecidableEq}\left(bbar\right)] \forall \left(rho: \operatorname{Matrix}\left(\left(a \times abar\right), \left(a \times abar\right), \mathbb{C}\right)\right), \left(\forall \left(U: \operatorname{Matrix}\left(\left(b \times bbar\right), \left(a \times abar\right), \mathbb{C}\right)\right), \left(\forall \left(T: \operatorname{Matrix}\left(\left(a \times b\right), \left(a \times b\right), \mathbb{C}\right)\right), \left(\forall \left(p: \mathbb{R}\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(rho\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.trace}\left(rho\right) = 1\right) \Rightarrow \left(\left(\left(\left(U\right)^{\operatorname{H}}\right) * \left(U\right) = 1\right) \Rightarrow \left(\left(\left(U\right) * \left(\left(U\right)^{\operatorname{H}}\right) = 1\right) \Rightarrow \left(\left(\forall \left(OA: \operatorname{Matrix}\left(a, a, \mathbb{C}\right)\right), \left(\forall \left(OB: \operatorname{Matrix}\left(b, b, \mathbb{C}\right)\right), \left(\operatorname{Matrix.trace}\left(\left(T\right) * \left(\operatorname{Matrix.kronecker}\left(OA, OB\right)\right)\right) = \operatorname{Matrix.trace}\left(\left(\left(\left(\left(rho\right) * \left(\operatorname{Matrix.kronecker}\left(OA, \left(1: \operatorname{Matrix}\left(abar, abar, \mathbb{C}\right)\right)\right)\right)\right) * \left(\left(U\right)^{\operatorname{H}}\right)\right) * \left(\operatorname{Matrix.kronecker}\left(OB, \left(1: \operatorname{Matrix}\left(bbar, bbar, \mathbb{C}\right)\right)\right)\right)\right) * \left(U\right)\right)\right)\right)\right) \Rightarrow \left(\left(1 < p\right) \Rightarrow \left(\left(\operatorname{schattenNorm}\left(\operatorname{PartialTraceMutualInformation.partialTraceLeft}\left(T\right), p\right)\right) + \left(\operatorname{schattenNorm}\left(\operatorname{PartialTraceMutualInformation.partialTraceRight}\left(T\right), p\right)\right) \le \left(1\right) + \left(\operatorname{schattenNorm}\left(T, p\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.claim` (`✓ std3`).

*Citation.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

Section IV, item 9, Conjecture 1, equation (25), asserts the displayed inequality for every finite-dimensional spacetime density matrix and every real p > 1. The correlation antecedent is equation (9), with the operator order of equation (4). U is the whole-system evolution from the factorization a × abar at time 0 to b × bbar at time t; the two adjoint equations express its unitarity. The matrix rho is positive semidefinite with trace one. No positivity or Hermiticity is required of T. The operation schattenNorm is footnote a's Schatten norm: the trace of (Mᴴ M)^(p/2), raised to 1/p. PartialTraceMutualInformation.partialTraceLeft traces out a, and PartialTraceMutualInformation.partialTraceRight traces out b.

**Definition 1.2 (A rational qubit vector).**

$$\left(\operatorname{witnessPsi}: \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right) = ![\frac{\left(63: \mathbb{C}\right)}{65}, \frac{\left(16: \mathbb{C}\right)}{65}]$$

*Formalization.* `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessPsi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

The vector has real rational coordinates in the computational basis and squared norm (63² + 16²)/65² = 1. It supplies the qubit amplitudes for the temporal correlation in equations (4) and (9).

**Definition 1.3 (A rational qubit rotation).**

$$\left(\operatorname{witnessV}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right) = !![\frac{\left(4: \mathbb{C}\right)}{5}, \frac{\left(3: \mathbb{C}\right)}{5}; \frac{\left(-3: \mathbb{C}\right)}{5}, \frac{\left(4: \mathbb{C}\right)}{5}]$$

*Formalization.* `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

The real matrix is orthogonal because 4² + 3² = 5² and its columns are orthogonal. Acting on witnessPsi gives the vector (12/13, −5/13).

**Definition 1.4 (The initial three-qubit vector).**

$$\left(\operatorname{witnessJointPsi}: \left(\left(\operatorname{Fin}\left(2\right) \times \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right) \to \mathbb{C}\right)\right) = \lambda \left(x: \left(\operatorname{Fin}\left(2\right) \times \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right)\right) \mapsto \left(\frac{\operatorname{Matrix.mulVec}\left(\left(\operatorname{D5.S3.Quantum.FiniteDimensional.qubitZ}\right)^{\operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(x\right)\right)\right)}, \operatorname{witnessPsi}\right)\left(\operatorname{Prod.fst}\left(x\right)\right)}{2}\right)$$

*Formalization.* `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessJointPsi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

The first coordinate is the observed qubit Q; the other coordinates are the control qubits R and S. For x = (q,(r,s)), the amplitude is (Z^r witnessPsi)_q/2, where D5.S3.Quantum.FiniteDimensional.qubitZ is the diagonal matrix with entries 1 and −1. Summing over the four control sectors gives a unit vector.

**Definition 1.5 (The pure initial density matrix).**

$$\left(\operatorname{witnessRho}: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(2\right) \times \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right), \left(\operatorname{Fin}\left(2\right) \times \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right), \mathbb{C}\right)\right) = \operatorname{PureStateHandshake.rankOneDensity}\left(\operatorname{witnessJointPsi}\right)$$

*Formalization.* `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessRho` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

PureStateHandshake.rankOneDensity takes the outer product of a vector with its conjugate. Thus this density matrix is positive semidefinite and has trace one on Q × (R × S).

**Definition 1.6 (The controlled rotation blocks).**

$$\left(\operatorname{witnessBlock}: \left(\left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right) = \lambda \left(c: \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\left(\left(\left(\operatorname{D5.S3.Quantum.FiniteDimensional.qubitZ}\right)^{\operatorname{Fin.val}\left(\operatorname{Prod.snd}\left(c\right)\right)}\right) * \left(\operatorname{witnessV}\right)\right) * \left(\left(\operatorname{D5.S3.Quantum.FiniteDimensional.qubitZ}\right)^{\operatorname{Fin.val}\left(\operatorname{Prod.fst}\left(c\right)\right)}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

For the control values c = (r,s), the block is Z^s witnessV Z^r. The phase before the rotation depends on R, and the phase after it depends on S. Every block is unitary.

**Definition 1.7 (The whole-system controlled evolution).**

$$\left(\operatorname{witnessU}: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(2\right) \times \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right), \left(\operatorname{Fin}\left(2\right) \times \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right), \mathbb{C}\right)\right) = \operatorname{Matrix.blockDiagonal}\left(\operatorname{witnessBlock}\right)$$

*Formalization.* `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessU` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

Matrix.blockDiagonal acts on Q × (R × S), with one qubit block for each pair of control values. It leaves both control coordinates fixed and applies the corresponding block to Q.

**Definition 1.8 (The diagonal spacetime matrix).**

$$\left(\operatorname{witnessT}: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right), \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right)\right) = \operatorname{Matrix.diagonal}\left(\lambda \left(x: \left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\frac{\left(!![\left(3024: \mathbb{C}\right), 945; 576, -320]\right)\left(\operatorname{Prod.fst}\left(x\right), \operatorname{Prod.snd}\left(x\right)\right)}{4225}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

The row and column index is the pair of observed qubit values at times 0 and t. The four diagonal entries, in order (0,0), (0,1), (1,0), (1,1), are 3024/4225, 945/4225, 576/4225 and −320/4225. Their sum is one. The negative last entry prevents this spacetime matrix from being a positive density matrix.

**Theorem 1.9 (The three-qubit example contradicts Conjecture 1).**

$$\neg \left(\operatorname{claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/milekhin-adamska-preskill-2025-spacetime-schatten-subadditivity` (refuted) by `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"milekhin-adamska-preskill-2025-spacetime-schatten-subadditivity","declaration_gid":"D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alexey Milekhin; Zofia Adamska; John Preskill (2025). *Observable and computable entanglement in time*. URL: <https://arxiv.org/abs/2502.12240v2>.

*Commentary.*

A and B are the same qubit Q at times 0 and t, with R and S as its complement at both times. The two control qubits dephase the observable insertions at both ends of the correlation. Writing psi = witnessPsi and V = witnessV, the resulting Kirkwood–Dirac weights are q(i,j) = psi(i) V(j,i) (V psi)(j). They are the four diagonal entries of witnessT. The initial density matrix and the controlled evolution satisfy equation (9) for all qubit observables in the order of equation (4). The left partial trace is diag(144/169,25/169), and the right partial trace is diag(3969/4225,256/4225). At p = 2, schattenNorm(witnessT,2) = sqrt(10471777/17850625), the left marginal norm is sqrt(21361/28561), and the right marginal norm is sqrt(15818497/17850625). Consequently 1 + schattenNorm(witnessT,2) ≤ 177/100 < 180/100 ≤ sqrt(21361/28561) + sqrt(15818497/17850625), contradicting the proposed inequality.

## References

- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessBlock`
- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessJointPsi`
- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessPsi`
- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessRho`
- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessT`
- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessU`
- Truth anchor: `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.witnessV`
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation](ChenKatoBrandaoCMIRefutation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](../QuantumChannels/TwoPositiveTransitionTrace.md)
- Dependency: [D5/S3/Quantum/Schatten/Holder](../Schatten/Holder.md)
