# Operational reduction of the graph-state encoding

## Abstract

Two distinct logical pure states have exactly the same retained density matrix.

**Definition 1.1 (Normalized dealer slices).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.dealerSlices`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.dealerSlices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Take the complex cast of the integer graph sign for joint configuration (c,a,s) and divide by the complex cast of the real square root of 2 raised to n − 1. The exponent uses natural subtraction. Rows are ordered discarded first and retained second. Columns are dealer bits. For the witness the denominator is 8.

**Definition 1.2 (Encode and take the discarded partial trace).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.reducedEncoding`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.reducedEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Form VρV† using the dealer-slice matrix V and the logical matrix ρ. At retained row a and column b, take the trace of the block with rows (c,a) and columns (c,b). This equals the sum of (VρV†)((c,a),(c,b)) over discarded configurations c.

**Theorem 1.3 (Orthonormal encoding columns).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.witness_encoding_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.witness_encoding_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For the witness, V†V equals the two by two identity. The integer Gram matrix is 64 times the identity and normalization divides it by 64.

**Definition 1.4 (Logical density matrix at the two signs).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logicalDensity`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logicalDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The logical matrix has both diagonal entries 1/2 and both off-diagonal entries sign/2 for a complex sign. The pure-state assertion below concerns the two real signs +1 and −1.

**Theorem 1.5 (Pure logical inputs).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logical_x_pure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logical_x_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For each Boolean selecting the negative sign, there is a vector v in the logical two-dimensional complex space with sum of v(i) times its conjugate equal to one, whose outer product equals the selected logical matrix. These are the projectors onto (|0⟩ + |1⟩)/√2 and (|0⟩ − |1⟩)/√2.

**Theorem 1.6 (Distinct logical matrices).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logical_x_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logical_x_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The logical matrices at +1 and −1 differ at entry (0, 1).

**Theorem 1.7 (Exact equality of the retained states).**

$$\mathit{reducedEncoding}\left(\mathit{witnessGraph}, \mathit{witnessDealer}, \mathit{witnessPlayers}, \mathit{logicalDensity}\left(1\right)\right) = \mathit{reducedEncoding}\left(\mathit{witnessGraph}, \mathit{witnessDealer}, \mathit{witnessPlayers}, \mathit{logicalDensity}\left(-1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.witness_reduced_density_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

On the witness graph with dealer 4 and retained set {2, 5, 6}, the two input projectors give the same partial trace. The two diagonal entries of the input difference vanish, and both off-diagonal entries are one. Each entry of the output difference is the sum of the forward and reverse cross sums divided by 64. The forward sum vanishes by the integer certificate and the reverse sum follows by swapping a with b and commuting the integer factors.

## References

- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.dealerSlices`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logicalDensity`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logical_x_distinct`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.logical_x_pure`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.reducedEncoding`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.witness_encoding_isometry`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.witness_reduced_density_eq`
- Dependency: [D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial](Combinatorial.md)
