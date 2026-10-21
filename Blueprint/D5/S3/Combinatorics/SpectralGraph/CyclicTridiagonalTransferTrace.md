# Cyclic tridiagonal determinants and transfer traces

## Abstract

A cyclic Jacobi determinant and its two-dimensional transfer evolution.

**Definition 1.1 (Cyclic tridiagonal matrix).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall N \in \operatorname{Nat},\; \forall d \in \operatorname{Nat} \to R,\; \operatorname{cycleDiag}\left(N, d\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(\lambda i: \operatorname{Fin}\left(N\right) \mapsto d\left(\operatorname{val}\left(i\right)\right)\right) - \operatorname{SimpleGraph}.\operatorname{adjMatrix}\left(\operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(N\right), R\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.cycleDiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal potential matrix minus the adjacency matrix of the cycle graph. The determinant identity concerns sizes at least three.

**Theorem 1.2 (Entries of the cyclic matrix).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall n \in \operatorname{Nat},\; \forall d \in \operatorname{Nat} \to R,\; \forall i \in \operatorname{Fin}\left(n + 3\right),\; \forall j \in \operatorname{Fin}\left(n + 3\right),\; \operatorname{cycleDiag}\left(n + 3, d\right)\left(i, j\right) = \operatorname{if} (i = j) \operatorname{then} d\left(\operatorname{val}\left(i\right)\right) \operatorname{else} \operatorname{if} (\operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(i\right) + 1, n + 3\right) = \operatorname{val}\left(j\right) \lor \operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(j\right) + 1, n + 3\right) = \operatorname{val}\left(i\right)) \operatorname{then} -(1) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.cycleDiag_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For sizes at least three, the diagonal entries are d, cyclic off-diagonal entries are minus one, and all remaining entries are zero.

**Definition 1.3 (One transfer step).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Ring}\left(K\right)] \forall d \in K,\; \operatorname{transfer}\left(d\right) = \begin{pmatrix}d&-(1)\\1&0\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two coordinates carry consecutive values of a second-order recurrence.

**Definition 1.4 (Ordered transfer product).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Ring}\left(K\right)] \forall d \in \operatorname{Nat} \to K,\; \operatorname{evolution}\left(d, 0\right) = 1 \land (\forall n \in \operatorname{Nat},\; \operatorname{evolution}\left(d, n + 1\right) = \operatorname{transfer}\left(d\left(n\right)\right) \cdot \operatorname{evolution}\left(d, n\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.evolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion multiplies the next step on the left. The variable n in the successor branch is bound by that pattern.

**Theorem 1.5 (Determinant of one step).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall x \in R,\; \operatorname{Matrix}.\operatorname{det}\left(\operatorname{transfer}\left(x\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.transfer_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every transfer step has determinant one; this also determines the determinant of a finite product.

**Theorem 1.6 (Splitting the transfer evolution).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Ring}\left(K\right)] \forall d \in \operatorname{Nat} \to K,\; \forall n \in \operatorname{Nat},\; \forall k \in \operatorname{Nat},\; \operatorname{evolution}\left(d, n + k\right) = \operatorname{evolution}\left(\lambda i: \operatorname{Nat} \mapsto d\left(n + i\right), k\right) \cdot \operatorname{evolution}\left(d, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.evolution_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splitting a sequence after n steps puts the later k steps on the left.

**Theorem 1.7 (Determinant of the evolution).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall d \in \operatorname{Nat} \to R,\; \forall n \in \operatorname{Nat},\; \operatorname{Matrix}.\operatorname{det}\left(\operatorname{evolution}\left(d, n\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.evolution_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplicativity of the determinant and induction preserve determinant one.

**Theorem 1.8 (The cyclic determinant identity).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] \forall n \in \operatorname{Nat},\; \forall d \in \operatorname{Nat} \to R,\; \operatorname{Matrix}.\operatorname{det}\left(\operatorname{cycleDiag}\left(n + 3, d\right)\right) = \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{evolution}\left(d, n + 3\right)\right) - 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.cycleDiag_det_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Impulse solutions form a lower unitriangular matrix. Multiplication reduces all interior rows to coordinate rows and leaves a two by two boundary block. Its determinant is the negative cyclic determinant. The two impulse solutions also give the entries of the transfer product, whose determinant is one; the boundary determinant consequently equals two minus the trace. These identities hold over every commutative ring.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.cycleDiag`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.cycleDiag_apply`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.cycleDiag_det_transfer`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.evolution`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.evolution_add`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.evolution_det`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.transfer`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.transfer_det`
