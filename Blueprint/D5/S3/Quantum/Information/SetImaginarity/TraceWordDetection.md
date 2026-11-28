# A quaternionic obstruction to a common real basis

## Abstract

Every ordered trace word can be real even when four states have no common real basis.

**Definition 1.1 (Real traces as a sufficiency condition).**

Lean statement: `D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.claim`

*Formalization.* `D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yu Guo, Jiabo Pan, Yuqin Wang, Shuanping Du (2026). *Measure of set imaginarity*. DOI: [10.1103/1yc6-lzfk](https://doi.org/10.1103/1yc6-lzfk). URL: <https://arxiv.org/abs/2608.28985v1>.

*Commentary.*

The assertion quantifies over every injective family of four positive semidefinite trace-one complex matrices, with rows and columns indexed by the disjoint union of two copies of Fin 2. It says that if every ordered trace word has imaginary part zero, for every natural length and every choice of letters, then one unitary makes all four states entrywise real. The introduction and Appendix C suggest a detection criterion whose sufficiency direction uses only the bounded window. Replacing that premise by reality of all trace words gives the separate implication tested here.

**Theorem 1.2 (Four positive definite states refute sufficiency).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yu Guo, Jiabo Pan, Yuqin Wang, Shuanping Du (2026). *Measure of set imaginarity*. DOI: [10.1103/1yc6-lzfk](https://doi.org/10.1103/1yc6-lzfk). URL: <https://arxiv.org/abs/2608.28985v1>.

*Commentary.*

Take the Pauli matrices X, Y, Z, with the upper right entry of Y equal to minus i. In the ordered tensor basis, use the four Hermitian involutions Z tensor I, X tensor I, Y tensor X and Y tensor Z. For each such G take the state (2I + G)/8. Their entries distinguish them, and their traces are one because each G is traceless. Each state is I/8 plus the Gram matrix of I + G scaled by 1/16, hence is positive definite.

Let J have rows (0, 1) and (-1, 0), and let Q be block diagonal with two copies of J. Each state intertwines its entrywise conjugate via Q. Induction on ordered words preserves the intertwining equation. Since the inverse of Q is minus Q, cyclicity of trace then shows every word has trace equal to its complex conjugate.

If a unitary U made all four states real, the product of its adjoint with its entrywise conjugate would be a symmetric unitary C intertwining all four generators with their conjugates. The first generator forces both off-diagonal blocks of C to vanish. The second forces the diagonal blocks to be equal. The third and fourth force their common block to anticommute with X and Z. Anticommutation with Z gives zero diagonal entries, and anticommutation with X gives opposite off-diagonal entries. Thus C is a scalar multiple of Q, which is skew-symmetric. Symmetry then forces C to vanish, contradicting unitarity.

All words in the dimension-four window from three to ten have real trace, so the same family refutes the inferred bounded sufficiency direction. Any restriction to words with distinct letters also retains this counterexample. The earlier work of Miyazaki and Matsumoto on antiunitary symmetries is related literature.

## References

- Truth anchor: `D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.claim`
- Truth anchor: `D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.result`
- Dependency: [D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture](PrintedConjecture.md)
