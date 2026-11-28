# The printed set imaginarity conjecture

## Abstract

Three distinct diagonal qubit states refute the biconditional printed as Conjecture 1.

**Definition 1.1 (One common real basis).**

Lean statement: `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.CommonRealBasis`

*Formalization.* `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.CommonRealBasis` (`✓ std3`).

*Citation.* Yu Guo, Jiabo Pan, Yuqin Wang, Shuanping Du (2026). *Measure of set imaginarity*. DOI: [10.1103/1yc6-lzfk](https://doi.org/10.1103/1yc6-lzfk). URL: <https://arxiv.org/abs/2608.28985v1>.

*Commentary.*

For a family indexed by Fin n of complex square matrices on a finite decidable index type, there exists a single unitary U such that every entry of U times the j-th matrix times the adjoint of U has imaginary part zero, for every j and every pair of row and column indices.

**Definition 1.2 (Trace of an ordered word).**

Lean statement: `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.traceWord`

*Formalization.* `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.traceWord` (`✓ std3`).

*Citation.* Yu Guo, Jiabo Pan, Yuqin Wang, Shuanping Du (2026). *Measure of set imaginarity*. DOI: [10.1103/1yc6-lzfk](https://doi.org/10.1103/1yc6-lzfk). URL: <https://arxiv.org/abs/2608.28985v1>.

*Commentary.*

For a family indexed by Fin n and a word w from Fin k to Fin n, take the ordinary complex trace of the product of the states selected by w, in increasing position order. The empty product is the identity. Word positions may select the same state.

**Definition 1.3 (Conjecture 1 as printed).**

Lean statement: `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.claim`

*Formalization.* `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.claim` (`✓ std3`).

*Citation.* Yu Guo, Jiabo Pan, Yuqin Wang, Shuanping Du (2026). *Measure of set imaginarity*. DOI: [10.1103/1yc6-lzfk](https://doi.org/10.1103/1yc6-lzfk). URL: <https://arxiv.org/abs/2608.28985v1>.

*Commentary.*

For all natural d at least two and n at least three, take an injective family of n positive semidefinite complex d by d matrices of trace one. The asserted biconditional equates existence of a common real basis with existence of an ordered word whose trace has nonzero imaginary part, with natural length k between three and the natural quotient d(d+1)/2 inclusive.

**Theorem 1.4 (Diagonal qubit counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.result` (`✓ std3`). ∎

*Resolves.* `Problems/guo-pan-wang-du-2026-set-imaginarity-conjecture-1` (refuted) by `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"guo-pan-wang-du-2026-set-imaginarity-conjecture-1","declaration_gid":"D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yu Guo, Jiabo Pan, Yuqin Wang, Shuanping Du (2026). *Measure of set imaginarity*. DOI: [10.1103/1yc6-lzfk](https://doi.org/10.1103/1yc6-lzfk). URL: <https://arxiv.org/abs/2608.28985v1>.

*Commentary.*

Use the diagonal states with diagonal entries (3/4, 1/4), (1/4, 3/4) and (1/2, 1/2). Their first entries distinguish them, and their diagonals are positive and sum to one. The identity is a common unitary. The inclusion from real matrices to complex matrices preserves ordered products and trace, so every trace word is real. The window at dimension two has length three, and every word in that window therefore has zero imaginary trace. The counterexample falsifies the direction from a common real basis to a nonreal trace word in the printed biconditional.

## References

- Truth anchor: `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.CommonRealBasis`
- Truth anchor: `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.claim`
- Truth anchor: `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.result`
- Truth anchor: `D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.traceWord`
