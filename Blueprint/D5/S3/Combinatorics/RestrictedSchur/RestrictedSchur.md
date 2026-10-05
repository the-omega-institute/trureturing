# A Seven-Block Colouring Refutes the Proposed Eventual Equality

## Abstract

A seven-block three-colouring gives a negative answer to Open Question 6.2 of Gaiser.

**Definition 1.1 (The seven-block three-colouring).**

$$sevenBlockColouring\left(k, n\right) = ite\left(n \le k, 0, ite\left(n \le k^{2} + k, 1, ite\left(n \le k^{2} + 2 \cdot k - 1, 0, ite\left(n \le k^{3} + 2 \cdot k^{2}, 2, ite\left(n \le k^{3} + 2 \cdot k^{2} + k - 1, 0, ite\left(n \le k^{3} + 3 \cdot k^{2} + k - 2, 1, 0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.sevenBlockColouring` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Collier Gaiser (2026). *Restricted generalized Schur numbers*. DOI: [10.48550/arXiv.2608.08789](https://doi.org/10.48550/arXiv.2608.08789). URL: <https://arxiv.org/abs/2608.08789v1>.

*Commentary.*

For integer k and n, the conditions in the nested conditional are evaluated in order; ite selects its second argument when its first argument holds, and its third otherwise. For k at least 3, the seven consecutive blocks in the positive integers have colours 0, 1, 0, 2, 0, 1, 0. The first six right endpoints are k, k^2+k, k^2+2k-1, k^3+2k^2, k^3+2k^2+k-1, and k^3+3k^2+k-2; all larger integers have colour 0.

**Theorem 1.2 (Absence of three-value monochromatic solutions).**

$$\forall k \in Nat,\; 3 \le k \Rightarrow \left(\neg (HasMonochromaticSolution\left(3, k, 2, k^{3} + 3 \cdot k^{2} + 2 \cdot k - 3, n \mapsto sevenBlockColouring\left(k, n\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.sevenBlock_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Collier Gaiser (2026). *Restricted generalized Schur numbers*. DOI: [10.48550/arXiv.2608.08789](https://doi.org/10.48550/arXiv.2608.08789). URL: <https://arxiv.org/abs/2608.08789v1>.

*Commentary.*

For every natural k at least 3, the interval from 1 through k^3+3k^2+2k-3 contains no monochromatic solution with exactly three distinct values under this colouring. The positive summands are smaller than their sum, so a putative solution has exactly two summand values a<b, with multiplicities j and k-j for 1 at most j less than k. For each pair of blocks of the same colour, interval inequalities place ja+(k-j)b in a different colour or beyond the interval.

**Theorem 1.3 (Open Question 6.2 has a negative answer).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.result` (`✓ std3`). ∎

*Resolves.* `Problems/gaiser-restricted-schur-three-colours` (refuted) by `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gaiser-restricted-schur-three-colours","declaration_gid":"D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Collier Gaiser (2026). *Restricted generalized Schur numbers*. DOI: [10.48550/arXiv.2608.08789](https://doi.org/10.48550/arXiv.2608.08789). URL: <https://arxiv.org/abs/2608.08789v1>.

*Commentary.*

There is no natural threshold after which S_3(k;2) always equals k^3+3k^2+k-1. Given a proposed threshold K, take k=max(K,3). The proposed value is positive, so equality would make the set defining the Schur number nonempty and put its least element in that set. The seven-block colouring would then have a solution in the proposed interval. That interval is contained in the larger interval from the preceding theorem, contradicting the absence of such a solution. Here claim denotes the eventual equality defined in RestrictedSchurDefs.

## References

- Truth anchor: `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.result`
- Truth anchor: `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.sevenBlockColouring`
- Truth anchor: `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.sevenBlock_avoids`
- Dependency: [D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs](RestrictedSchurDefs.md)
