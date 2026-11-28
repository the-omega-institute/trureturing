# Signed C5 transfer reflection

## Abstract

The signed five-cycle transfer has an exact scalar reflection product.

**Definition 1.1 (Cycle anticommutation sign).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5TransferReflection.cycleSign`

*Formalization.* `D5/S3/Quantum/Fermionic/WuC5TransferReflection.cycleSign` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The cyclic edge relation contributes −1 and every nonedge contributes +1, including the equal-site convention. The independent pairs are directed by the step-two word BᵢBᵢ₊₂.

**Theorem 1.2 (Five-cycle word squares).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5TransferReflection.word_squares`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuC5TransferReflection.word_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For letters in an algebra over a commutative ring with these signs and arbitrary central scalar squares, the square of the linear word is the sum of the scalar squares plus twice the sum of the five independent-pair words. The square of the pair-word sum is scalar because the five pair words anticommute, while the crossing counts are 3, 1, 1, 3.

**Theorem 1.3 (Exact transfer reflection).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5TransferReflection.transfer_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuC5TransferReflection.transfer_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A SignedCycle consists of five base involutions with the cycle signs and five commuting occupation involutions, each anticommuting only with its own base involution. The grouped transfer collects the empty base word, the five singletons, and the five independent pairs, with unused occupation factors retained.

Multiplying the transfer at z and −z gives the scalar reflection polynomial for arbitrary real weights and every complex z. Away from the occupation denominator zeros, the proof factors the transfer into a dressed C5 word and the product of occupation factors. It moves that product through the dressed word at −z, combines the resulting scalar factors, and extends the identity across the finite exceptional set by continuity.

**Theorem 1.4 (Common occupation factor).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5TransferReflection.transfer_reflection_common`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuC5TransferReflection.transfer_reflection_common` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When all occupation weights equal a₀, writing l = 1 − a₀²z², S = sumᵢ tᵢ², and D = sumᵢ tᵢ²tᵢ₊₂², the reflection scalar is l³(l² − z²lS + z⁴D). The linear coefficient is the weighted base Hamiltonian plus the common occupation field, and the constant coefficient is I.

Elman, Chapman, and Flammia (arXiv:2012.07857, Lemma 2) give the bare transfer inversion for even-hole-free, claw-free graphs and compute the bare C5 scalar in Eq. (100). The occupation-decorated graph contains a claw whose center is a base site and whose leaves are its two cycle neighbors and its private occupation vertex. The dressed occupation extension is proved in transfer_reflection.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5TransferReflection.cycleSign`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5TransferReflection.transfer_reflection`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5TransferReflection.transfer_reflection_common`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5TransferReflection.word_squares`
- Dependency: [D5/S3/HilbertOperators/WuTransferReflectionBound](../../HilbertOperators/WuTransferReflectionBound.md)
