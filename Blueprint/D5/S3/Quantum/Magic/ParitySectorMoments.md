# Parity-sector Clifford reduction and diagonal cosine fourth moments

## Abstract

Qudit parity sectors in odd dimensions, canonical orthonormal frames and projectors, parity-commuting Clifford reduction of Weyl labels to pure clock powers, diagonal cosine compressions and power sums, and closed-form Haar fourth moments of nonzero Weyl labels.

**Definition 1.1 (Qudit parity operator).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.parityMatrix`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.parityMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a natural dimension d, parityMatrix(d) is the permutation matrix P |j> = |-j> acting on C^d indexed by Z / dZ.

**Definition 1.2 (Even parity subspace).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.evenSectorSubspace`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.evenSectorSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension d, evenSectorSubspace(d) = ker(P - I) is the +1 eigenspace E_d of the parity operator in C^d.

**Definition 1.3 (Odd parity subspace).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.oddSectorSubspace`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.oddSectorSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension d, oddSectorSubspace(d) = ker(P + I) is the -1 eigenspace O_d of the parity operator in C^d.

**Definition 1.4 (Even-sector orthogonal projector).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.evenProjector`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.evenProjector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a dimension d, evenProjector(d) = (I + P) / 2 is the orthogonal projector onto the even parity sector.

**Definition 1.5 (Odd-sector orthogonal projector).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.oddProjector`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.oddProjector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a dimension d, oddProjector(d) = (I - P) / 2 is the orthogonal projector onto the odd parity sector.

**Definition 1.6 (Canonical even-sector isometric frame).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.evenIsometry`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.evenIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension d, evenIsometry(d) : C^{(d + 1) / 2} -> C^d has column 0 equal to |0> and column j for 1 <= j < (d + 1) / 2 equal to (|j> + |-j>) / sqrt(2).

**Definition 1.7 (Canonical odd-sector isometric frame).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.oddIsometry`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.oddIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a nonzero dimension d, oddIsometry(d) : C^{(d - 1) / 2} -> C^d has column idx for 0 <= idx < (d - 1) / 2 equal to (|idx + 1> - |-(idx + 1)>) / sqrt(2).

**Definition 1.8 (Even-sector compressed clock eigenvalues).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.evenClockDiag`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.evenClockDiag` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a dimension d and integer clock exponent h, evenClockDiag(d, h) assigns 1 to index 0 and cos(2 pi h j / d) to each positive index 1 <= j < (d + 1) / 2.

**Definition 1.9 (Odd-sector compressed clock eigenvalues).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.oddClockDiag`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.oddClockDiag` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a dimension d and integer clock exponent h, oddClockDiag(d, h) assigns cos(2 pi h (idx + 1) / d) to each index 0 <= idx < (d - 1) / 2.

**Definition 1.10 (Even-sector compressed clock power sums).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.evenClockPowerSum`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.evenClockPowerSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For d, h, and m, evenClockPowerSum(d, h, m) is the m-th power sum sum_{idx} evenClockDiag(d, h, idx)^m across the (d + 1) / 2 eigenvalues on E_d.

**Definition 1.11 (Odd-sector compressed clock power sums).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.oddClockPowerSum`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.oddClockPowerSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For d, h, and m, oddClockPowerSum(d, h, m) is the m-th power sum sum_{idx} oddClockDiag(d, h, idx)^m across the (d - 1) / 2 eigenvalues on O_d.

**Definition 1.12 (Projective order of a phase-space label).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.weylLabelOrder`

*Formalization.* `D5/S3/Quantum/Magic/ParitySectorMoments.weylLabelOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For a dimension d and label a = (a_1, a_2) in (Z / dZ)^2, weylLabelOrder(d, a) = d / gcd(val(a_1), gcd(val(a_2), d)) is the additive order of a in (Z / dZ)^2.

**Theorem 1.13 (Parity involution, canonical sector bases, dimensions, and isometry invariance).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.parity_sectors_bases_and_isometries`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ParitySectorMoments.parity_sectors_bases_and_isometries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For every odd dimension d >= 3, parityMatrix(d) is Hermitian and involutory (P^2 = I, P^* = P). The canonical frames evenIsometry(d) and oddIsometry(d) are isometries whose range projectors equal evenProjector(d) and oddProjector(d), whose column spaces equal evenSectorSubspace(d) of dimension (d + 1) / 2 and oddSectorSubspace(d) of dimension (d - 1) / 2, and every isometric embedding E : C^S -> C^d with image E_d (respectively O_d) has |S| = (d + 1) / 2 (respectively (d - 1) / 2) and shares the same projector, labelFourthMoment values, and aseGap as the canonical frame.

**Theorem 1.14 (Parity-commuting Clifford reduction of nonzero Weyl labels to pure clock powers).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.parity_clifford_label_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ParitySectorMoments.parity_clifford_label_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For every odd dimension d >= 3, both canonical parity frames have unit fourth moment at the origin (0, 0), and for every nonzero label a in (Z / dZ)^2 there exists an integer h with gcd(h, d) = gcd(val(a_1), gcd(val(a_2), d)) such that labelFourthMoment(V, a) = labelFourthMoment(V, (0, h mod d)) simultaneously for V in {E_d, O_d}. The reduction conjugates Weyl operators by the discrete Fourier transform F |j> = d^{-1 / 2} sum_l omega^{j l} |l> and the odd-d quadratic phase gate S |j> = tau^{j^2} |j>, both unitary and commuting with P, which act on phase-space labels up to unimodular scalars as (x, y) -> (-y, x) and (x, y) -> (x, x + y), implementing Euclidean gcd reduction on nonnegative integer lifts.

**Theorem 1.15 (Diagonal cosine compressions of pure clock powers and closed-form power sums).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.parity_clock_compression_and_power_sums`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ParitySectorMoments.parity_clock_compression_and_power_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For every odd dimension d >= 3 and every integer h, compressing D_{(0, h mod d)} = Z^h onto E_d and O_d in the canonical bases yields the real diagonal matrices diag(evenClockDiag(d, h)) and diag(oddClockDiag(d, h)). Whenever h is not divisible by d, letting n = d / gcd(h, d) >= 3 (which is odd) and writing epsilon = +1 for E_d and epsilon = -1 for O_d, character orthogonality over Z / dZ gives the power sums p_1 = epsilon / 2, p_2 = (d + 2 epsilon) / 4, p_3 = (d + 4 epsilon) / 8 when n = 3 and epsilon / 2 when n != 3, and p_4 = (3 d + 8 epsilon) / 16.

**Theorem 1.16 (Closed-form Haar fourth moment of a nonzero Weyl label with order-three bifurcation).**

Lean statement: `D5/S3/Quantum/Magic/ParitySectorMoments.parity_nonzero_label_fourth_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ParitySectorMoments.parity_nonzero_label_fourth_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For every odd dimension d >= 3 and every nonzero label a in (Z / dZ)^2 of order n = weylLabelOrder(d, a), substituting the compressed clock power sums into the five-term Hermitian fourth-moment polynomial on E_d (dimension k = (d + 1) / 2) and O_d (dimension k = (d - 1) / 2) yields labelFourthMoment(E_d, a) = labelFourthMoment(O_d, a) = 3 / ((d + 1)(d + 3)) whenever n != 3, whereas for n = 3 it yields labelFourthMoment(E_d, a) = (3 d + 35) / ((d + 1)(d + 5)(d + 7)) and labelFourthMoment(O_d, a) = (3 d - 5) / ((d - 1)(d + 1)(d + 5)).

## References

- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.evenClockDiag`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.evenClockPowerSum`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.evenIsometry`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.evenProjector`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.evenSectorSubspace`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.oddClockDiag`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.oddClockPowerSum`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.oddIsometry`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.oddProjector`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.oddSectorSubspace`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.parityMatrix`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.parity_clifford_label_reduction`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.parity_clock_compression_and_power_sums`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.parity_nonzero_label_fourth_moment`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.parity_sectors_bases_and_isometries`
- Truth anchor: `D5/S3/Quantum/Magic/ParitySectorMoments.weylLabelOrder`
- Dependency: [D5/S3/Quantum/Magic/SubspaceStabilizerEntropy](SubspaceStabilizerEntropy.md)
