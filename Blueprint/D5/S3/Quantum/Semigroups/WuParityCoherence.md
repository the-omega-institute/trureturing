# Signed parity coherence in two CAR modes

## Abstract

The signed CAR jumps give exact formulas for parity interference and rank-two projection defects.

**Theorem 1.1 (Lowering and raising interference).**

Lean statement: `D5/S3/Quantum/Semigroups/WuParityCoherence.signed_interference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuParityCoherence.signed_interference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

In physical occupation order (00, 01, 10, 11), the lowering jumps are E₀₂ + E₁₃ and −E₀₁ + E₂₃. Write B for the block with rows (00, 11) and columns (01, 10). For a Hermitian M, keep the opposite-parity entries of each jump sum and pair them with M² by the ordinary real trace. The lowering trace is twice the real part of the determinant with rows 0 of B(M²) and 1 of B(M). The raising trace uses rows 0 of B(M) and 1 of B(M²).

The cubic deficit weights the two traces by −γr² and −γr, respectively, where γ = 9/[4(1 + r³)]. Their sum is −2γr times the real part of r times the lowering determinant plus the raising determinant.

**Theorem 1.2 (Exact four-square defect).**

Lean statement: `D5/S3/Quantum/Semigroups/WuParityCoherence.rankTwo_projection_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuParityCoherence.rankTwo_projection_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let Q be a Hermitian projection of trace two. Let A be its even principal block, and let B be its even-row, odd-column block, in the same sector orders. Set L = Re(A₁₁ − A₀₀), and let G be the ordinary real trace pairing of Q with the sum of its lowering and raising sandwiches. The exact defect 3 − L² − G equals 3(Re Tr A − 1)² + 4|A₀₁|² + 2|B₀₀ − overline(B₁₁)|² + 2|B₀₁ + overline(B₁₀)|².

The real trace pairing contains +4 Re det B. Expanding the two squared moduli of cross-block entries produces the corresponding −4 Re det B in the defect. The two even-site diagonal equations of Q² = Q supply the remaining terms. The four squares vanish exactly when G = 3 − L².

**Theorem 1.3 (Attained maximum at fixed occupation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuParityCoherence.rankTwo_projection_isGreatest`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuParityCoherence.rankTwo_projection_isGreatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For each L in [−1, 1], the greatest value of G over Hermitian projections of trace two with Re Tr(NQ) = 2 + L is 3 − L², where the total number operator N is diag(0, 1, 1, 2). An attaining projection on that same slice commutes with first-mode occupation.

The four-square identity bounds G on the entire slice. For attainment, take the identity on the first mode tensored with the real one-mode projection with diagonal p = (1 − L)/2 and q = (1 + L)/2 and both off-diagonal entries √(pq). This projection has the required occupation trace and makes all four squares vanish, including at both endpoints.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuParityCoherence.rankTwo_projection_defect`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuParityCoherence.rankTwo_projection_isGreatest`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuParityCoherence.signed_interference`
- Dependency: [D5/S3/Quantum/Semigroups/WuPhysicalHighHigh](WuPhysicalHighHigh.md)
