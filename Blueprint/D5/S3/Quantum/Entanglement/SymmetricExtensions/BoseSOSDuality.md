# Native SOS sufficiency and diagonal tensor duality

## Abstract

Native SOS sufficiency and diagonal tensor duality

The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.

**Theorem 1.1 (Actual nonnegative trace pairing).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality.even_sos_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality.even_sos_nonnegative` (`✓ std3`). ∎

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

A homogeneous complex coherent symbol p of an actual Hermitian operator, with native SOS squared-variable expansion, pairs nonnegatively with every actual Bose-PPT matrix. Constructed PSD cut certificates have the same complex coherent symbol; polynomial separation proves equality of their symmetric compressions before trace pairing.

**Theorem 1.2 (Exact diagonal operator SOS equivalence).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality.diagonal_dual_iff_sos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality.diagonal_dual_iff_sos` (`✓ std3`). ∎

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

For arbitrary r and n, an occupation-diagonal Hermitian operator with actual real symbol p(X squared), where p is homogeneous of degree r, membership in the actual Bose-PPT dual is equivalent to the native SOS condition. This supplies the operator-polynomial step in Gulati-Nechita-Park Theorems 8.9 and 8.11; BoseHierarchy uses it to prove the complete marginal and Parrilo hierarchy characterization.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality.diagonal_dual_iff_sos`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality.even_sos_nonnegative`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDiagonalSymbol](BoseDiagonalSymbol.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality](BosePPTDuality.md)
