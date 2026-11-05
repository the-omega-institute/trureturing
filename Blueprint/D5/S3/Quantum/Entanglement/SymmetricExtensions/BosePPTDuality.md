# Native SOS necessity for actual Bose-PPT dual operators

## Abstract

Native SOS necessity for actual Bose-PPT dual operators

The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.

**Definition 1.1 (Actual Bose support space).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.boseSpace`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.boseSpace` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The real Hermitian subspace is defined by the original full tensor-projector sandwich. Positivity is not imposed by the subspace.

**Definition 1.2 (Actual all-cut Bose-PPT cone).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.bosePPT`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.bosePPT` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The actual full Bose sandwich is combined with product-basis PSD partial transposes at every cut, including empty and full cuts.

**Theorem 1.3 (SOS necessity without dropping closure).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.dual_bosePPT_real_sos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.dual_bosePPT_real_sos` (`✓ std3`). ∎

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

Every Hermitian operator with nonnegative trace pairing against all actual Bose-PPT matrices has a native real SOS coherent polynomial. The proof uses closedness of the actual homogeneous SOS coefficient cone and finite-dimensional bipolarity. It does not identify an unclosed operator dual sum.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.bosePPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.boseSpace`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality.dual_bosePPT_real_sos`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual](BoseDual.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSCertificates](BoseSOSCertificates.md)
