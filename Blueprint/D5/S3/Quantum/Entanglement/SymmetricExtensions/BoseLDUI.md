# Exact Dicke and LDUI coordinates

## Abstract

Exact Dicke and LDUI coordinates

The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.

**Definition 1.1 (Exact upper-triangular Y to symmetric P).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.coordinates`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.coordinates` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The diagonal coordinate is P_ii=Y_ii and each off-diagonal coordinate is P_ij=Y_min(i,j),max(i,j)/2. Substituting into ldui recovers the original upper-triangular normalized Dicke mixture: the off-diagonal weight 2P_ij cancels this factor one half. This is a direct application of the two definitions and is checked with the star criterion rather than retained as a separate theorem. Arbitrary signed coefficients, zero and singular inputs are included; no trace normalization is built into the map.

**Definition 1.2 (Actual LDUI operator).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.ldui`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.ldui` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

This is the existing normalized Dicke operator with diagonal weight P_ii and off-diagonal weight 2P_ij. It is an actual bipartite computational matrix.

**Definition 1.3 (Actual CLDUI companion).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.cldui`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.cldui` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The companion is the actual root partial transpose of the LDUI operator. Full Bose support belongs to the inverse-transposed witness, and is not asserted for the companion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.cldui`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.coordinates`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.ldui`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol](BoseCoherentSymbol.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose](BoseRootTranspose.md)
