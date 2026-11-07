# Exact Dicke and LDUI coordinates

## Abstract

Exact Dicke and LDUI coordinates

The operator-polynomial arguments are prior Gulati-Nechita-Park mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Strict hierarchy inclusions, unrestricted witness lifting, and closedness of the unclosed DPS dual sum are outside these statements.

For an arbitrary upper-triangular real Y, the diagonal coordinate is P_ii=Y_ii and each off-diagonal coordinate is P_ij=Y_min(i,j),max(i,j)/2. Substitution into the actual LDUI operator uses the off-diagonal weight 2P_ij, so the exact half factor cancels. Signed, zero and singular inputs remain in scope and no trace normalization is imposed.

**Definition 1.1 (Actual LDUI operator).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.ldui`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.ldui` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

This is the existing normalized Dicke operator with diagonal weight P_ii and off-diagonal weight 2P_ij. It is an actual bipartite computational matrix.

The CLDUI companion is the actual product-basis root transpose of the LDUI matrix. The companion need not have full Bose support; that support belongs to the inverse-transposed witness. The root transpose and the Y/P half-factor application are retained here as complete exposition.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI.ldui`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol](BoseCoherentSymbol.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose](BoseRootTranspose.md)
