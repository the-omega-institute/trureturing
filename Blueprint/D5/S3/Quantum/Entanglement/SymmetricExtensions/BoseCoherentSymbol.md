# Coherent symbols of Bose operators

## Abstract

Coherent symbols separate actual Bose-supported operators

This is the finite polynomial spanning argument used in Gulati-Nechita-Park, Theorem 8.9. It concerns actual computational tensor matrices and the repository's full symmetric projector. It does not assume the GNP extension characterization and does not yet prove that characterization.

**Definition 1.1 (Actual bihomogeneous entry polynomial).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.symbol`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.symbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each computational matrix entry multiplies the monomial with its row occupation in the first variable family and its column occupation in the second. Repeated occupations are summed with their actual multiplicities, without any normalization.

**Theorem 1.2 (Evaluation is the actual coherent quadratic form).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_symbol`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_symbol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting conjugate z in the first family and z in the second gives exactly the quadratic form of the actual repeated tensor vector. This identity requires no support or positivity hypothesis.

**Theorem 1.3 (Coherent evaluations separate Bose operators).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eq_zero_of_coherent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eq_zero_of_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every tensor length and local dimension, a Hermitian matrix supported by the full symmetric-projector sandwich is zero if all its coherent quadratic forms vanish. An invertible Cartesian substitution and polynomial uniqueness prove vanishing of the independent-coordinate polynomial. The existing occupation-orbit theorem then identifies each coefficient with a matrix entry times two strictly positive occupation multiplicities. Empty and zero-dimensional boundaries are retained.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eq_zero_of_coherent`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.eval_symbol`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.symbol`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT](../AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS](BoseDPS.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl](BoseOccupationTwirl.md)
