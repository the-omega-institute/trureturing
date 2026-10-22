# Original ordinary modes in the native normal action

## Abstract

Original ordinary modes in the native normal action

The nonnegative source action is the literal neutralPolynomialMode on each charged polynomial. Zero mode is the actual charge pairing, and positive degree k acts by k times the Gram-weighted partial derivative at oscillator index k-1.

**Theorem 1.1 (Original ordinary modes in the native normal action).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockNormalCurrentAction.Corr_neutralPolynomialMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockNormalCurrentAction.Corr_neutralPolynomialMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Corr_neutralPolynomialMode proves compatibility of every actual nonnegative source mode with every coefficient of the full Corr. neutralPolynomialMode_X_mul is obtained from the original weightedPartial_X_mul supplier, whose proof body is preserved and whose visibility is reconciled.

binomial_product consumes the existing Mathlib Ring.choose and Pochhammer suppliers. jet_contraction_binomial identifies frequency(j)*jetScalar(n,-j-1) with (n+1)*Ring.choose(frequency(j),n+1), with no sign or positivity restriction on j. deltaTerm_support proves genuine finite mode support before its sum is formed. nativeDelta is only an auxiliary finite sum of original source modes, not a replacement Ytw or an assumed module law.

The owning Reg mirrors provide exact dependent-telescope readouts and compiled source equivalence bridges for the substantive commutator and correction identities. They do not provide completed four-slot Contract.Registration inhabitants: variation, sensitivity and observational-dependence evidence remain admission obligations. Consumed algebraic and support helpers are proof organization, not separate new mathematical content.

This is the classical twisted lattice current law in the native constructors, not a claim of literature novelty. The established FLM background and the existing normal-support source attribution remain in force. Full all-state twisted Jacobi, the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockNormalCurrentAction.Corr_neutralPolynomialMode`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection](LatticeHalfFockCurrentCorrection.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormalRecurrence](LatticeHalfFockCurrentNormalRecurrence.md)
