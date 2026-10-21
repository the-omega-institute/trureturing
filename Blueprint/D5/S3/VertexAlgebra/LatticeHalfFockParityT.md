# Actual half-Fock parity and finite trace

## Abstract

Literal oscillator parity on every actual finite half-Fock grade and its inserted trace.

For arbitrary integral symmetric even-diagonal lattice data D, an invertible Gram determinant hu, every natural grade N and every ground endomorphism A, define actualParity as TensorProduct.map of the public oscillator sigmaLinear with the genuine ground identity. The operator is on ActualTensor, so it does not replace the separate charge-reflection theta.

**Definition 1.1 (The literal oscillator parity operator).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParity`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The operator is the actual oscillator involution tensored with identity on ActualGround. Existing sigma_monomial supplies the occurrence-length sign.

**Theorem 1.2 (Parity is scalar on every actual grade vector).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParity_on_actualGrade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParity_on_actualGrade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Every vector in actualGrade D hu N is sent to (-1)^N times itself. The proof uses the accepted actualGradeBasis, the equality of odd oscillator-weight parity and occurrence-count parity, and basis linearity; no eigenvector-only premise is added.

**Theorem 1.3 (Parity after genuine ground insertion is a restricted operator).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityGroundInsertRestrict_eq_smul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityGroundInsertRestrict_eq_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Compose actualParity with the existing ground insertion, restrict the composite to the preserved finite grade, and prove the operator equality to (-1)^N times actualGroundInsertRestrict. The restriction is genuine and carries arbitrary A.

**Theorem 1.4 (The parity-inserted finite trace).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityTraceTerm_eq_bRank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityTraceTerm_eq_bRank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The trace is taken on the existing finite actual grade. Linearity of LinearMap.trace and the accepted bRank trace identity give (-1)^N times the ordinary finite insertion trace, including rank zero, N zero, zero traces and arbitrary complex A.

The canonical Character supplier is caller-owned and is not imported by this checkpoint. The trace-defined parity character, absolute convergence transport and the paired forward/reverse T laws with phases exp(2*pi*I*rank/48), together with T squared at exp(2*pi*I*rank/24), remain the explicit continuation obligation once that API is canonically available. No eta rewrite, scalar proxy, positivity or even-rank premise is introduced here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityGroundInsertRestrict_eq_smul`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityTraceTerm_eq_bRank`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParity_on_actualGrade`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGradedTrace](LatticeHalfFockGradedTrace.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](LatticeInvolution.md)
