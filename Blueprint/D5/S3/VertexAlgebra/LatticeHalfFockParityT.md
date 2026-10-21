# Actual half-Fock parity and paired T action

## Abstract

Literal oscillator parity, convergent finite-grade trace characters, and paired T and T-squared action.

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

**Definition 1.5 (The trace-defined parity character).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityInsertedCharacter`

*Formalization.* `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityInsertedCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Use exactly exp(2*pi*I*tau*rank/48) times the series of LinearMap.trace on actualGrade of actualParityGroundInsertRestrict, weighted by exp(pi*I*tau)^N. Thus the character retains the actual finite restriction and the same vacuum normalization as Character.

**Theorem 1.6 (Absolute convergence through the negative oscillator parameter).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_parity_trace_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_parity_trace_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every complex q with norm less than one, identify each literal parity trace coefficient with Character.actualTraceTerm at -q. Character.actual_trace_series applies because norm(-q)=norm(q), yielding absolute summability and HasSum with trace(A) times oddCoefficientSeries(rank,-q). No Euler or eta proof is duplicated.

**Theorem 1.7 (The normalized trace series sums to the parity character).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_parity_character_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_parity_character_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every tau in the upper half-plane, the oscillator parameter has norm less than one. Multiplication by the retained vacuum exponential gives absolute summability and HasSum to actualParityInsertedCharacter. This convergent series is consumed in the forward paired T proof.

**Theorem 1.8 (Both forward paired T laws).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_paired_T`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_paired_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The identity exp(pi*I*(tau+1))=-exp(pi*I*tau) interchanges the ordinary and parity trace series. The vacuum shift contributes phase48=exp(2*pi*I*rank/48). The two conclusions are character(tau+1)=phase48*parityCharacter(tau) and parityCharacter(tau+1)=phase48*character(tau). They are forward laws, retain all complex phases, and are consumed by the T-squared proof.

**Theorem 1.9 (Both T-squared laws).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_paired_T_sq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_paired_T_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Apply the paired T laws at tau and tau+1, both in the upper half-plane, and combine the two vacuum phases by exp_add. Each character at tau+2 equals exp(2*pi*I*rank/24) times itself at tau. Every theorem retains arbitrary lattice data D, IsUnit determinant, arbitrary ground endomorphism A, rank zero, grade zero and zero or complex trace. No positivity, even-rank premise, trace division or charge-reflection theta is used.

These results establish the oscillator-parity paired T action on the original half-Fock trace characters. Full SL2Z closure of a sector system, fusion, sewing, charged residue identities, and the full Moonshine/VOA/CFT/string/AdS-CFT programme remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityGroundInsertRestrict_eq_smul`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityInsertedCharacter`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParityTraceTerm_eq_bRank`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actualParity_on_actualGrade`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_paired_T`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_paired_T_sq`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_parity_character_series`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockParityT.actual_parity_trace_series`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCharacter](LatticeHalfFockCharacter.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGradedTrace](LatticeHalfFockGradedTrace.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](LatticeInvolution.md)
