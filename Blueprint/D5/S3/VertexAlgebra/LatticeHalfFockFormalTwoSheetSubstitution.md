# Formal Two-Sheet Substitution

## Abstract

Original formal two-sheet coordinate

The coefficient variable u is formal. T(u)=4u(1-u)^(-2) has zero constant term, so substitution is the actual Mathlib power-series algebra homomorphism. No evaluation at a complex number, analytic convergence, cutoff, or chosen square-root axiom is used.

**Theorem 1.1 (Formal Coordinate Relation).**

$$\operatorname{mul}\left(\operatorname{twoSheetSeries}\left(\right), \operatorname{pow}\left(\operatorname{sub}\left(1, X\right), 2\right)\right)=\operatorname{mul}\left(4, X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution.formal_two_sheet_relation` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

T(u)(1-u)^2=4u is an identity in Complex formal power series. It is a normalization helper, not the missing charged-product theorem.

**Theorem 1.2 (Original Half-Integer Root).**

$$\operatorname{sheetSubstitution}\left(\operatorname{halfRoot}\left(\right)\right)=\operatorname{mul}\left(\operatorname{sub}\left(1, X\right), \operatorname{inv}\left(\operatorname{add}\left(1, X\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution.original_half_root_two_sheet` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The unchanged binomial series with exponent -1/2, composed with T, equals (1-u)/(1+u). The proof uses its binomial square identity and formal substitution. Constant coefficient one excludes the other algebraic square-root branch. The complete original Lambda/J mode comparison and both charged all-j identities remain separate obligations.

**Theorem 1.3 (Every Original Integer Label).**

$$\forall E\in \mathbb{Z}, \operatorname{sheetSubstitution}\left(\operatorname{halfLabel}\left(E\right)\right)=\operatorname{twoSheetLabel}\left(E\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution.original_half_integer_all_label_two_sheet` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every integer E, the literal binomial series with coefficients choose(E/2,n), composed with T(u), equals (1+u)^E(1-u)^(-E). Integer induction treats positive and negative labels without a cutoff or a nonnegative-label premise. This supplies the exact scalar label substitution for the original local chart. It does not identify the full original Lambda/J normal operators or eliminate any retained variable.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution.formal_two_sheet_relation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution.original_half_integer_all_label_two_sheet`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution.original_half_root_two_sheet`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets](LatticeHalfFockActualChargedTwoSheetFullNormalJets.md)
