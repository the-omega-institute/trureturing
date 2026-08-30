# Golden Local Branch Classification

## Abstract

The mod-five quadratic character controls a two-branch complex local operator.

**Definition 1.1 (Even branch projection).**

Lean statement: `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.evenBranchProjection`

*Formalization.* `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.evenBranchProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The half-sum of the identity and the canonical bit flip projects to the fixed branch.

**Definition 1.2 (Odd branch projection).**

Lean statement: `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.oddBranchProjection`

*Formalization.* `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.oddBranchProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The half-difference of the identity and the canonical bit flip projects to the negated branch.

**Definition 1.3 (Golden local branch operator).**

Lean statement: `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.goldenLocalBranchOperator`

*Formalization.* `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.goldenLocalBranchOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The even projector is combined with the odd projector weighted by the Legendre character modulo five.

**Theorem 1.4 (The local operator ramifies only at five).**

$$\forall p \in \mathbb{N}, (\operatorname{Prime}\left(p\right) \Rightarrow \operatorname{det}\left(\operatorname{goldenLocalBranchOperator}\left(p\right)\right) = \operatorname{legendreSym}\left(5, p\right)) \land\\{}(\operatorname{Prime}\left(p\right) \Rightarrow (\operatorname{legendreSym}\left(5, p\right) = 1 \Rightarrow (\operatorname{det}\left(\operatorname{goldenLocalBranchOperator}\left(p\right)\right) = 1 \land \operatorname{goldenLocalBranchOperator}\left(p\right) = I))) \land\\{}(\operatorname{Prime}\left(p\right) \Rightarrow (\operatorname{legendreSym}\left(5, p\right) = -1 \Rightarrow (\operatorname{det}\left(\operatorname{goldenLocalBranchOperator}\left(p\right)\right) = -1 \land \operatorname{goldenLocalBranchOperator}\left(p\right) = bitFlip))) \land\\{}(\operatorname{Prime}\left(p\right) \Rightarrow (\operatorname{legendreSym}\left(5, p\right) = 0 \Rightarrow (\operatorname{det}\left(\operatorname{goldenLocalBranchOperator}\left(p\right)\right) = 0 \land\\{}\operatorname{goldenLocalBranchOperator}\left(p\right) = evenBranchProjection \land\\{}\operatorname{mulVec}\left(\operatorname{goldenLocalBranchOperator}\left(p\right), \operatorname{vec2}\left(1, -1\right)\right) = 0 \land\\{}\operatorname{mulVec}\left(\operatorname{goldenLocalBranchOperator}\left(p\right), \operatorname{vec2}\left(1, 1\right)\right) = \operatorname{vec2}\left(1, 1\right)))) \land\\{}(\operatorname{Prime}\left(p\right) \Rightarrow (\neg\operatorname{IsUnit}\left(\operatorname{goldenLocalBranchOperator}\left(p\right)\right) \Leftrightarrow p = 5)) \land\\{}\operatorname{cast}\left(5, GoldenInt\right) = (-1 + 2\varphi)^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.golden_local_branch_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant is the mod-five quadratic character. Character one gives the identity, character minus one gives the canonical bit flip, and character zero fixes the even vector while killing the odd vector. For prime indices, noninvertibility is equivalent to the index being five. The same statement includes the ramified-square identity on GoldenInt.

The proof uses Mathlib's two-by-two determinant and matrix invertibility criteria, the Legendre zero criterion, and the frozen canonical golden-integer square theorem.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.evenBranchProjection`
- Truth anchor: `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.goldenLocalBranchOperator`
- Truth anchor: `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.golden_local_branch_classification`
- Truth anchor: `D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification.oddBranchProjection`
- Dependency: [D5/S3/PrimeForms/GoldenPrimeClassification](../GoldenPrimeClassification.md)
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge](../../QuantumBounds/ReferenceFrame/ChannelFidelityBridge.md)
