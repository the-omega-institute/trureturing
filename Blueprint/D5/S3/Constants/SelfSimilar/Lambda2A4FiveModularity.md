# Five-Modularity of the Lambda-Squared A4 Lattice

## Abstract

The source Gram and Hodge certificates force both five-modular similarities, rank six, and the two recorded discriminant identities.

**Theorem 1.1 (The certified Lambda-squared A4 realization is five-modular).**

$$\begin{gathered}\forall E, B, L, b, J, e,\\{}\operatorname{IntegralRealBilinearLattice}\left(E, B, L\right) \land \operatorname{BasisFin6Z}\left(b, L\right) \land\\{}\operatorname{latticeGram}\left(B, L, b\right) = lambda2A4Gram \land\\{}\operatorname{LinearEquiv}\left(e, L, \operatorname{dualSubmodule}\left(B, L\right)\right) \land\\{}(\forall x \in L, e(x) = \frac{1}{5} \cdot J(x)) \land\\{}(\forall x, y \in E, B(J(x), J(y)) = 5 \cdot B(x, y)) \Rightarrow\\{}\operatorname{LatticeSimilarity}\left(B, \frac{1}{\sqrt{5}}, L, \operatorname{dualSubmodule}\left(B, L\right)\right) \land\\{}\operatorname{finrankZ}\left(L\right) = 6 \land\\{}\operatorname{LatticeSimilarity}\left(B, \sqrt{5}, \operatorname{dualSubmodule}\left(B, L\right), L\right) \land\\{}\operatorname{latticeDiscriminant}\left(B, L, b\right) = 5^{3} \land\\{}\operatorname{latticeDiscriminant}\left(B, L, b\right) = 5^{\frac{6}{2}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/Lambda2A4FiveModularity.lambda2A4_five_modularity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be any integral lattice realization carrying the six-element basis, the displayed Lambda-squared A4 Gram matrix, the integral Hodge operator, and the exact identification of its bilinear dual with the image of J divided by five.

The Hodge similitude equation makes that dual identification scale the bilinear form by one fifth. It therefore gives similarity ratio one over square root five; the inverse equivalence gives ratio square root five in the other direction.

The six-element integral basis supplies rank six. The determinant of its fixed Gram matrix is 125, yielding separately the source identities five cubed and five raised to six divided by two.

## References

- Truth anchor: `D5/S3/Constants/SelfSimilar/Lambda2A4FiveModularity.lambda2A4_five_modularity`
