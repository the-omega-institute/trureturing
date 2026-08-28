# Five-Modularity of the Lambda-Squared A4 Lattice

## Abstract

The source Hodge and unimodular-pairing data force both five-modular similarities, rank six, and the two recorded discriminant identities.

**Theorem 1.1 (The certified Lambda-squared A4 realization is five-modular).**

$$\begin{gathered}\operatorname{LatticeSimilarity}\left(lambda2A4Form, \frac{1}{\sqrt{5}}, lambda2A4Lattice, \operatorname{dualSubmodule}\left(lambda2A4Form, lambda2A4Lattice\right)\right) \land\\{}\operatorname{finrankZ}\left(lambda2A4Lattice\right) = 6 \land\\{}\operatorname{LatticeSimilarity}\left(lambda2A4Form, \sqrt{5}, \operatorname{dualSubmodule}\left(lambda2A4Form, lambda2A4Lattice\right), lambda2A4Lattice\right) \land\\{}\operatorname{latticeDiscriminant}\left(lambda2A4Form, lambda2A4Lattice, lambda2A4IntegralBasis\right) = 5^{3} \land\\{}\operatorname{latticeDiscriminant}\left(lambda2A4Form, lambda2A4Lattice, lambda2A4IntegralBasis\right) = 5^{\frac{6}{2}} \land\\{}((\forall x, y \in lambda2A4Lattice, lambda2A4Form(lambda2A4DualEquiv(x), lambda2A4DualEquiv(y)) = \frac{1}{5} \cdot lambda2A4Form(x, y)) \Rightarrow \operatorname{latticeDiscriminant}\left(lambda2A4Form, lambda2A4Lattice, lambda2A4IntegralBasis\right) = 5^{\frac{6}{2}}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/Lambda2A4FiveModularity.lambda2A4_five_modularity` (`⚠ D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity.lambda2A4GramInt_det._native.native_decide.ax_1_1, D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity.lambda2A4PairEquiv._native.native_decide.ax_1, D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity.lambda2A4ReverseEquiv._native.native_decide.ax_1, D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity.lambda2A4UnimodularMatrixInt_det._native.native_decide.ax_1_1, D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity.lambda2A4_hodge_pairing_matrix_int._native.native_decide.ax_1_1, D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity.lambda2A4_hodge_similitude_matrix_int._native.native_decide.ax_1_1`). ∎

*Source.* Repository-derived.

*Commentary.*

Here L is the integral span of the fixed ordered wedge basis in the actual second exterior power of the A4 root space. Its form has the displayed Gram matrix, its Hodge operator is the fixed matrix J, and its actual bilinear dual is identified by the concrete map x to Jx divided by five.

The Hodge similitude equation makes that dual identification scale the bilinear form by one fifth. It therefore gives similarity ratio one over square root five; the inverse equivalence gives ratio square root five in the other direction.

The six-element integral basis supplies rank six. The pairing matrix of the transported dual basis against the source basis is the source's unimodular matrix U, whose determinant is minus one.

Changing between the two real bases turns unimodularity into reciprocal source and dual discriminants. Exact five-modular scaling gives the sixth-power determinant scale; reciprocity and positivity then force five raised to six divided by two, hence also five cubed. No precomputed determinant of the fixed Gram matrix enters this chain.

## References

- Truth anchor: `D5/S3/Constants/SelfSimilar/Lambda2A4FiveModularity.lambda2A4_five_modularity`
