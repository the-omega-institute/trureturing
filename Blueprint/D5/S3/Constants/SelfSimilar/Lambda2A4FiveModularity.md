# Five-Modularity of the Lambda-Squared A4 Lattice

## Abstract

The source Hodge and unimodular-pairing data force both five-modular similarities, rank six, and the two recorded discriminant identities.

**Theorem 1.1 (The certified Lambda-squared A4 realization is five-modular).**

$$\begin{gathered}\forall E, B, L, b, J, e, s, t,\\{}\operatorname{IntegralRealBilinearLattice}\left(E, B, L\right) \land \operatorname{BasisFin6Z}\left(b, L\right) \land\\{}\operatorname{latticeGram}\left(B, L, b\right) = lambda2A4Gram \land\\{}\operatorname{LinearEquiv}\left(e, L, \operatorname{dualSubmodule}\left(B, L\right)\right) \land\\{}(\forall x \in L, e(x) = \frac{1}{5} \cdot J(x)) \land\\{}(\forall x, y \in E, B(J(x), J(y)) = 5 \cdot B(x, y)) \land\\{}\operatorname{BasisFin6R}\left(s, E\right) \land \operatorname{BasisFin6R}\left(t, E\right) \land\\{}(\forall i, s(i) = b(i)) \land\\{}(\forall i, t(i) = e(b(i))) \land\\{}\operatorname{det}\left(\operatorname{latticePairingMatrix}\left(B, L, b, e\right)\right) = -1 \land\\{}0 < \operatorname{latticeDiscriminant}\left(B, L, b\right) \Rightarrow\\{}\operatorname{LatticeSimilarity}\left(B, \frac{1}{\sqrt{5}}, L, \operatorname{dualSubmodule}\left(B, L\right)\right) \land\\{}\operatorname{finrankZ}\left(L\right) = 6 \land\\{}\operatorname{LatticeSimilarity}\left(B, \sqrt{5}, \operatorname{dualSubmodule}\left(B, L\right), L\right) \land\\{}\operatorname{latticeDiscriminant}\left(B, L, b\right) = 5^{3} \land\\{}\operatorname{latticeDiscriminant}\left(B, L, b\right) = 5^{\frac{6}{2}} \land\\{}((\forall x, y \in L, B(e(x), e(y)) = \frac{1}{5} \cdot B(x, y)) \Rightarrow \operatorname{latticeDiscriminant}\left(B, L, b\right) = 5^{\frac{6}{2}}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SelfSimilar/Lambda2A4FiveModularity.lambda2A4_five_modularity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be any integral lattice realization carrying the six-element basis, the displayed Lambda-squared A4 Gram matrix, the integral Hodge operator, and the exact identification of its bilinear dual with the image of J divided by five. The source and transported-dual integral bases are also identified with real bases of the ambient space.

The Hodge similitude equation makes that dual identification scale the bilinear form by one fifth. It therefore gives similarity ratio one over square root five; the inverse equivalence gives ratio square root five in the other direction.

The six-element integral basis supplies rank six. The pairing matrix of the transported dual basis against the source basis is the source's unimodular matrix U, whose determinant is minus one.

Changing between the two real bases turns unimodularity into reciprocal source and dual discriminants. Exact five-modular scaling gives the sixth-power determinant scale; reciprocity and positivity then force five raised to six divided by two, hence also five cubed. No precomputed determinant of the fixed Gram matrix enters this chain.

## References

- Truth anchor: `D5/S3/Constants/SelfSimilar/Lambda2A4FiveModularity.lambda2A4_five_modularity`
