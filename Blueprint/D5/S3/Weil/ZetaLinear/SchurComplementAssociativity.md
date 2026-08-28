# Schur Complement Associativity

## Abstract

Sequential and one-shot Schur elimination give the same retained operator.

**Theorem 1.1 (Sequential elimination equals one-shot elimination).**

$$\forall H0 \in \operatorname{Type}\left(\right), H1 \in \operatorname{Type}\left(\right), H2 \in \operatorname{Type}\left(\right), A00 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H0, H0\right), A01 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H1, H0\right), A02 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H2, H0\right), A10 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H0, H1\right), A11 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H1, H1\right), A12 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H2, H1\right), A20 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H0, H2\right), A21 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H1, H2\right), A22 \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H2, H2\right), A22Inv \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H2, H2\right), reducedA11Inv \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H1, H1\right), lowerInv \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, \operatorname{Prod}\left(H1, H2\right), \operatorname{Prod}\left(H1, H2\right)\right),\; \left(\operatorname{NormedAddCommGroup}\left(H0\right) \land \left(\operatorname{InnerProductSpace}\left(\mathbb{C}, H0\right) \land \left(\operatorname{CompleteSpace}\left(H0\right) \land \left(\operatorname{NormedAddCommGroup}\left(H1\right) \land \left(\operatorname{InnerProductSpace}\left(\mathbb{C}, H1\right) \land \left(\operatorname{CompleteSpace}\left(H1\right) \land \left(\operatorname{NormedAddCommGroup}\left(H2\right) \land \left(\operatorname{InnerProductSpace}\left(\mathbb{C}, H2\right) \land \left(\operatorname{CompleteSpace}\left(H2\right) \land \left(\operatorname{comp}\left(A22Inv, A22\right) = \operatorname{id}\left(\mathbb{C}, H2\right) \land \left(\operatorname{comp}\left(reducedA11Inv, A11 - \operatorname{comp}\left(A12, \operatorname{comp}\left(A22Inv, A21\right)\right)\right) = \operatorname{id}\left(\mathbb{C}, H1\right) \land \operatorname{comp}\left(\operatorname{prod}\left(\operatorname{coprod}\left(A11, A12\right), \operatorname{coprod}\left(A21, A22\right)\right), lowerInv\right) = \operatorname{id}\left(\mathbb{C}, \operatorname{Prod}\left(H1, H2\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow A00 - \operatorname{comp}\left(A02, \operatorname{comp}\left(A22Inv, A20\right)\right) - \operatorname{comp}\left(A01 - \operatorname{comp}\left(A02, \operatorname{comp}\left(A22Inv, A21\right)\right), \operatorname{comp}\left(reducedA11Inv, A10 - \operatorname{comp}\left(A12, \operatorname{comp}\left(A22Inv, A20\right)\right)\right)\right) = A00 - \operatorname{comp}\left(\operatorname{coprod}\left(A01, A02\right), \operatorname{comp}\left(lowerInv, \operatorname{prod}\left(A10, A20\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/SchurComplementAssociativity.schur_complement_associativity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H0, H1, and H2 be complete complex inner-product spaces. Nine bounded maps are the blocks of an operator on their three-fold product.

Suppose the H2 block, the H1 block obtained after eliminating H2, and the combined lower block have the displayed inverse witnesses. Then sequentially eliminating H2 and H1 gives the same retained H0 operator as eliminating H1 times H2 in one step.

The proof applies the combined lower inverse to the retained column, solves its two block equations successively, and substitutes those solutions into the retained row.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/SchurComplementAssociativity.schur_complement_associativity`
