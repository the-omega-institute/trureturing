# The Strict Composite Matrix-Cone Chain

## Abstract

The two-qubit separable, positive-semidefinite, and block-positive matrix cones form a strict inclusion chain.

**Theorem 1.1 (The composite matrix cones form a strict chain).**

$$(\{W: \operatorname{Matrix}((\operatorname{Fin}(2) \times \operatorname{Fin}(2)), (\operatorname{Fin}(2) \times \operatorname{Fin}(2)), \mathbb{C}) \mid \operatorname{separableCone}(W)\} \subset \{W: \operatorname{Matrix}((\operatorname{Fin}(2) \times \operatorname{Fin}(2)), (\operatorname{Fin}(2) \times \operatorname{Fin}(2)), \mathbb{C}) \mid \operatorname{PosSemidef}(W)\}) \land (\{W: \operatorname{Matrix}((\operatorname{Fin}(2) \times \operatorname{Fin}(2)), (\operatorname{Fin}(2) \times \operatorname{Fin}(2)), \mathbb{C}) \mid \operatorname{PosSemidef}(W)\} \subset \{W: \operatorname{Matrix}((\operatorname{Fin}(2) \times \operatorname{Fin}(2)), (\operatorname{Fin}(2) \times \operatorname{Fin}(2)), \mathbb{C}) \mid \operatorname{blockPositive}(W)\}) \land (\forall W: \operatorname{Matrix}((\operatorname{Fin}(2) \times \operatorname{Fin}(2)), (\operatorname{Fin}(2) \times \operatorname{Fin}(2)), \mathbb{C}), \operatorname{blockPositive}(W) \Leftrightarrow \forall a: \operatorname{Fin}(2) \to \mathbb{C}, b: \operatorname{Fin}(2) \to \mathbb{C}, 0 \leq \operatorname{Re}(\operatorname{dotProduct}(a\times b, W(a\times b)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeCones/StrictChain.strict_composite_cone_chain_and_block_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient space consists of complex matrices on two two-dimensional factors. The first conjunct says that the separable cone is a proper subset of the positive-semidefinite cone. The second says that the positive-semidefinite cone is a proper subset of the block-positive cone.

The final conjunct records the defining product-vector test for block positivity: the real part of the quadratic form is nonnegative for every pair of factor vectors. Thus the displayed theorem includes both strict inclusions and the parenthetical criterion in the source statement.

The inclusion proofs are the frozen separable_isPosSemidef and posSemidef_blockPositive declarations. Frozen singlet and exchange operator witnesses establish strictness. Loogle and LeanSearch found the exact Set.ssubset_iff_exists assembly theorem, which the Lean proof applies directly; neither service found an exact theorem for the custom three-cone chain.

## References

- Truth anchor: `D5/S3/Resource/CompositeCones/StrictChain.strict_composite_cone_chain_and_block_criterion`
