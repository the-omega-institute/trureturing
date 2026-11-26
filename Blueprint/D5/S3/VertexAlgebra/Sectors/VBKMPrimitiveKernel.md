# VBKMPrimitiveKernel

## Abstract

Virasoro and Borcherds presentation, action, and ideal structure.

**Theorem 1.1 (normalized not proper).**

$$\forall (M L : \operatorname{Type}), [\operatorname{AddCommGroup} M], [\operatorname{Module} \mathbb{C} M], [\operatorname{LieRing} L], [\operatorname{LieAlgebra} \mathbb{C} L], [\operatorname{LieRingModule} L M], [\operatorname{LieModule} \mathbb{C} L M], \forall (H E F : L), \forall (a b : \mathbb{C} ), (a \neq 0) \to ([ E,F] = H) \to ([ H,E] = a \cdot E) \to ([ H,F] = -a \cdot F) \to \forall (w x : M), ([ H,w] = b \cdot w) \to ([ E,w] = 0) \to (\forall n : \mathbb{N} , (2/a)*b \neq (n : \mathbb{C} )) \to \forall (S : \operatorname{Set} L), (S \subseteq \operatorname{Submodule}.\operatorname{span} \mathbb{C} (\{E,F,H\} : \operatorname{Set} L)) \to (x \in \operatorname{LieSubmodule}.\operatorname{lieSpan} \mathbb{C} (\operatorname{LieSubalgebra}.\operatorname{lieSpan} \mathbb{C} L S) (\{w\} : \operatorname{Set} M)) \to ([ E,x] = 0) \to (x \neq 0) \to \neg (\operatorname{LieSubmodule}.\operatorname{lieSpan} \mathbb{C} (\operatorname{LieSubalgebra}.\operatorname{lieSpan} \mathbb{C} L S) (\{x\} : \operatorname{Set} M)).\operatorname{toSubmodule} < (\operatorname{LieSubmodule}.\operatorname{lieSpan} \mathbb{C} (\operatorname{LieSubalgebra}.\operatorname{lieSpan} \mathbb{C} L S) (\{w\} : \operatorname{Set} M)).\operatorname{toSubmodule}$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPrimitiveKernel.normalized_not_proper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies normalized not proper.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPrimitiveKernel.normalized_not_proper`
