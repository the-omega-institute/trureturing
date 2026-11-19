# VBKMWeightIdeal

## Abstract

Virasoro and Borcherds presentation, action, and ideal structure.

**Theorem 1.1 (nonzero disjoint ideal).**

$$\forall (A N P : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (\operatorname{neg} : N \to A), \forall (\operatorname{pos} : P \to A), \forall (v H : A), \forall (C : \operatorname{Set} A), (\forall c \in C, \forall n, [ c,\operatorname{neg} n] \in \operatorname{Submodule}.\operatorname{span} \mathbb{C} (\operatorname{Set}.\operatorname{range} \operatorname{neg})) \to (\forall c \in C, [ c,v] \in \operatorname{Submodule}.\operatorname{span} \mathbb{C} (\{v\} : \operatorname{Set} A)) \to (\forall p n, [ \operatorname{pos} p,\operatorname{neg} n] \in \operatorname{sup} (\operatorname{sup} (\operatorname{Submodule}.\operatorname{span} \mathbb{C} (\operatorname{Set}.\operatorname{range} \operatorname{neg})) (\operatorname{Submodule}.\operatorname{span} \mathbb{C} C)) (\operatorname{Submodule}.\operatorname{span} \mathbb{C} (\operatorname{Set}.\operatorname{range} \operatorname{pos}))) \to (\forall p, [ \operatorname{pos} p,v] = 0) \to (\operatorname{LieSubalgebra}.\operatorname{lieSpan} \mathbb{C} A (C \cup \operatorname{Set}.\operatorname{range} \operatorname{neg} \cup \operatorname{Set}.\operatorname{range} \operatorname{pos}) = \operatorname{Top}.\operatorname{top} ) \to \forall (\alpha : N \to \mathbb{C} ), \forall (\mu : \mathbb{C} ), (\forall n, [ H,\operatorname{neg} n] = (-\alpha n) \cdot \operatorname{neg} n) \to ([ H,v] = \mu \cdot v) \to (\forall n, 0 < (\alpha n).\operatorname{re}) \to (\mu .\operatorname{re} < 0) \to (\forall c \in C, [ H,c] = 0) \to (v \neq 0) \to \exists K : \operatorname{LieIdeal} \mathbb{C} A, K \neq \perp \land \operatorname{inf} \operatorname{K}.\operatorname{toSubmodule} (\operatorname{Submodule}.\operatorname{span} \mathbb{C} C) = \perp $$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMWeightIdeal.nonzero_disjoint_ideal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies nonzero disjoint ideal.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMWeightIdeal.nonzero_disjoint_ideal`
