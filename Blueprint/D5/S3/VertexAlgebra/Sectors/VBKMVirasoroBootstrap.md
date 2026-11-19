# VBKMVirasoroBootstrap

## Abstract

Virasoro and Borcherds presentation, action, and ideal structure.

**Theorem 1.1 (positive brackets from mixed).**

$$\forall (M I : \operatorname{Type}), [\operatorname{AddCommGroup} M], [\operatorname{Module} \mathbb{C} M], \forall (F : (\operatorname{Sum} I \mathbb{N}^{+} ) \to \operatorname{Module}.\operatorname{End} \mathbb{C} M), \forall (v : M), (\operatorname{Submodule}.\operatorname{span} \mathbb{C} (\operatorname{Set}.\operatorname{range} (\operatorname{List}.\operatorname{foldr} (\operatorname{fun} i x \mapsto F i x) v)) = \operatorname{Top}.\operatorname{top} ) \to \forall (T : \mathbb{Z} \to \operatorname{Module}.\operatorname{End} \mathbb{C} M), \forall (C : \operatorname{Module}.\operatorname{End} \mathbb{C} M), (\forall r : \mathbb{N}^{+} , T (-(val\left(r\right) : \mathbb{Z} )) = F (\operatorname{Sum}.\operatorname{inr} r)) \to (\forall (m : \mathbb{Z} ), 0 < m \to \forall i : I, [ T m,F (\operatorname{Sum}.\operatorname{inl} i)] = 0) \to (\forall (m : \mathbb{Z} ) (r : \mathbb{N}^{+} ), [ T m,T (-(val\left(r\right) : \mathbb{Z} ))] = ((m+(val\left(r\right) : \mathbb{Z} ) : \mathbb{Z} ) : \mathbb{C} ) \cdot T (m-val\left(r\right)) + \operatorname{if} m = val\left(r\right) \operatorname{then} ((m^{3}-m : \mathbb{Z} ) : \mathbb{C} ) \cdot C \operatorname{else} 0) \to (\forall m : \mathbb{Z} , [ T m,T 0] = (m : \mathbb{C} ) \cdot T m) \to (\forall m : \mathbb{Z} , [ T m,C] = 0) \to (\forall (m : \mathbb{Z} ), 0 < m \to T m v = 0) \to \forall (m n : \mathbb{Z} ), 0 < m \to 0 < n \to [ T m,T n] = ((m-n : \mathbb{Z} ) : \mathbb{C} ) \cdot T (m+n)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMVirasoroBootstrap.positive_brackets_from_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies positive brackets from mixed.

**Theorem 1.2 (full brackets from mixed).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (T : \mathbb{Z} \to A), \forall (C : A), (\forall (m : \mathbb{Z} ) (r : \mathbb{N}^{+} ), [ T m,T (-(val\left(r\right) : \mathbb{Z} ))] = ((m+(val\left(r\right) : \mathbb{Z} ) : \mathbb{Z} ) : \mathbb{C} ) \cdot T (m-val\left(r\right)) + \operatorname{if} m = val\left(r\right) \operatorname{then} ((m^{3}-m : \mathbb{Z} ) : \mathbb{C} ) \cdot C \operatorname{else} 0) \to (\forall m : \mathbb{Z} , [ T m,T 0] = (m : \mathbb{C} ) \cdot T m) \to (\forall m n : \mathbb{Z} , 0 < m \to 0 < n \to [ T m,T n] = ((m-n : \mathbb{Z} ) : \mathbb{C} ) \cdot T (m+n)) \to \forall m n : \mathbb{Z} , [ T m,T n] = ((m-n : \mathbb{Z} ) : \mathbb{C} ) \cdot T (m+n) + \operatorname{if} m = -n \operatorname{then} ((m^{3}-m : \mathbb{Z} ) : \mathbb{C} ) \cdot C \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMVirasoroBootstrap.full_brackets_from_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies full brackets from mixed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMVirasoroBootstrap.full_brackets_from_mixed`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMVirasoroBootstrap.positive_brackets_from_mixed`
