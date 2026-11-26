# VBKMSingularVector

## Abstract

Virasoro and Borcherds presentation, action, and ideal structure.

**Definition 1.1 (singularWord).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (L : \mathbb{Z} \to A), \forall (w : A), (\operatorname{singularWord} L w : A) = ([ L (-1), [ L (-1), [ L (-1), [ L (-1), w] ] ] ] - (3 : \mathbb{C} ) \cdot [ L (-2), [ L (-1), [ L (-1), w] ] ] - (7 / 4 : \mathbb{C} ) \cdot [ L (-2), [ L (-2), w] ] + (3 : \mathbb{C} ) \cdot [ L (-3), [ L (-1), w] ] + (3 / 2 : \mathbb{C} ) \cdot [ L (-4), w] )$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies singularWord.

**Theorem 1.2 (singularWord cartan).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (L : \mathbb{Z} \to A), \forall (C H : A), \forall (\delta : \mathbb{C} ), (\forall r : \mathbb{Z} , [ L (-r), H] = ((r : \mathbb{C} ) * \delta ) \cdot L (-r)) \to (\forall n m : \mathbb{Z} , [ L n, L m] = ((n-m : \mathbb{Z} ) : \mathbb{C} ) \cdot L (n+m) + \operatorname{if} n = -m \operatorname{then} ((n^{3}-n : \mathbb{Z} ) : \mathbb{C} ) \cdot C \operatorname{else} 0) \to \operatorname{singularWord} L H = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_cartan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies singularWord cartan.

**Theorem 1.3 (singularWord commute).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (L : \mathbb{Z} \to A), \forall (e w : A), (\forall n : \mathbb{Z} , n < 0 \to [ e, L n] = 0) \to [ e, \operatorname{singularWord} L w] = \operatorname{singularWord} L [ e,w] $$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies singularWord commute.

**Theorem 1.4 (singularWord mode one).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (L : \mathbb{Z} \to A), \forall (C w : A), (\forall n m : \mathbb{Z} , [ L n, L m] = ((n-m : \mathbb{Z} ) : \mathbb{C} ) \cdot L (n+m) + \operatorname{if} n = -m \operatorname{then} ((n^{3}-n : \mathbb{Z} ) : \mathbb{C} ) \cdot C \operatorname{else} 0) \to ([ L 0,w] = (-3/8 : \mathbb{C} ) \cdot w) \to ([ L 1,w] = 0) \to [ L 1, \operatorname{singularWord} L w] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_mode_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies singularWord mode one.

**Theorem 1.5 (singularWord mode two).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (L : \mathbb{Z} \to A), \forall (C w : A), (\forall n m : \mathbb{Z} , [ L n, L m] = ((n-m : \mathbb{Z} ) : \mathbb{C} ) \cdot L (n+m) + \operatorname{if} n = -m \operatorname{then} ((n^{3}-n : \mathbb{Z} ) : \mathbb{C} ) \cdot C \operatorname{else} 0) \to ([ L 0,w] = (-3/8 : \mathbb{C} ) \cdot w) \to ([ L 1,w] = 0) \to ([ L 2,w] = 0) \to ([ C,w] = (1/3 : \mathbb{C} ) \cdot w) \to (\forall n : \mathbb{Z} , [ C,L n] = 0) \to [ L 2, \operatorname{singularWord} L w] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_mode_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies singularWord mode two.

**Theorem 1.6 (positive modes kill).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (L : \mathbb{Z} \to A), \forall (C v : A), (\forall n m : \mathbb{Z} , [ L n,L m] = ((n-m : \mathbb{Z} ) : \mathbb{C} ) \cdot L (n+m) + \operatorname{if} n = -m \operatorname{then} ((n^{3}-n : \mathbb{Z} ) : \mathbb{C} ) \cdot C \operatorname{else} 0) \to ([ L 1,v] = 0) \to ([ L 2,v] = 0) \to \forall n : \mathbb{Z} , 0 < n \to [ L n,v] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.positive_modes_kill` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies positive modes kill.

**Theorem 1.7 (singularWord eigen).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (L : \mathbb{Z} \to A), \forall (H w : A), \forall (\delta \mu : \mathbb{C} ), (\forall n : \mathbb{Z} , [ H,L n] = ((n : \mathbb{C} )*\delta ) \cdot L n) \to ([ H,w] = \mu \cdot w) \to [ H,\operatorname{singularWord} L w] = (\mu -4*\delta ) \cdot \operatorname{singularWord} L w$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies singularWord eigen.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.positive_modes_kill`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_cartan`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_commute`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_mode_one`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMSingularVector.singularWord_mode_two`
