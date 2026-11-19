# VBKMRecursiveAction

## Abstract

Virasoro and Borcherds presentation, action, and ideal structure.

**Theorem 1.1 (left basis).**

$$\forall (g : (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), \forall (w : (\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ))), (\operatorname{fun} (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{cons} g)) g ((\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) w) = (\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) (g::w)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.left_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies left basis.

**Definition 1.2 (relation).**

$$\forall (r s : \mathbb{N}^{+} ), \forall (v : (\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ))), (\operatorname{relation} r s v : ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )) = ((\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) (\operatorname{Sum}.\operatorname{inr} r :: \operatorname{Sum}.\operatorname{inr} s :: v) - (\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) (\operatorname{Sum}.\operatorname{inr} s :: \operatorname{Sum}.\operatorname{inr} r :: v) - ((val\left(s\right) : \mathbb{C} ) - (val\left(r\right) : \mathbb{C} )) \cdot (\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) (\operatorname{Sum}.\operatorname{inr} (r+s) :: v))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.relation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies relation.

**Definition 1.3 (relations).**

$$(\operatorname{relations} : \operatorname{Set} ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )) = (\{x | \exists (u v : (\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ))) (r s : \mathbb{N}^{+} ), x = (\operatorname{fun} (u : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{append} u)) u (\operatorname{relation} r s v)\})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.relations` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies relations.

**Definition 1.4 (N).**

$$(N : \operatorname{Submodule} \mathbb{C} ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )) = (\operatorname{Submodule}.\operatorname{span} \mathbb{C} \operatorname{relations})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.N` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies N.

**Theorem 1.5 (leftPreserves).**

$$\forall (g : (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), \forall (x : ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )), (x \in N) \to (\operatorname{fun} (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{cons} g)) g x \in N$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.leftPreserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies leftPreserves.

**Definition 1.6 (tokenWeight).**

$$\forall (a : \mathbb{C} \times \mathbb{C} ), (\forall (i : \operatorname{Bool}), \operatorname{tokenWeight} a (\operatorname{Sum}.\operatorname{inl} i) = (\operatorname{if} i \operatorname{then} 4/3*a.1+a.2 \operatorname{else} a.1+2/3*a.2)) \land (\forall (r : \mathbb{N}^{+} ), \operatorname{tokenWeight} a (\operatorname{Sum}.\operatorname{inr} r) = (val\left(r\right) : \mathbb{C} )/3*(a.1+a.2))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.tokenWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies tokenWeight.

**Definition 1.7 (wordWeight).**

$$\forall (a : \mathbb{C} \times \mathbb{C} ), \forall (w : (\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ))), (\operatorname{wordWeight} a w : \mathbb{C} ) = ((\operatorname{w}.\operatorname{map} (\operatorname{tokenWeight} a)).\operatorname{sum})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.wordWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies wordWeight.

**Definition 1.8 (cartan).**

$$\forall (a : \mathbb{C} \times \mathbb{C}), cartan\left(a\right) = \operatorname{D5}.\operatorname{S1}.\operatorname{Words}.\operatorname{WeakShuffleNormalization}.\operatorname{diagonal}\left(wordWeight\left(a\right)\right) = \operatorname{Finsupp}.\operatorname{linearCombination}\left(\mathbb{C}, (\operatorname{fun} w \mapsto \operatorname{Finsupp}.\operatorname{single}\left(w, wordWeight\left(a, w\right)\right))\right)$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.cartan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The Cartan operator rescales each word by its total weight.

**Definition 1.9 (raisingWord).**

$$\forall (i : \operatorname{Bool}), (\operatorname{raisingWord} i [ ] = 0) \land (\forall (k : \operatorname{Bool}) (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), \operatorname{raisingWord} i (\operatorname{Sum}.\operatorname{inl} k::w) = (\operatorname{fun} (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{cons} g)) (\operatorname{Sum}.\operatorname{inl} k) (\operatorname{raisingWord} i w) + (\operatorname{if} i=k \operatorname{then} \operatorname{cartan} (\operatorname{if} i \operatorname{then} (1,0) \operatorname{else} (0,1)) ((\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) w) \operatorname{else} 0)) \land (\forall (r : \mathbb{N}^{+} ) (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), \operatorname{raisingWord} i (\operatorname{Sum}.\operatorname{inr} r::w) = (\operatorname{fun} (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{cons} g)) (\operatorname{Sum}.\operatorname{inr} r) (\operatorname{raisingWord} i w))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.raisingWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies raisingWord.

**Definition 1.10 (raising).**

$$\forall (i : \operatorname{Bool}), (\operatorname{raising} i : ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) \to_{l} [\mathbb{C} ] ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )) = (\operatorname{Finsupp}.\operatorname{linearCombination} \mathbb{C} (\operatorname{raisingWord} i))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.raising` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies raising.

**Theorem 1.11 (cartanPreserves).**

$$\forall (a : \mathbb{C} \times \mathbb{C} ), \forall (x : ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )), (x \in N) \to \operatorname{cartan} a x \in N$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.cartanPreserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies cartanPreserves.

**Theorem 1.12 (raisingPreserves).**

$$\forall (i : \operatorname{Bool}), \forall (x : ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )), (x \in N) \to \operatorname{raising} i x \in N$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.raisingPreserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies raisingPreserves.

**Definition 1.13 (degree).**

$$(\operatorname{degree} : \mathbb{C} \times \mathbb{C} ) = ((-81/8,105/8))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.degree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies degree.

**Definition 1.14 (central).**

$$(\operatorname{central} : \mathbb{C} \times \mathbb{C} ) = ((1,-1))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.central` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies central.

**Definition 1.15 (modeWord).**

$$\forall (m : \mathbb{Z} ), (\operatorname{modeWord} m [ ] = (\operatorname{if} m < 0 \operatorname{then} (\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) [\operatorname{Sum}.\operatorname{inr} ((-m).\operatorname{toNat}.\operatorname{toPNat}')] \operatorname{else} 0)) \land (\forall (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), \operatorname{modeWord} m (g::w) = (\operatorname{if} m < 0 \operatorname{then} (\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) (\operatorname{Sum}.\operatorname{inr} ((-m).\operatorname{toNat}.\operatorname{toPNat}')::g::w) \operatorname{else} \operatorname{if} m = 0 \operatorname{then} \operatorname{cartan} \operatorname{degree} ((\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) (g::w)) \operatorname{else} \operatorname{match} g \operatorname{with} | \operatorname{Sum}.\operatorname{inl} i \mapsto (\operatorname{fun} (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{cons} g)) (\operatorname{Sum}.\operatorname{inl} i) (\operatorname{modeWord} m w) | \operatorname{Sum}.\operatorname{inr} r \mapsto (\operatorname{fun} (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{cons} g)) (\operatorname{Sum}.\operatorname{inr} r) (\operatorname{modeWord} m w) + ((m+(val\left(r\right) : \mathbb{Z} ) : \mathbb{Z} ) : \mathbb{C} ) \cdot \operatorname{modeWord} (m-val\left(r\right)) w + (\operatorname{if} m = val\left(r\right) \operatorname{then} ((m^{3}-m : \mathbb{Z} ) : \mathbb{C} ) \cdot \operatorname{cartan} \operatorname{central} ((\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) w) \operatorname{else} 0)))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.modeWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies modeWord.

**Definition 1.16 (mode).**

$$\forall (m : \mathbb{Z} ), (\operatorname{mode} m : ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) \to_{l} [\mathbb{C} ] ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )) = (\operatorname{Finsupp}.\operatorname{linearCombination} \mathbb{C} (\operatorname{modeWord} m))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.mode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies mode.

**Definition 1.17 (qleft).**

$$\forall (g : (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), (\operatorname{qleft} g : (((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) / N) \to_{l} [\mathbb{C} ] (((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) / N)) = (\operatorname{N}.\operatorname{mapQ} N ((\operatorname{fun} (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{cons} g)) g) (\operatorname{fun} x \operatorname{hx} \mapsto \operatorname{leftPreserves} g \operatorname{hx}))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qleft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies qleft.

**Definition 1.18 (qcartan).**

$$\forall (a : \mathbb{C} \times \mathbb{C} ), (\operatorname{qcartan} a : (((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) / N) \to_{l} [\mathbb{C} ] (((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) / N)) = (\operatorname{N}.\operatorname{mapQ} N (\operatorname{cartan} a) (\operatorname{fun} x \operatorname{hx} \mapsto \operatorname{cartanPreserves} a \operatorname{hx}))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies qcartan.

**Theorem 1.19 (qleft project).**

$$\forall (g : (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), \forall (x : ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )), \operatorname{qleft} g (\operatorname{N}.\operatorname{mkQ} x) = \operatorname{N}.\operatorname{mkQ} ((\operatorname{fun} (g : \operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} ) \mapsto \operatorname{Finsupp}.\operatorname{lmapDomain} \mathbb{C} \mathbb{C} (\operatorname{List}.\operatorname{cons} g)) g x)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qleft_project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qleft project.

**Theorem 1.20 (modePreserves).**

$$\forall (m : \mathbb{Z} ), \forall (x : ((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} )), (x \in N) \to \operatorname{mode} m x \in N$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.modePreserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies modePreserves.

**Definition 1.21 (qmode).**

$$\forall (m : \mathbb{Z} ), (\operatorname{qmode} m : \operatorname{Module}.\operatorname{End} \mathbb{C} (((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) / N)) = (\operatorname{N}.\operatorname{mapQ} N (\operatorname{mode} m) (\operatorname{fun} x \operatorname{hx} \mapsto \operatorname{modePreserves} m \operatorname{hx}))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies qmode.

**Theorem 1.22 (qcartan mode).**

$$\forall (a : \mathbb{C} \times \mathbb{C} ), \forall (m : \mathbb{Z} ), [ \operatorname{qcartan} a,\operatorname{qmode} m] = (-(m : \mathbb{C} )/3*(a.1+a.2)) \cdot \operatorname{qmode} m$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qcartan mode.

**Theorem 1.23 (qmode negative).**

$$\forall (r : \mathbb{N}^{+} ), \operatorname{qmode} (-(val\left(r\right) : \mathbb{Z} )) = \operatorname{qleft} (\operatorname{Sum}.\operatorname{inr} r)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qmode negative.

**Theorem 1.24 (qmode zero).**

$$\operatorname{qmode} 0 = \operatorname{qcartan} \operatorname{degree}$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qmode zero.

**Theorem 1.25 (qmode positive root).**

$$\forall (m : \mathbb{Z} ), (0 < m) \to \forall (i : \operatorname{Bool}), [ \operatorname{qmode} m,\operatorname{qleft} (\operatorname{Sum}.\operatorname{inl} i)] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode_positive_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qmode positive root.

**Definition 1.26 (qvacuum).**

$$(\operatorname{qvacuum} : (((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) / N)) = (\operatorname{N}.\operatorname{mkQ} ((\operatorname{fun} (w : \operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \mapsto \operatorname{Finsupp}.\operatorname{single} w (1 : \mathbb{C} )) [ ]))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qvacuum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies qvacuum.

**Theorem 1.27 (qmode virasoro).**

$$\forall (m n : \mathbb{Z} ), [ \operatorname{qmode} m,\operatorname{qmode} n] = ((m-n : \mathbb{Z} ) : \mathbb{C} ) \cdot \operatorname{qmode} (m+n) + \operatorname{if} m = -n \operatorname{then} ((m^{3}-m : \mathbb{Z} ) : \mathbb{C} ) \cdot \operatorname{qcartan} \operatorname{central} \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode_virasoro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qmode virasoro.

**Definition 1.28 (qraising).**

$$\forall (i : \operatorname{Bool}), (\operatorname{qraising} i : \operatorname{Module}.\operatorname{End} \mathbb{C} (((\operatorname{List} (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )) \to_{0} \mathbb{C} ) / N)) = (\operatorname{N}.\operatorname{mapQ} N (\operatorname{raising} i) (\operatorname{fun} x \operatorname{hx} \mapsto \operatorname{raisingPreserves} i \operatorname{hx}))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qraising` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies qraising.

**Theorem 1.29 (qcartan add).**

$$\forall (a b : \mathbb{C} \times \mathbb{C} ), \operatorname{qcartan} (a+b) = \operatorname{qcartan} a + \operatorname{qcartan} b$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qcartan add.

**Theorem 1.30 (qcartan smul).**

$$\forall (c : \mathbb{C} ), \forall (a : \mathbb{C} \times \mathbb{C} ), \operatorname{qcartan} (c \cdot a) = c \cdot \operatorname{qcartan} a$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qcartan smul.

**Theorem 1.31 (qcartan commute).**

$$\forall (a b : \mathbb{C} \times \mathbb{C} ), [ \operatorname{qcartan} a,\operatorname{qcartan} b] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qcartan commute.

**Theorem 1.32 (qcartan qleft).**

$$\forall (a : \mathbb{C} \times \mathbb{C} ), \forall (g : (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), [ \operatorname{qcartan} a,\operatorname{qleft} g] = \operatorname{tokenWeight} a g \cdot \operatorname{qleft} g$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_qleft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qcartan qleft.

**Theorem 1.33 (qcartan qraising).**

$$\forall (a : \mathbb{C} \times \mathbb{C} ), \forall (i : \operatorname{Bool}), [ \operatorname{qcartan} a,\operatorname{qraising} i] = -\operatorname{tokenWeight} a (\operatorname{Sum}.\operatorname{inl} i) \cdot \operatorname{qraising} i$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_qraising` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qcartan qraising.

**Theorem 1.34 (qraising qleft).**

$$\forall (i : \operatorname{Bool}), \forall (g : (\operatorname{Sum} \operatorname{Bool} \mathbb{N}^{+} )), [ \operatorname{qraising} i,\operatorname{qleft} g] = \operatorname{match} g \operatorname{with} | \operatorname{Sum}.\operatorname{inl} k \mapsto \operatorname{if} i=k \operatorname{then} \operatorname{qcartan} (\operatorname{if} i \operatorname{then} (1,0) \operatorname{else} (0,1)) \operatorname{else} 0 | \operatorname{Sum}.\operatorname{inr} \mathord{\cdot} \mapsto 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qraising_qleft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qraising qleft.

**Theorem 1.35 (qraising negative).**

$$\forall (i : \operatorname{Bool}), \forall (n : \mathbb{Z} ), (n < 0) \to [ \operatorname{qraising} i,\operatorname{qmode} n] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qraising_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies qraising negative.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.N`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.cartan`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.cartanPreserves`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.central`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.degree`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.leftPreserves`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.left_basis`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.mode`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.modePreserves`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.modeWord`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_add`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_commute`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_mode`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_qleft`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_qraising`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qcartan_smul`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qleft`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qleft_project`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode_negative`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode_positive_root`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode_virasoro`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qmode_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qraising`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qraising_negative`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qraising_qleft`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.qvacuum`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.raising`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.raisingPreserves`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.raisingWord`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.relation`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.relations`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.tokenWeight`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction.wordWeight`
- Dependency: [D5/S1/Words/WeakShuffleNormalization](../../../S1/Words/WeakShuffleNormalization.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/VBKMVirasoroBootstrap](VBKMVirasoroBootstrap.md)
