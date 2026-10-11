# Two walls in the literal cyclic word space

## Abstract

Literal cyclic words with two walls carry the three eclectic bond operators and a commuting right shift.

Let a and b be natural numbers and L = a+b+2. The positions form ZMod(L). The letters one, two and wall denote the physical letters 1, 2 and 3, respectively; their Fin(3) encodings are 0, 1 and 2. Words retain their positions and are not identified under rotation. The vector space over any field K consists of finite linear combinations of counted words. Its delta vector at w has coefficient one at w and zero elsewhere. Endomorphism multiplication means composition, with the right factor acting first.

**Definition 1.1 (The three-letter type).**

$$\operatorname{Letter} = \operatorname{Fin}\left(3\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.Letter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The letter type has exactly three elements.

**Definition 1.2 (Letter one).**

$$\operatorname{one} = 0$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first encoding denotes letter 1.

**Definition 1.3 (Letter two).**

$$\operatorname{two} = 1$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.two` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second encoding denotes letter 2.

**Definition 1.4 (The wall).**

$$\operatorname{wall} = 2$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.wall` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The third encoding denotes the wall 3.

**Definition 1.5 (Cyclic positions).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Pos}\left(a, b\right) = \operatorname{ZMod}\left(a + b + 2\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.Pos` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Addition of positions is taken modulo L, so the last and first positions are adjacent.

**Definition 1.6 (Positive cyclic length).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{lengthNeZero}\left(a, b\right) = \operatorname{NeZeroMk}\left(\operatorname{proofOf}\left(\neg(a + b + 2 = 0)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.lengthNeZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum a+b+2 is nonzero. NeZeroMk packages this proof and supplies the finite enumeration of cyclic positions.

**Definition 1.7 (Counting a letter).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Letter},\; \forall w \in (\operatorname{Pos}\left(a, b\right) \to \operatorname{Letter}),\; \operatorname{count}\left(c, w\right) = \sum_{p\in\operatorname{Pos}\left(a, b\right)} (\operatorname{ite}\left(w\left(p\right) = c, 1, 0\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each site contributes one exactly when its letter equals c.

**Definition 1.8 (Counted literal words).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Word}\left(a, b\right) = \operatorname{Subtype}\left(((w : \operatorname{Pos}\left(a, b\right) \to \operatorname{Letter}) \mapsto (\operatorname{count}\left(\operatorname{one}, w\right) = a) \land ((\operatorname{count}\left(\operatorname{two}, w\right) = b) \land (\operatorname{count}\left(\operatorname{wall}, w\right) = 2)))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype retains exactly a ones, b twos and two walls. The three count certificates restrict the complete function space. The finite ambient function type and decidable count predicates give Word its inherited Fintype instance.

**Definition 1.9 (Transport along a site permutation).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall e \in \operatorname{Perm}\left(\operatorname{Pos}\left(a, b\right)\right),\; \forall w \in \operatorname{Word}\left(a, b\right),\; \forall p \in \operatorname{Pos}\left(a, b\right),\; (\operatorname{coe}\left(\operatorname{permute}\left(e\right)\left(w\right)\right)\left(p\right) = \operatorname{coe}\left(w\right)\left(\operatorname{inverse}\left(e\right)\left(p\right)\right)) \land (\operatorname{coe}\left(\operatorname{inverse}\left(\operatorname{permute}\left(e\right)\right)\left(w\right)\right)\left(p\right) = \operatorname{coe}\left(w\right)\left(e\left(p\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.permute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map composes a word with the inverse site permutation; the inverse map composes with the permutation itself. Reindexing the finite count sum preserves every letter count, so both maps land in the counted subtype.

**Definition 1.10 (Right rotation).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall t \in \operatorname{Pos}\left(a, b\right),\; \operatorname{rotate}\left(t\right) = \operatorname{permute}\left(\operatorname{addRight}\left(t\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.rotate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position map addRight(t) sends p to p+t. The transported word thus reads w(p−t), giving the source's right-shift convention.

**Definition 1.11 (Swapping a cyclic bond).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall p \in \operatorname{Pos}\left(a, b\right),\; \operatorname{swapWord}\left(p\right) = \operatorname{permute}\left(\operatorname{swap}\left(p, p + 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.swapWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same permutation exchanges both cyclically adjacent sites and fixes all other sites.

**Definition 1.12 (Oriented allowed inputs).**

$$\operatorname{inputPair} = \operatorname{vector3}\left((\operatorname{wall}, \operatorname{two}), (\operatorname{one}, \operatorname{wall}), (\operatorname{two}, \operatorname{one})\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.inputPair` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

In arXiv:2112.04506v1, Section 2.1, Eq. (2.3), the three transitions are 32 to 23, 13 to 31, and 21 to 12. Every other input pair is annihilated.

**Definition 1.13 (The input-pair predicate).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall w \in \operatorname{Word}\left(a, b\right),\; \forall p \in \operatorname{Pos}\left(a, b\right),\; (\operatorname{Allowed}\left(i, w, p\right)) \Leftrightarrow ((\operatorname{coe}\left(w\right)\left(p\right) = \operatorname{first}\left(\operatorname{inputPair}\left(i\right)\right)) \land (\operatorname{coe}\left(w\right)\left(p + 1\right) = \operatorname{second}\left(\operatorname{inputPair}\left(i\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.Allowed` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The test reads the ordered pair at p and p+1 before exchanging the sites.

**Definition 1.14 (Decidable input test).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall w \in \operatorname{Word}\left(a, b\right),\; \forall p \in \operatorname{Pos}\left(a, b\right),\; \operatorname{allowedDecidable}\left(i, w, p\right) = \operatorname{inferInstance}\left(\operatorname{Decidable}\left(\operatorname{Allowed}\left(i, w, p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.allowedDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equality of the finite letters decides both parts of the input test.

**Definition 1.15 (The word vector space).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall K \in \operatorname{Type},\; [\operatorname{Zero}\left(K\right)] \operatorname{Space}\left(K, a, b\right) = \operatorname{Finsupp}\left(\operatorname{Word}\left(a, b\right), K\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.Space` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finsupp consists of functions with finite support. Since the word type is finite, every coefficient function has finite support.

**Definition 1.16 (The canonical word basis).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{basis}\left(K, a, b\right) = \operatorname{FinsuppBasisSingleOne}\left(K, \operatorname{Word}\left(a, b\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.basis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standard finitely supported function basis is indexed by all counted words. Its coordinates give unique expansions into delta vectors.

**Definition 1.17 (Delta vectors).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(a, b\right),\; \operatorname{delta}\left(K, w\right) = \operatorname{basis}\left(K, a, b\right)\left(w\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delta vectors are the canonical basis of the finitely supported function space.

**Definition 1.18 (One local transition).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall p \in \operatorname{Pos}\left(a, b\right),\; \forall w \in \operatorname{Word}\left(a, b\right),\; \operatorname{bond}\left(K, i, p, w\right) = \operatorname{ite}\left(\operatorname{Allowed}\left(i, w, p\right), \operatorname{delta}\left(K, \operatorname{swapWord}\left(p\right)\left(w\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.bond` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The local action is the delta vector at the exchanged word when the input test succeeds, and zero otherwise. This is the action in Eq. (2.3), restricted to words with two walls.

**Definition 1.19 (The bond sum).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{F}\left(K, a, b, i\right) = \operatorname{linearCombination}\left(K, ((w : \operatorname{Word}\left(a, b\right)) \mapsto \sum_{p\in\operatorname{Pos}\left(a, b\right)} (\operatorname{bond}\left(K, i, p, w\right)))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.F` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

LinearCombination extends the displayed image of each delta vector linearly. The sum runs over all positions, as in Eq. (2.2); different bonds leading to the same word contribute separately.

**Definition 1.20 (The first bond operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{F1}\left(K, a, b\right) = \operatorname{F}\left(K, a, b, 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.F1` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

F1 sums the transitions 32 to 23.

**Definition 1.21 (The second bond operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{F2}\left(K, a, b\right) = \operatorname{F}\left(K, a, b, 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.F2` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

F2 sums the transitions 13 to 31.

**Definition 1.22 (The third bond operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{F3}\left(K, a, b\right) = \operatorname{F}\left(K, a, b, 2\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.F3` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

F3 sums the transitions 21 to 12.

**Definition 1.23 (The coupled eclectic operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall xi \in (\operatorname{Fin}\left(3\right) \to K),\; \operatorname{T}\left(K, a, b, xi\right) = xi\left(0\right) \cdot \operatorname{F1}\left(K, a, b\right) + xi\left(1\right) \cdot \operatorname{F2}\left(K, a, b\right) + xi\left(2\right) \cdot \operatorname{F3}\left(K, a, b\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.T` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The three couplings multiply the three bond sums, as in Eq. (2.2). No nonzero-coupling or characteristic-zero assumption is needed for this action.

**Definition 1.24 (Linear translation).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall t \in \operatorname{Pos}\left(a, b\right),\; \operatorname{translation}\left(K, t\right) = \operatorname{lmapDomain}\left(K, K, \operatorname{rotate}\left(t\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.translation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map pushes each basis label forward by right rotation.

**Definition 1.25 (The one-site right shift).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{U}\left(K, a, b\right) = \operatorname{translation}\left(K, 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWords.U` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Section 2.2, Eq. (2.9), uses U on the elementary state j1…jL to give jL j1…j(L−1). This is rotation by one in the literal word coordinates.

**Theorem 1.26 (Count preservation, delta actions and translation symmetry).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (\forall c \in \operatorname{Letter},\; \forall p \in \operatorname{Pos}\left(a, b\right),\; \forall w \in (\operatorname{Pos}\left(a, b\right) \to \operatorname{Letter}),\; \operatorname{count}\left(c, ((q : \operatorname{Pos}\left(a, b\right)) \mapsto w\left(\operatorname{swap}\left(p, p + 1\right)\left(q\right)\right))\right) = \operatorname{count}\left(c, w\right)) \land ((\forall t \in \operatorname{Pos}\left(a, b\right),\; \forall w \in \operatorname{Word}\left(a, b\right),\; \operatorname{translation}\left(K, t\right)\left(\operatorname{delta}\left(K, w\right)\right) = \operatorname{delta}\left(K, \operatorname{rotate}\left(t\right)\left(w\right)\right)) \land ((\forall w \in \operatorname{Word}\left(a, b\right),\; \operatorname{U}\left(K, a, b\right)\left(\operatorname{delta}\left(K, w\right)\right) = \operatorname{delta}\left(K, \operatorname{rotate}\left(1\right)\left(w\right)\right)) \land ((\forall i \in \operatorname{Fin}\left(3\right),\; \forall w \in \operatorname{Word}\left(a, b\right),\; \operatorname{F}\left(K, a, b, i\right)\left(\operatorname{delta}\left(K, w\right)\right) = \sum_{p\in\operatorname{Pos}\left(a, b\right)} (\operatorname{bond}\left(K, i, p, w\right))) \land ((\operatorname{U}\left(K, a, b\right)^{a + b + 2} = 1) \land ((\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{U}\left(K, a, b\right) \cdot \operatorname{F}\left(K, a, b, i\right) = \operatorname{F}\left(K, a, b, i\right) \cdot \operatorname{U}\left(K, a, b\right)) \land (\forall xi \in (\operatorname{Fin}\left(3\right) \to K),\; \operatorname{U}\left(K, a, b\right) \cdot \operatorname{T}\left(K, a, b, xi\right) = \operatorname{T}\left(K, a, b, xi\right) \cdot \operatorname{U}\left(K, a, b\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TwoWallWords.cyclic_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A swap is a permutation of sites, so finite-sum reindexing preserves every count. Translation carries the bond at p to the bond at p+t, with the same oriented input test and exchanged output. Reindexing the complete bond sum therefore gives commutation. Repeated right shifts add their displacements in ZMod(L); displacement L is zero. The coupling formula inherits commutation by linearity.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.Allowed`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.F`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.F1`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.F2`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.F3`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.Letter`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.Pos`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.Space`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.T`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.U`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.Word`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.allowedDecidable`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.basis`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.bond`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.count`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.cyclic_action`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.delta`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.inputPair`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.lengthNeZero`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.one`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.permute`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.rotate`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.swapWord`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.translation`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.two`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWords.wall`
