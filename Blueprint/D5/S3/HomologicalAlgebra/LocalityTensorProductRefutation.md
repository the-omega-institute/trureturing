# Locality tensor products need not be locality vector spaces

## Abstract

A locality structure on real five-space refutes both conjectures for componentwise and four-way locality.

**Definition 1.1 (Locality vector spaces).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.IsLocalityVectorSpace}\left(K, r\right)\right) \Leftrightarrow \left(\left(\forall \left(x: E\right), \left(\forall \left(y: E\right), \left(\left(r\left(x, y\right)\right) \to \left(r\left(y, x\right)\right)\right)\right)\right) \land \left(\left(r\left(\left(0: E\right), \left(0: E\right)\right)\right) \land \left(\forall \left(U: \operatorname{Set}\left(E\right)\right), \left(\exists \left(S: \operatorname{Submodule}\left(K, E\right)\right), \left(\operatorname{SetLike.coe}\left(S\right) = \{\left(x: E\right) \mid \left(\forall \left(u: E\right), \left(\left(u \in U\right) \to \left(r\left(u, x\right)\right)\right)\right)\}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.IsLocalityVectorSpace` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

A relation on a K-vector space is a locality vector-space relation when it is symmetric, relates zero to zero, and every polar set is the underlying set of a linear subspace. The polar of U consists of all x related to every u in U. This is Definition 1.1 of arXiv:2205.14616v1, Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 340–359. SetLike.coe explicitly converts the submodule S to its underlying set.

**Definition 1.2 (The locality Cartesian product).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(V: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.localityProduct}\left(r, V, W\right): \operatorname{Set}\left(E \times E\right)\right) = \{\left(p: E \times E\right) \mid \left(\left(\operatorname{Prod.fst}\left(p\right) \in V\right) \land \left(\left(\operatorname{Prod.snd}\left(p\right) \in W\right) \land \left(r\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right)\right)\right)\right)\}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.localityProduct` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

For subspaces V and W of E, retain exactly the pairs with first component in V, second component in W, and related components. This is the locality Cartesian product of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 387–394.

**Definition 1.3 (The relation on a free span).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(X: \operatorname{Type}\right), \left([\operatorname{Zero}\left(K\right)], \left(\forall \left(s: \left(X\right) \to \left(\left(X\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(a: \operatorname{Finsupp}\left(X, K\right)\right), \left(\forall \left(b: \operatorname{Finsupp}\left(X, K\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.spanRel}\left(s, a, b\right)\right) \Leftrightarrow \left(\forall \left(x: X\right), \left(\left(x \in \operatorname{Finsupp.support}\left(a\right)\right) \to \left(\forall \left(y: X\right), \left(\left(y \in \operatorname{Finsupp.support}\left(b\right)\right) \to \left(s\left(x, y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.spanRel` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

Two finitely supported coefficient functions are related when every element of the first support is related to every element of the second support. Empty supports impose no condition. The support formulation of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 755–769, needs only a zero coefficient, so the definition allows an arbitrary type K with Zero K and an arbitrary relation s.

**Definition 1.4 (The bilinearity submodule).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(V: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.bilRelations}\left(V, W\right): \operatorname{Submodule}\left(K, \operatorname{Finsupp}\left(\left(E \times E\right), K\right)\right)\right) = \operatorname{Submodule.span}\left(K, \{\left(f: \operatorname{Finsupp}\left(\left(E \times E\right), K\right)\right) \mid \left(\left(\exists \left(a: E\right), \left(\left(a \in V\right) \land \left(\exists \left(b: E\right), \left(\left(b \in V\right) \land \left(\exists \left(x: E\right), \left(\left(x \in W\right) \land \left(f = \operatorname{Finsupp.single}\left(\left(a + b, x\right), \left(1: K\right)\right) - \operatorname{Finsupp.single}\left(\left(a, x\right), \left(1: K\right)\right) - \operatorname{Finsupp.single}\left(\left(b, x\right), \left(1: K\right)\right)\right)\right)\right)\right)\right)\right)\right) \lor \left(\left(\exists \left(a: E\right), \left(\left(a \in V\right) \land \left(\exists \left(x: E\right), \left(\left(x \in W\right) \land \left(\exists \left(y: E\right), \left(\left(y \in W\right) \land \left(f = \operatorname{Finsupp.single}\left(\left(a, x + y\right), \left(1: K\right)\right) - \operatorname{Finsupp.single}\left(\left(a, x\right), \left(1: K\right)\right) - \operatorname{Finsupp.single}\left(\left(a, y\right), \left(1: K\right)\right)\right)\right)\right)\right)\right)\right)\right) \lor \left(\left(\exists \left(a: E\right), \left(\left(a \in V\right) \land \left(\exists \left(x: E\right), \left(\left(x \in W\right) \land \left(\exists \left(k: K\right), \left(f = \operatorname{Finsupp.single}\left(\left(\operatorname{HSMul.hSMul}\left(k, a\right), x\right), \left(1: K\right)\right) - \operatorname{HSMul.hSMul}\left(k, \operatorname{Finsupp.single}\left(\left(a, x\right), \left(1: K\right)\right)\right)\right)\right)\right)\right)\right)\right) \lor \left(\exists \left(a: E\right), \left(\left(a \in V\right) \land \left(\exists \left(x: E\right), \left(\left(x \in W\right) \land \left(\exists \left(k: K\right), \left(f = \operatorname{Finsupp.single}\left(\left(a, \operatorname{HSMul.hSMul}\left(k, x\right)\right), \left(1: K\right)\right) - \operatorname{HSMul.hSMul}\left(k, \operatorname{Finsupp.single}\left(\left(a, x\right), \left(1: K\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.bilRelations` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

In the free K-vector space on all pairs from E, take the span of the two additivity relations and the two scalar relations, with a and b in V and x and y in W. Finsupp.single assigns the coefficient one in K to the indicated pair. The generators are exactly those of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 422–430; they need not themselves have local support.

**Definition 1.5 (The free span of local pairs).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(V: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right): \operatorname{Submodule}\left(K, \operatorname{Finsupp}\left(\left(E \times E\right), K\right)\right)\right) = \operatorname{Finsupp.supported}\left(K, K, \operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.localityProduct}\left(r, V, W\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.freeSpan` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

This submodule consists of the finitely supported functions whose support lies in the locality Cartesian product. It realizes the free span K(V ×_⊤ W) used in the locality tensor product, Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 556–562, inside the free span on all pairs from E.

**Definition 1.6 (Bilinearity relations with local support).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(V: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.bilIdeal}\left(r, V, W\right): \operatorname{Submodule}\left(K, \operatorname{Finsupp}\left(\left(E \times E\right), K\right)\right)\right) = \operatorname{Min.min}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.bilRelations}\left(V, W\right), \operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.bilIdeal` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

Intersect the ambient bilinearity submodule with the free span of local pairs. Thus an element must both be a linear combination of bilinearity relations and have local support; the individual relations in that combination need not have local support. This is the subspace I_bil intersected with K(V ×_⊤ W) in Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 1984–1987, used as the denominator in lines 556–562. Min.min denotes the meet of submodules.

**Definition 1.7 (The locality tensor product).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(V: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.localityTensor}\left(r, V, W\right): \operatorname{Type}\right) = \operatorname{HasQuotient.Quotient}\left(\operatorname{CoeSort.coe}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right)\right), \operatorname{Submodule.comap}\left(\operatorname{Submodule.subtype}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right)\right), \operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.bilIdeal}\left(r, V, W\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.localityTensor` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

The locality tensor product is the free span of local pairs modulo its bilinearity subspace, as in the definition in Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 556–562. CoeSort.coe explicitly regards the free-span submodule as a type of elements. Taking the inverse image under Submodule.subtype puts the denominator inside that type before forming the quotient.

**Definition 1.8 (Pairwise locality of four entries).**

$$\forall \left(E: \operatorname{Type}\right), \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(p: E \times E\right), \left(\forall \left(q: E \times E\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.fourWay}\left(E, r, p, q\right)\right) \Leftrightarrow \left(\left(r\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right)\right) \land \left(\left(r\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.fst}\left(q\right)\right)\right) \land \left(\left(r\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(q\right)\right)\right) \land \left(\left(r\left(\operatorname{Prod.snd}\left(p\right), \operatorname{Prod.fst}\left(q\right)\right)\right) \land \left(\left(r\left(\operatorname{Prod.snd}\left(p\right), \operatorname{Prod.snd}\left(q\right)\right)\right) \land \left(r\left(\operatorname{Prod.fst}\left(q\right), \operatorname{Prod.snd}\left(q\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.fourWay` (`✓ std3`).

*Citation.* Pierre J. Clavier (2025). *TRAPs, Generalisations of MZVs, Locality and Resurgence for Quantum Field Theories*. URL: <https://arxiv.org/abs/2506.09493v1>.

*Commentary.*

The four entries p₁, p₂, q₁ and q₂ must be pairwise related: all six unordered pairs satisfy r. The pairs within each generator are included. This is the literal four-entry condition of arXiv:2506.09493v1, LOC.tex, lines 220 and 743–747. It implies the relational product Prod.RProd r r, namely r(v,v′) ∧ r(w,w′). This componentwise reading is the relation of arXiv:2205.14616v1, Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 447–449. The two relations need not coincide even when V = W.

**Definition 1.9 (Existential locality on the quotient).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(s: \left(E \times E\right) \to \left(\left(E \times E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(V: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(a: \operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.localityTensor}\left(r, V, W\right)\right), \left(\forall \left(b: \operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.localityTensor}\left(r, V, W\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.quotientRel}\left(r, s, V, W, a, b\right)\right) \Leftrightarrow \left(\operatorname{Relation.Map}\left(\lambda \left(u: \operatorname{CoeSort.coe}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right)\right)\right) \mapsto \left(\lambda \left(v: \operatorname{CoeSort.coe}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right)\right)\right) \mapsto \left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.spanRel}\left(s, \operatorname{Subtype.val}\left(u\right), \operatorname{Subtype.val}\left(v\right)\right)\right)\right), \operatorname{Submodule.Quotient.mk}, \operatorname{Submodule.Quotient.mk}, a, b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.quotientRel` (`✓ std3`).

*Citation.* Pierre J. Clavier (2025). *TRAPs, Generalisations of MZVs, Locality and Resurgence for Quantum Field Theories*. URL: <https://arxiv.org/abs/2506.09493v1>.

*Commentary.*

For a generator relation s, two quotient classes are related if they have representatives whose supports are related by s. Subtype.val explicitly takes each representative to its ambient coefficient function. Relation.Map takes the direct image under the two quotient maps; it requires the existence of related representatives, as in arXiv:2506.09493v1, LOC.tex, lines 606–612. The componentwise and four-way generator relations give the two readings considered here.

**Definition 1.10 (Locality-compatible subspaces).**

$$\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.LocalityCompatible}\left(r, W\right)\right) \Leftrightarrow \left(\forall \left(x: E\right), \left(\forall \left(y: E\right), \left(\forall \left(z: E\right), \left(\forall \left(w: E\right), \left(\left(w \in W\right) \to \left(\left(r\left(x, y\right)\right) \to \left(\left(r\left(x + w, z\right)\right) \to \left(\exists \left(w': E\right), \left(\left(w' \in W\right) \land \left(\left(r\left(x + w', y\right)\right) \land \left(r\left(x + w', z\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.LocalityCompatible` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

A subspace W is locality compatible when the following simultaneous adjustment is possible. If x is related to y and x + w is related to z for some w in W, then a single adjustment w′ in W makes x + w′ related to both y and z. This is Definition 6.7 of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 1880–1886. The predicate itself is defined for any relation r.

**Definition 1.11 (The locality tensor-product conjecture).**

$$\forall \left(s: \forall \left(E: \operatorname{Type}\right), \left(\left(\left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right) \to \left(\left(E \times E\right) \to \left(\left(E \times E\right) \to \left(\operatorname{Prop}\right)\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.TensorConjecture}\left(s\right)\right) \Leftrightarrow \left(\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{CharZero}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(V: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.IsLocalityVectorSpace}\left(K, r\right)\right) \to \left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.IsLocalityVectorSpace}\left(K, \operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.quotientRel}\left(r, s\left(E, r\right), V, W\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.TensorConjecture` (`✓ std3`).

*Citation.* Pierre J. Clavier (2025). *TRAPs, Generalisations of MZVs, Locality and Resurgence for Quantum Field Theories*. URL: <https://arxiv.org/abs/2506.09493v1>.

*Commentary.*

For a chosen generator-relation rule s, every field K of characteristic zero and K-vector space E, every locality relation r and every pair of subspaces V and W, the conjecture asserts that the quotient locality on the locality tensor product is a locality vector-space relation. This is Conjecture conj:loc_tensor of arXiv:2506.09493v1, LOC.tex, lines 1797–1799. The thesis states no characteristic restriction. Here K has characteristic zero, as in the paper's Notations, Clavier_Foissy_Lopez_Paycha_arxiv.tex, line 321. Refuting this restricted assertion also refutes the unrestricted thesis assertion. Its literal thesis reading uses fourWay; the componentwise reading uses the relation of source 1. K and E range over Type, without a finite-dimensionality hypothesis.

**Definition 1.12 (The locality-compatibility conjecture).**

$$\forall \left(s: \forall \left(E: \operatorname{Type}\right), \left(\left(\left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right) \to \left(\left(E \times E\right) \to \left(\left(E \times E\right) \to \left(\operatorname{Prop}\right)\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.PairConjecture}\left(s\right)\right) \Leftrightarrow \left(\forall \left(K: \operatorname{Type}\right), \left(\forall \left(E: \operatorname{Type}\right), \left([\operatorname{Field}\left(K\right)], \left([\operatorname{CharZero}\left(K\right)], \left([\operatorname{AddCommGroup}\left(E\right)], \left([\operatorname{Module}\left(K, E\right)], \left(\forall \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(V: \operatorname{Submodule}\left(K, E\right)\right), \left(\forall \left(W: \operatorname{Submodule}\left(K, E\right)\right), \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.IsLocalityVectorSpace}\left(K, r\right)\right) \to \left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.LocalityCompatible}\left(\lambda \left(a: \operatorname{CoeSort.coe}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right)\right)\right) \mapsto \left(\lambda \left(b: \operatorname{CoeSort.coe}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right)\right)\right) \mapsto \left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.spanRel}\left(s\left(E, r\right), \operatorname{Subtype.val}\left(a\right), \operatorname{Subtype.val}\left(b\right)\right)\right)\right), \operatorname{Submodule.comap}\left(\operatorname{Submodule.subtype}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.freeSpan}\left(r, V, W\right)\right), \operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.bilIdeal}\left(r, V, W\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.PairConjecture` (`✓ std3`).

*Citation.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

For the same fields K of characteristic zero, vector spaces and subspaces, the conjecture asserts that the bilinearity subspace inside the free span of local pairs is locality compatible with the support relation induced by the chosen generator-relation rule s. Conjectural statement 6.16 of Clavier_Foissy_Lopez_Paycha_arxiv.tex, lines 1984–1987, uses componentwise locality. Its characteristic-zero restriction is specified in the paper's Notations, line 321. The four-way variant uses the thesis relation on the same generators.

**Definition 1.13 (The disjunction of all four assertions).**

$$\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.claim}\right) \Leftrightarrow \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.TensorConjecture}\left(\lambda \left(E: \operatorname{Type}\right) \mapsto \left(\lambda \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right) \mapsto \left(\operatorname{Prod.RProd}\left(r, r\right)\right)\right)\right)\right) \lor \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.TensorConjecture}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.fourWay}\right)\right) \lor \left(\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.PairConjecture}\left(\lambda \left(E: \operatorname{Type}\right) \mapsto \left(\lambda \left(r: \left(E\right) \to \left(\left(E\right) \to \left(\operatorname{Prop}\right)\right)\right) \mapsto \left(\operatorname{Prod.RProd}\left(r, r\right)\right)\right)\right)\right) \lor \left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.PairConjecture}\left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.fourWay}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

The proposition asserts that at least one of the tensor-product or locality-compatibility conjectures holds under either componentwise or four-way locality. Its negation refutes all four assertions separately.

**Theorem 1.14 (A counterexample to both conjectures under both relations).**

$$\neg \left(\operatorname{D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/clavier-foissy-lopez-paycha-2022-locality-tensor-product-refutation` (refuted) by `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"clavier-foissy-lopez-paycha-2022-locality-tensor-product-refutation","declaration_gid":"D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha (2022). *Tensor products and the Milnor-Moore theorem in the locality setup*. DOI: [10.1007/s40879-025-00822-z](https://doi.org/10.1007/s40879-025-00822-z). URL: <https://arxiv.org/abs/2205.14616v1>.

*Commentary.*

Take K = ℝ, E = ℝ⁵ with coordinates indexed by Fin 5, and V = W = E. Let P(v) = (v₀,v₁,v₂). In ℝ³ take the six lines spanned, in order, by (0,1,0), (1,1,0), (1,−1,0), (0,0,1), (1,0,1) and (1,0,−1). Define R(v,t) by requiring that P(v) = 0 or P(t) = 0 or the two projections lie on a common one of these lines, together with v₃t₂ = t₃v₂ = v₄t₁ = t₄v₁ = 0.

A nonzero vector of ℝ³ belongs to at most one of the six lines: equating scalar multiples of their directions and comparing their three coordinates proves this for each pair of directions. Consequently, for fixed v, the projected part of its polar is all of E when P(v) = 0, the inverse image of the unique line containing P(v) when there is such a line, and the kernel of P otherwise. Each is a subspace. The four additional equations are linear in t, so the full singleton polar is a subspace. The relation is symmetric and relates zero to zero. The polar of any set is the intersection of its singleton polars, hence R makes E a locality vector space.

Write [v,t] for the single generator at the pair (v,t), with real coefficient one, and eᵢ for the coordinate vectors. For k = 1,2 put Aₖ = ½[e₀ + eₖ,e₀ + eₖ] + ½[e₀ − eₖ,e₀ − eₖ] − [eₖ,eₖ], and put c₃ = [e₃,e₃], c₄ = [e₄,e₄]. All generators of A₁ and A₂ are local: their projections have one of the six specified directions and their last two coordinates vanish. The generators c₃ and c₄ are also local because their projections vanish. Thus these four elements lie in the free span of local pairs.

Expanding the two additivity relations and the scalar relations for multiplication by −1 shows that Aₖ − [e₀,e₀] belongs to the ambient bilinearity submodule. More explicitly, expand [e₀ + eₖ,e₀ + eₖ] in both entries, expand [e₀ − eₖ,e₀ − eₖ] in the same way, and replace terms with a negative entry by their scalar relations. Half their sum is congruent to [e₀,e₀] + [eₖ,eₖ]. Subtracting the identities for k = 2 and k = 1 gives A₂ − A₁ in that submodule. Its local support places the difference in the intersection defining the bilinearity subspace. Checking the three possible support pairs of each Aₖ also gives that A₁ is support-related to c₃ and A₂ is support-related to c₄ under both generator relations. Every generator used here is diagonal, of the form (v,v). Local support supplies R(v,v), so the componentwise cross relation supplies all four cross pairs and the local diagonal pairs supply the remaining two conditions of four-way locality.

For each i in Fin 5, extend [v,t] ↦ vᵢtᵢ linearly to a real functional Fᵢ on the ambient free span. Each functional vanishes on every bilinearity generator by distributivity and scalar multiplication; linearity then makes it vanish on their entire span. Direct evaluation gives F₀(A₁) = 1, F₃(c₃) = 1, F₄(c₄) = 1, and F₃(c₃ + c₄) = F₄(c₃ + c₄) = 1. Whenever Fᵢ of a finitely supported element is nonzero, some pair (v,t) in its support has vᵢtᵢ nonzero, since otherwise every term in its defining finite sum would vanish.

If R(v,t) and v₀t₀ ≠ 0, neither projection vanishes. A common line must then be one of those whose direction has first coordinate one, so v₁ ≠ 0 or v₂ ≠ 0. Now suppose a,b,c have local support, F₀(a) ≠ 0, F₃(b) ≠ 0 and F₄(c) ≠ 0, and a is support-related to both b and c. Choose support pairs (v,t) of a, (u,s) of b and (h,j) of c with v₀t₀ ≠ 0, u₃s₃ ≠ 0 and h₄j₄ ≠ 0. Either generator relation implies componentwise relatedness, giving R(v,u) and R(v,h). The equations u₃v₂ = 0 and h₄v₁ = 0 force v₂ = v₁ = 0. But the pair (v,t) has local support, contradicting the preceding alternative. Finally, equality of quotient classes makes the difference of representatives lie in the bilinearity subspace, so every Fᵢ has equal values on equal quotient classes.

To refute locality compatibility, take x = A₁, x′ = A₂, y = c₃, z = c₄ and w = x′ − x. The element w belongs to the bilinearity subspace, x is related to y, and x + w = x′ is related to z. Compatibility would supply an adjustment w′ in that subspace such that x + w′ is related to both y and z. Yet F₀(x + w′) = F₀(A₁) = 1, while F₃(y) = F₄(z) = 1. The obstruction for the three elements x + w′, y, z gives a contradiction.

For the tensor-product conjecture, let q be the quotient map. Since A₂ − A₁ belongs to its kernel, q(A₂) = q(A₁). The related representatives already found imply that q(A₁) is related to both q(c₃) and q(c₄). If the quotient relation were a locality vector-space relation, the polar of the singleton {q(A₁)} would be a subspace. Closure under addition would make q(A₁) related to q(c₃ + c₄). Choose related representatives a,b of these two classes. Invariance of the functionals on classes gives F₀(a) = 1 and F₃(b) = F₄(b) = 1. Applying the same obstruction to a,b,b is impossible. Both arguments apply to each generator relation: diagonal generators provide the positive relations, and projection to componentwise locality gives the same obstruction. Thus both conjectures are false for both relations, negating the four-term disjunction.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.IsLocalityVectorSpace`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.LocalityCompatible`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.PairConjecture`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.TensorConjecture`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.bilIdeal`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.bilRelations`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.claim`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.fourWay`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.freeSpan`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.localityProduct`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.localityTensor`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.quotientRel`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.result`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.spanRel`
