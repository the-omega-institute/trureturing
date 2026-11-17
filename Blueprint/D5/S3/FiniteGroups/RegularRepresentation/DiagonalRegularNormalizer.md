# Coordinates of the Diagonal Regular Normalizer

## Abstract

For any group H and nonempty label type K, the ambient normalizer of simultaneous left translations on K times H has unique coordinates consisting of a label permutation, one common group automorphism and source-indexed right translations, with an explicit equivalence of types and evaluation law.

Let K : Type u and H : Type v be arbitrary types, with H a group. Write Sym(K times H) for Equiv.Perm (K times H), with multiplication given by composition. For h in H, the same left translation L(h) acts on every label: L(h)(i,x) = (i,h*x). The subgroup D is the actual range of h mapping to L(h), and N is its normalizer in this ambient symmetric group. The formulas below use diagonalHom, diagonal and diagonalNormalizer for L, D and N. Typeu and Typev denote arbitrary, independently chosen type universes.

**Definition 1.1 (Simultaneous left translation on every label).**

$$\forall K \in Typeu,\; \forall H \in Typev,\; [\operatorname{Group}\left(H\right)], \forall h \in H,\; \forall i \in K,\; \forall x \in H,\; \operatorname{diagonalHom}\left(K, H\right)\left(h\right)\left((i, x)\right) = (i, h \cdot x)$$

*Formalization.* `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.diagonalHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

diagonalHom K H is a monoid homomorphism from H to Perm (K times H). The label action is trivial and the action on H is left multiplication, so its evaluation is exactly the displayed formula.

**Definition 1.2 (The diagonal subgroup is the actual translation range).**

$$\forall K \in Typeu,\; \forall H \in Typev,\; [\operatorname{Group}\left(H\right)], \operatorname{diagonal}\left(K, H\right) = \left\{\operatorname{diagonalHom}\left(K, H\right)\left(h\right) \mid h \in H\right\}$$

*Formalization.* `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.diagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed set is range (diagonalHom K H), regarded as a subgroup of Perm (K times H). Its elements use one and the same h at every label. There is no independently chosen translation parameter for each label in D.

**Definition 1.3 (The normalizer in the ambient symmetric group).**

$$\forall K \in Typeu,\; \forall H \in Typev,\; [\operatorname{Group}\left(H\right)], \operatorname{diagonalNormalizer}\left(K, H\right) = \left(\operatorname{N}_{\operatorname{Perm}\left(K \times H\right)}\right)\left(\operatorname{diagonal}\left(K, H\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.diagonalNormalizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N with subscript Perm (K times H) denotes Subgroup.normalizer of the underlying set of D in that ambient group. Thus p belongs to N exactly when conjugation by the actual permutation p preserves D in both directions.

**Definition 1.4 (The type of permutation, automorphism and translation coordinates).**

$$\forall K \in Typeu,\; \forall H \in Typev,\; [\operatorname{Group}\left(H\right)], \operatorname{Parameters}\left(K, H\right) = \operatorname{Perm}\left(K\right) \times (\operatorname{MulAut}\left(H\right) \times (K \to H))$$

*Formalization.* `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.Parameters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A parameter is the right-associated triple (sigma,alpha,b), where sigma is a permutation of K, alpha is a multiplicative group automorphism of H, and b is a function from K to H. In the formulas fst(t), fst(snd(t)) and snd(snd(t)) are these three coordinates. This is a product type; no group operation on triples is specified.

**Definition 1.5 (The ambient permutation determined by coordinates).**

$$\forall K \in Typeu,\; \forall H \in Typev,\; [\operatorname{Group}\left(H\right)], \forall sigma \in \operatorname{Perm}\left(K\right),\; \forall alpha \in \operatorname{MulAut}\left(H\right),\; \forall b \in K \to H,\; \forall i \in K,\; \forall x \in H,\; \operatorname{coordinatePerm}\left(K, H, (sigma, (alpha, b))\right)\left((i, x)\right) = (sigma\left(i\right), alpha\left(x\right) \cdot b\left(i\right))$$

*Formalization.* `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.coordinatePerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equiv.prodCongrRight first applies alpha followed by right multiplication by b(i) on the H coordinate, and Equiv.prodCongr then applies sigma to the label. The translation is indexed by the source label i. The order alpha(x)*b(i) is essential for a possibly noncommutative H: these are right translations.

**Definition 1.6 (An equivalence of types between the actual normalizer and coordinates).**

$$\forall K \in Typeu,\; \forall H \in Typev,\; [\operatorname{Group}\left(H\right)], [\operatorname{Nonempty}\left(K\right)], \operatorname{normalizerEquiv}\left(K, H\right): \operatorname{Equiv}\left(\operatorname{diagonalNormalizer}\left(K, H\right), \operatorname{Parameters}\left(K, H\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.normalizerEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With nonempty K, normalizerEquiv is a type equivalence N to Parameters K H. Its inverse sends a triple to coordinatePerm together with membership in the actual ambient normalizer. It is not stated as a group equivalence, and no multiplication law for the parameter triples is part of this definition.

**Theorem 1.7 (Evaluation of the coordinates of a normalizing permutation).**

$$\forall K \in Typeu,\; \forall H \in Typev,\; [\operatorname{Group}\left(H\right)], [\operatorname{Nonempty}\left(K\right)], \forall p \in \operatorname{diagonalNormalizer}\left(K, H\right),\; \forall i \in K,\; \forall x \in H,\; p\left((i, x)\right) = (\operatorname{fst}\left(\operatorname{normalizerEquiv}\left(K, H, p\right)\right)\left(i\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{normalizerEquiv}\left(K, H, p\right)\right)\right)\left(x\right) \cdot \operatorname{snd}\left(\operatorname{snd}\left(\operatorname{normalizerEquiv}\left(K, H, p\right)\right)\right)\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.normalizerEquiv_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p in N, take t = normalizerEquiv K H p. The formula is p(i,x) = (sigma(i),alpha(x)*b(i)) with exactly the three projections of t. This evaluation supplies the coordinate equality in the forward implication of the membership classification and identifies the reconstructed permutation.

**Theorem 1.8 (Full ambient-normalizer classification with unique coordinates).**

$$\forall K \in Typeu,\; \forall H \in Typev,\; [\operatorname{Group}\left(H\right)], [\operatorname{Nonempty}\left(K\right)], \forall p \in \operatorname{Perm}\left(K \times H\right),\; p \in \left(\operatorname{N}_{\operatorname{Perm}\left(K \times H\right)}\right)\left(\operatorname{diagonal}\left(K, H\right)\right) \Leftrightarrow \left(\exists t \in \operatorname{Parameters}\left(K, H\right),\; \left(\forall i \in K,\; \forall x \in H,\; p\left((i, x)\right) = (\operatorname{fst}\left(t\right)\left(i\right), \operatorname{fst}\left(\operatorname{snd}\left(t\right)\right)\left(x\right) \cdot \operatorname{snd}\left(\operatorname{snd}\left(t\right)\right)\left(i\right))\right) \land \left(\forall s \in \operatorname{Parameters}\left(K, H\right),\; \left(\forall i \in K,\; \forall x \in H,\; p\left((i, x)\right) = (\operatorname{fst}\left(s\right)\left(i\right), \operatorname{fst}\left(\operatorname{snd}\left(s\right)\right)\left(x\right) \cdot \operatorname{snd}\left(\operatorname{snd}\left(s\right)\right)\left(i\right))\right) \Rightarrow s = t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.mem_normalizer_iff_existsUnique_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every ambient permutation p, membership in N is equivalent to existence of a triple with the coordinate formula for every i and x, together with equality of every other such triple to it. The displayed existential and universal condition expands unique existence in the right-associated product Perm K times MulAut H times (K to H). A single alpha governs every label.

To reconstruct coordinates, first identify H with the actual diagonal range by the faithful-action equivalence Equiv.Perm.subgroupOfMulAction. Normalization gives an automorphism of D through Subgroup.normalizerMonoidHom. Transport it with MulAut.congr to obtain alpha on H before selecting any reference label. Conjugation in the ambient group gives L(alpha(h)) = p*L(h)*p inverse, hence the twisted equivariance equation p(i,h*x) = (fst(p(i,x)),alpha(h)*snd(p(i,x))). Thus the common automorphism comes from one conjugation action, rather than separate choices on different blocks.

Set k(i) = fst(p(i,1)) and b(i) = snd(p(i,1)). Substituting x at the identity into twisted equivariance gives p(i,x) = (k(i),alpha(x)*b(i)). It remains to prove that k is a permutation. If k(i) = k(j), choose x = alpha inverse (b(i)*b(j) inverse). Then p(j,x) = p(i,1), so injectivity of p forces i = j. To reach a label j, take any preimage of (j,1) under p; the coordinate formula shows that its source label maps to j under k. These arguments give both injectivity and surjectivity without finiteness, so k determines sigma in Perm K.

Conversely, the coordinate construction is an actual bijection of K times H. Computing its conjugation gives p*L(h)*p inverse = L(alpha(h)) in Sym(K times H). Surjectivity of alpha, or equivalently applying alpha inverse, gives the reverse range inclusion as well, proving membership in the ambient normalizer. For uniqueness, evaluate two coordinate descriptions at (i,1) to recover sigma and b. At one label, equality alpha(x)*b(i) = beta(x)*b(i) and right cancellation recover alpha for every x. This last step uses Nonempty K.

Trivial H and infinite K or H are included: no nontriviality, Fintype, cardinality or commutativity assumption is used. Nonempty K is essential for this uniform uniqueness assertion; if K is empty, distinct automorphisms of H can describe the same empty permutation. This theorem classifies normalization of the diagonal regular action. Preservation of the label partition alone does not impose its common-automorphism condition, and is a different symmetry question.

For finite nonempty K with cardinality r and a finite cyclic group H of order m, normalizerEquiv gives cardinality r! times m^r times phi(m). The permutation factor contributes r!, functions K to H contribute m^r, and IsCyclic.card_mulAut gives phi(m) automorphisms. The single common alpha supplies one totient factor, not a separate automorphism choice for each label. This count uses the type equivalence and does not require a group law on parameter triples.

For n > 0 and a a natural number, put t = (finRotate n)^a, H = Subgroup.zpowers t, r = gcd(n,a) and m = n/r. The subgroup H acts freely on Fin n: an element fixing one point commutes with the transitive full rotation and therefore fixes all points. For Omega the H-orbit quotient, the existing Mathlib selfEquivOrbitsQuotientProd chart has inverse (omega,h) mapping to h acting on omega.out; its verified equivariance transports the actual subgroup H, by ambient permutation congruence, onto the diagonal range on Omega times H. Normalizer transport therefore applies to the actual chosen subgroup. Here |H| = m and n = |Omega|m = rm with m > 0, so |Omega| = r. Thus the exact normalizer cardinality is r! times m^r times phi(m). This includes a = 0, n = 1 and m = 1; for n = 6 and a = 2 the normalizer has 36 elements while the complete orbit-relation automorphism group has 72. The latter comparison is a mathematical consequence, not a new library theorem.

## References

- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.Parameters`
- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.coordinatePerm`
- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.diagonal`
- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.diagonalHom`
- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.diagonalNormalizer`
- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.mem_normalizer_iff_existsUnique_coordinates`
- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.normalizerEquiv`
- Truth anchor: `D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer.normalizerEquiv_eval`
