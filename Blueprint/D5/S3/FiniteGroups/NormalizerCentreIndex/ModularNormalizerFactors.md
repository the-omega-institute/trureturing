# Coprime products and modular groups

## Abstract

Normalizer subgroups and their conjugacy classes multiply over coprime factors.

**Definition 1.1 (Distinct normalizer subgroups).**

$$\forall G \in Type,\; [Group\left(G\right)] NormalizerWitness\left(G\right) = \{N: Subgroup\left(G\right) \mid\exists H \in Subgroup\left(G\right),\; N = \operatorname{Subgroup}.\operatorname{normalizer}\left((H: Set\left(G\right))\right)\}$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.NormalizerWitness` (`✓ std3`).

*Citation.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The source writes: “If we denote respectively by s(G) and ω(G) the number of normalizers and the number of conjugacy classes of normalizers of a group G, then our problem is: for which groups G do we have s(G) = ω(G)? To be more precise, we want to focus our study in a slightly different way: for which values of ω(G) the equality s(G) = ω(G) holds true independently of the choice of the group G in a suitable class?” Printed page 1169. The subtype contains each normalizer once, regardless of the number of subgroups producing it.

**Definition 1.2 (Inner conjugacy of subgroups).**

$$\forall G \in Type,\; [Group\left(G\right)] \forall A \in Subgroup\left(G\right),\; \forall B \in Subgroup\left(G\right),\; ConjEquivalent\left(A, B\right) = \left(\exists g \in G,\; \forall x \in G,\; x\in A \iff g \cdot x \cdot g^{-1}\in B\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.ConjEquivalent` (`✓ std3`).

*Citation.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The source writes: “If we denote respectively by s(G) and ω(G) the number of normalizers and the number of conjugacy classes of normalizers of a group G, then our problem is: for which groups G do we have s(G) = ω(G)? To be more precise, we want to focus our study in a slightly different way: for which values of ω(G) the equality s(G) = ω(G) holds true independently of the choice of the group G in a suitable class?” Printed page 1169. Two subgroups are related when conjugation by one group element identifies their membership predicates. This relation includes all elements of both subgroups.

**Definition 1.3 (The equivalence relation on normalizers).**

$$\forall G \in Type,\; [Group\left(G\right)] \forall h \in Equivalence\left((fun (A B: NormalizerWitness\left(G\right)) \mapsto ConjEquivalent\left(val\left(A\right), val\left(B\right)\right))\right),\; normalizerSetoid\left(G\right) = \operatorname{Setoid}.\operatorname{mk}\left((fun (A B: NormalizerWitness\left(G\right)) \mapsto ConjEquivalent\left(val\left(A\right), val\left(B\right)\right)), h\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.normalizerSetoid` (`✓ std3`).

*Citation.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The source writes: “If we denote respectively by s(G) and ω(G) the number of normalizers and the number of conjugacy classes of normalizers of a group G, then our problem is: for which groups G do we have s(G) = ω(G)? To be more precise, we want to focus our study in a slightly different way: for which values of ω(G) the equality s(G) = ω(G) holds true independently of the choice of the group G in a suitable class?” Printed page 1169. The relation is ConjEquivalent on the underlying subgroups. Identity, inversion and multiplication of conjugating elements prove reflexivity, symmetry and transitivity.

**Definition 1.4 (Conjugacy classes of normalizers).**

$$\forall G \in Type,\; [Group\left(G\right)] NormalizerClass\left(G\right) = Quotient\left(normalizerSetoid\left(G\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.NormalizerClass` (`✓ std3`).

*Citation.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The source writes: “If we denote respectively by s(G) and ω(G) the number of normalizers and the number of conjugacy classes of normalizers of a group G, then our problem is: for which groups G do we have s(G) = ω(G)? To be more precise, we want to focus our study in a slightly different way: for which values of ω(G) the equality s(G) = ω(G) holds true independently of the choice of the group G in a suitable class?” Printed page 1169. The quotient identifies normalizer subgroups under inner conjugacy.

**Definition 1.5 (The number of normalizers).**

$$\forall G \in Type,\; [Group\left(G\right)] sCard\left(G\right) = \operatorname{Cardinal}.\operatorname{mk}\left(NormalizerWitness\left(G\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.sCard` (`✓ std3`).

*Citation.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The source writes: “If we denote respectively by s(G) and ω(G) the number of normalizers and the number of conjugacy classes of normalizers of a group G, then our problem is: for which groups G do we have s(G) = ω(G)? To be more precise, we want to focus our study in a slightly different way: for which values of ω(G) the equality s(G) = ω(G) holds true independently of the choice of the group G in a suitable class?” Printed page 1169. The cardinal-valued count includes infinite sets of distinct normalizers.

**Definition 1.6 (The finite normalizer-class count).**

$$\forall G \in Type,\; [Group\left(G\right)] omega\left(G\right) = \operatorname{Nat}.\operatorname{card}\left(NormalizerClass\left(G\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.omega` (`✓ std3`).

*Citation.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The source writes: “If we denote respectively by s(G) and ω(G) the number of normalizers and the number of conjugacy classes of normalizers of a group G, then our problem is: for which groups G do we have s(G) = ω(G)? To be more precise, we want to focus our study in a slightly different way: for which values of ω(G) the equality s(G) = ω(G) holds true independently of the choice of the group G in a suitable class?” Printed page 1169. The natural-valued count is used only when NormalizerClass is finite.

**Definition 1.7 (Index of the centre).**

$$\forall G \in Type,\; [Group\left(G\right)] centreIndex\left(G\right) = \operatorname{Cardinal}.\operatorname{mk}\left(G / \operatorname{Subgroup}.\operatorname{center}\left(G\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.centreIndex` (`✓ std3`).

*Citation.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

Question 3.3. Let G be a group satisfying the normalizer condition, and suppose that ω(G) is finite. If s(G) > ω(G), is |G : Z(G)| ω(G)-bounded? Is this true at least for finite p-groups? Printed page 1174. This is the cardinality of the quotient by the centre, including an infinite index.

**Theorem 1.8 (Counts multiply over coprime products).**

$$\forall G \in Type,\; [Group\left(G\right)] \forall K \in Type,\; [Group\left(K\right)] [Finite\left(G\right)] [Finite\left(K\right)] (\operatorname{Nat}.\operatorname{Coprime}\left(\operatorname{Nat}.\operatorname{card}\left(G\right), \operatorname{Nat}.\operatorname{card}\left(K\right)\right)) \Rightarrow ((sCard\left(G \times K\right) = sCard\left(G\right) \cdot sCard\left(K\right)) \land (omega\left(G \times K\right) = omega\left(G\right) \cdot omega\left(K\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.counts_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The existing subgroup-product equivalence splits every subgroup when the finite factor orders are coprime. The normalizer of a product is the product of normalizers; conjugacy also splits. The resulting bijections give both cardinality identities.

**Theorem 1.9 (Finiteness of the product quotient).**

$$\forall G \in Type,\; [Group\left(G\right)] \forall K \in Type,\; [Group\left(K\right)] [Finite\left(G\right)] [Finite\left(K\right)] (\operatorname{Nat}.\operatorname{Coprime}\left(\operatorname{Nat}.\operatorname{card}\left(G\right), \operatorname{Nat}.\operatorname{card}\left(K\right)\right)) \Rightarrow ([Finite\left(NormalizerClass\left(G\right)\right)] [Finite\left(NormalizerClass\left(K\right)\right)] Finite\left(NormalizerClass\left(G \times K\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finite_product_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The product-class equivalence transports finiteness from the two factor quotients.

**Definition 1.10 (The central additive embedding).**

$$\forall p \in \mathbb{N},\; \forall h \in \operatorname{AddMonoidHom}.\operatorname{comp}\left(\operatorname{AddMonoidHom}.\operatorname{mulLeft}\left((p: ZMod\left(p^{2}\right))\right), \operatorname{Int}.\operatorname{castAddHom}\left(ZMod\left(p^{2}\right)\right)\right)\left((p: \mathbb{Z})\right) = 0,\; \operatorname{Modular}.\operatorname{t}\left(p\right) = \operatorname{ZMod}.\operatorname{lift}\left(p, \langle\operatorname{AddMonoidHom}.\operatorname{comp}\left(\operatorname{AddMonoidHom}.\operatorname{mulLeft}\left((p: ZMod\left(p^{2}\right))\right), \operatorname{Int}.\operatorname{castAddHom}\left(ZMod\left(p^{2}\right)\right)\right), h\rangle\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.t` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

Multiplication by p descends from integer residues modulo p to residues modulo p²; p times p is zero in the target.

**Definition 1.11 (The modular automorphism).**

$$\forall p \in \mathbb{N},\; \forall a \in ZMod\left(p\right),\; \forall h \in (1+\operatorname{Modular}.\operatorname{t}\left(p, a\right)) \cdot (1-\operatorname{Modular}.\operatorname{t}\left(p, a\right)) = 1,\; \forall k \in (1-\operatorname{Modular}.\operatorname{t}\left(p, a\right)) \cdot (1+\operatorname{Modular}.\operatorname{t}\left(p, a\right)) = 1,\; \operatorname{Modular}.\operatorname{aut}\left(p, a\right) = \operatorname{AddEquiv}.\operatorname{toMultiplicative}\left(\operatorname{Multiplicative}.\operatorname{toAdd}\left(\operatorname{AddAut}.\operatorname{mulLeft}\left((\langle(1+\operatorname{Modular}.\operatorname{t}\left(p, a\right)), (1-\operatorname{Modular}.\operatorname{t}\left(p, a\right)), h, k\rangle: ZMod\left(p^{2}\right)^{*})\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.aut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The forward multiplier is 1 + t p a and the inverse multiplier is 1 − t p a. Their product is one because products of two values of t vanish.

**Definition 1.12 (The action of the second cyclic factor).**

$$\forall p \in \mathbb{N},\; \forall h \in \operatorname{Modular}.\operatorname{aut}\left(p, \operatorname{Multiplicative}.\operatorname{toAdd}\left(1\right)\right) = 1,\; \forall k \in \left(\forall a \in Multiplicative\left(ZMod\left(p\right)\right),\; \forall b \in Multiplicative\left(ZMod\left(p\right)\right),\; \operatorname{Modular}.\operatorname{aut}\left(p, \operatorname{Multiplicative}.\operatorname{toAdd}\left(a \cdot b\right)\right) = \operatorname{Modular}.\operatorname{aut}\left(p, \operatorname{Multiplicative}.\operatorname{toAdd}\left(a\right)\right) \cdot \operatorname{Modular}.\operatorname{aut}\left(p, \operatorname{Multiplicative}.\operatorname{toAdd}\left(b\right)\right)\right),\; \operatorname{Modular}.\operatorname{action}\left(p\right) = \operatorname{MonoidHom}.\operatorname{mk}\left(\operatorname{OneHom}.\operatorname{mk}\left((fun (a: Multiplicative\left(ZMod\left(p\right)\right)) \mapsto \operatorname{Modular}.\operatorname{aut}\left(p, \operatorname{Multiplicative}.\operatorname{toAdd}\left(a\right)\right)), h\right), k\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.action` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

An element of Multiplicative (ZMod p) acts through its additive coordinate and the automorphism aut.

**Definition 1.13 (The modular group).**

$$\forall p \in \mathbb{N},\; \operatorname{Modular}.\operatorname{P}\left(p\right) = SemidirectProduct\left(Multiplicative\left(ZMod\left(p^{2}\right)\right), Multiplicative\left(ZMod\left(p\right)\right), \operatorname{Modular}.\operatorname{action}\left(p\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The semidirect product has underlying coordinates in ZMod (p²) and ZMod p. For prime p its order is p³.

**Theorem 1.14 (Finite modular carrier).**

$$\forall p \in \mathbb{N},\; [NeZero\left(p\right)] Finite\left(\operatorname{Modular}.\operatorname{P}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finiteP` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

Finiteness is transported along SemidirectProduct.equivProd from the product of the two finite residue types.

**Theorem 1.15 (Order of the modular group).**

$$\forall p \in \mathbb{N},\; [NeZero\left(p\right)] \operatorname{Nat}.\operatorname{card}\left(\operatorname{Modular}.\operatorname{P}\left(p\right)\right) = p^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.card_p` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The coordinate bijection gives p² times p elements.

**Theorem 1.16 (Order of the centre).**

$$\forall p \in \mathbb{N},\; [Fact\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] \operatorname{Nat}.\operatorname{card}\left(\operatorname{Subgroup}.\operatorname{center}\left(\operatorname{Modular}.\operatorname{P}\left(p\right)\right)\right) = p$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.center_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

The centre consists of coordinates (t p u, 0), with u in ZMod p. Injectivity of t gives exactly p central elements.

**Theorem 1.17 (Two normalizer subgroups).**

$$\forall p \in \mathbb{N},\; [Fact\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] (p\neq 2) \Rightarrow (sCard\left(\operatorname{Modular}.\operatorname{P}\left(p\right)\right) = 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.s_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

A subgroup containing the central order-p subgroup, or contained in it, has whole-group normalizer. Every remaining subgroup has the elementary abelian subgroup of first coordinate divisible by p as its normalizer. Both normalizers occur.

**Theorem 1.18 (Two normalizer conjugacy classes).**

$$\forall p \in \mathbb{N},\; [Fact\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] (p\neq 2) \Rightarrow (omega\left(\operatorname{Modular}.\operatorname{P}\left(p\right)\right) = 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.omega_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

Both normalizer subgroups are normal, so each is its own conjugacy class.

**Theorem 1.19 (Finite normalizer quotient).**

$$\forall p \in \mathbb{N},\; [Fact\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] (p\neq 2) \Rightarrow (Finite\left(NormalizerClass\left(\operatorname{Modular}.\operatorname{P}\left(p\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finite_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

Finiteness passes from the finite modular group to the subtype of its normalizer subgroups and then to their conjugacy quotient.

## References

- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.ConjEquivalent`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.NormalizerClass`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.NormalizerWitness`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.P`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.action`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.aut`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.card_p`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.center_card`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.centreIndex`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.counts_prod`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finiteP`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finite_classes`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finite_product_classes`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.normalizerSetoid`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.omega`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.omega_card`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.sCard`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.s_card`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.t`
- Dependency: [D5/S3/FiniteGroups/SubgroupConjugacyRatio](../SubgroupConjugacyRatio.md)
