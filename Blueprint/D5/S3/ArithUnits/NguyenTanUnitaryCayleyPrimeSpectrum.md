# Primeness does not imply adjacency nonsingularity

## Abstract

Prime connected and anti-connected unitary Cayley graphs can have zero as an adjacency eigenvalue.

**Definition 1.1 (A nondegenerate functional).**

$$\forall (R: Type), [\operatorname{CommRing}\left(R\right)], (\operatorname{IsFrobenius}\left(R\right)) \Leftrightarrow (\exists (n: \mathbb{N}), ((n: R) = 0) \land (\exists (psi: \operatorname{AddMonoidHom}\left(R, \operatorname{ZMod}\left(n\right)\right)), \forall (I: \operatorname{Ideal}\left(R\right)), (\forall (x: R), (x \in I) \Rightarrow (psi\left(x\right) = 0)) \Rightarrow (I = \perp)))$$

*Formalization.* `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.IsFrobenius` (`✓ std3`).

*Citation.* Tung T. Nguyen, Nguyen Duy Tân (2025). *Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs*. DOI: [10.48550/arXiv.2508.10348](https://doi.org/10.48550/arXiv.2508.10348). URL: <https://arxiv.org/abs/2508.10348v1>.

*Commentary.*

Section 4.1, page 12: "being Frobenius means that R is a Z/n algebra equipped with a non-degenerate Z/n linear functional ψ : R → Z/n. Here, non-degenerate means that the kernel of ψ does not contain any non-zero ideal in R." The integer n annihilates R, and the additive homomorphism psi is automatically Z/n-linear. Every ideal contained in its kernel is the zero ideal.

**Definition 1.2 (The graph on the additive ring).**

$$\forall (R: Type), [\operatorname{CommRing}\left(R\right)], \forall (U: \operatorname{Subgroup}\left(\operatorname{Units}\left(R\right)\right)), \operatorname{unitaryCayley}\left(R, U\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left(fun (a: R) \mapsto fun (b: R) \mapsto \exists (u: \operatorname{Units}\left(R\right)), (u \in U) \land (a - b = \operatorname{Units}.\operatorname{val}\left(u\right))\right)$$

*Formalization.* `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.unitaryCayley` (`✓ std3`).

*Citation.* Tung T. Nguyen, Nguyen Duy Tân (2025). *Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs*. DOI: [10.48550/arXiv.2508.10348](https://doi.org/10.48550/arXiv.2508.10348). URL: <https://arxiv.org/abs/2508.10348v1>.

*Commentary.*

Section 3.1, page 7: "Let R be a finite commutative ring and S be a symmetric subset of R"; "we fix a subgroup U of R× such that −1 ∈ U (this will ensure that all relevant generating sets are symmetric)." SimpleGraph.fromRel makes the relation symmetric and removes loops. Under minus-one membership, two vertices a and b are adjacent exactly when a − b is the value of a unit in U. Units.val is the coercion to R.

**Definition 1.3 (Homogeneous vertex sets).**

$$\forall (V: Type), \forall (G: \operatorname{SimpleGraph}\left(V\right)), \forall (X: \operatorname{Set}\left(V\right)), (\operatorname{IsHomogeneousSet}\left(G, X\right)) \Leftrightarrow (\forall (v: V), (\neg (v \in X)) \Rightarrow ((\forall (x: V), (x \in X) \Rightarrow (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, v, x\right))) \lor (\forall (x: V), (x \in X) \Rightarrow (\neg \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, v, x\right)))))$$

*Formalization.* `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.IsHomogeneousSet` (`✓ std3`).

*Citation.* Tung T. Nguyen, Nguyen Duy Tân (2025). *Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs*. DOI: [10.48550/arXiv.2508.10348](https://doi.org/10.48550/arXiv.2508.10348). URL: <https://arxiv.org/abs/2508.10348v1>.

*Commentary.*

Section 3.3, page 10: "A subset X in a graph G is called a homogeneous set if every vertex in V(G) \ X is adjacent to either all or none of the vertices in X." The two alternatives are separate universal statements over X; the outside vertex v may choose either alternative.

**Definition 1.4 (No non-trivial homogeneous set).**

$$\forall (V: Type), [\operatorname{Fintype}\left(V\right)], \forall (G: \operatorname{SimpleGraph}\left(V\right)), (\operatorname{IsPrimeGraph}\left(G\right)) \Leftrightarrow (\forall (X: \operatorname{Finset}\left(V\right)), (\operatorname{IsHomogeneousSet}\left(G, (X: \operatorname{Set}\left(V\right))\right)) \Rightarrow ((\operatorname{Finset}.\operatorname{card}\left(X\right) < 2) \lor (\operatorname{Finset}.\operatorname{card}\left(X\right) = \operatorname{Fintype}.\operatorname{card}\left(V\right))))$$

*Formalization.* `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.IsPrimeGraph` (`✓ std3`).

*Citation.* Tung T. Nguyen, Nguyen Duy Tân (2025). *Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs*. DOI: [10.48550/arXiv.2508.10348](https://doi.org/10.48550/arXiv.2508.10348). URL: <https://arxiv.org/abs/2508.10348v1>.

*Commentary.*

Section 3.3, page 10: "A homogeneous set X with 2 ≤ |X| < |V(G)| is called non-trivial. The graph G is said to be prime if it does not contain any non-trivial homogeneous sets." Finset represents every subset of the finite vertex type. A homogeneous finset has cardinality less than two or equal to Fintype.card V.

**Definition 1.5 (A nonzero vector in the adjacency kernel).**

$$\forall (V: Type), [\operatorname{Fintype}\left(V\right)], \forall (G: \operatorname{SimpleGraph}\left(V\right)), (\operatorname{HasZeroEigenvalue}\left(G\right)) \Leftrightarrow (\exists (v: V \to \mathbb{C}), (\neg (v = 0)) \land (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{SimpleGraph}.\operatorname{adjMatrix}\left(\mathbb{C}, G\right), v\right) = 0))$$

*Formalization.* `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.HasZeroEigenvalue` (`✓ std3`).

*Citation.* Tung T. Nguyen, Nguyen Duy Tân (2025). *Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs*. DOI: [10.48550/arXiv.2508.10348](https://doi.org/10.48550/arXiv.2508.10348). URL: <https://arxiv.org/abs/2508.10348v1>.

*Commentary.*

Zero is an adjacency eigenvalue exactly when the complex adjacency matrix annihilates a nonzero vector.

**Definition 1.6 (Nguyen–Tân Question 4.17).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (R: Type), [\operatorname{CommRing}\left(R\right)], [\operatorname{Fintype}\left(R\right)], (\operatorname{IsFrobenius}\left(R\right)) \Rightarrow (\forall (U: \operatorname{Subgroup}\left(\operatorname{Units}\left(R\right)\right)), ((-1: \operatorname{Units}\left(R\right)) \in U) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{unitaryCayley}\left(R, U\right)\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Connected}\left((\operatorname{unitaryCayley}\left(R, U\right))^{c}\right)) \Rightarrow ((\operatorname{IsPrimeGraph}\left(\operatorname{unitaryCayley}\left(R, U\right)\right)) \Leftrightarrow (\neg (\operatorname{HasZeroEigenvalue}\left(\operatorname{unitaryCayley}\left(R, U\right)\right))))))))$$

*Formalization.* `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.claim` (`✓ std3`).

*Citation.* Tung T. Nguyen, Nguyen Duy Tân (2025). *Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs*. DOI: [10.48550/arXiv.2508.10348](https://doi.org/10.48550/arXiv.2508.10348). URL: <https://arxiv.org/abs/2508.10348v1>.

*Commentary.*

Question 4.17, page 19 of arXiv:2508.10348v1: "Suppose that Γ(R, U) is both connected and anti-connected. Is it true that Γ(R, U) is prime if and only if 0 is not an eigenvalue?" The affirmative proposition ranges over finite commutative Frobenius rings and subgroups of their units containing minus one. Anti-connected means that the complement is connected. Zero is an eigenvalue exactly when the complex adjacency matrix annihilates a nonzero vector; the HasZeroEigenvalue definition node displays this condition in full.

**Theorem 1.7 (The affirmative proposition is false).**

$$\neg (\forall (R: Type), [\operatorname{CommRing}\left(R\right)], [\operatorname{Fintype}\left(R\right)], (\operatorname{IsFrobenius}\left(R\right)) \Rightarrow (\forall (U: \operatorname{Subgroup}\left(\operatorname{Units}\left(R\right)\right)), ((-1: \operatorname{Units}\left(R\right)) \in U) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{unitaryCayley}\left(R, U\right)\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Connected}\left((\operatorname{unitaryCayley}\left(R, U\right))^{c}\right)) \Rightarrow ((\operatorname{IsPrimeGraph}\left(\operatorname{unitaryCayley}\left(R, U\right)\right)) \Leftrightarrow (\neg (\operatorname{HasZeroEigenvalue}\left(\operatorname{unitaryCayley}\left(R, U\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tung T. Nguyen, Nguyen Duy Tân (2025). *Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs*. DOI: [10.48550/arXiv.2508.10348](https://doi.org/10.48550/arXiv.2508.10348). URL: <https://arxiv.org/abs/2508.10348v1>.

*Commentary.*

For every finite commutative group G of even cardinality at least three, the group algebra MonoidAlgebra (ZMod 2) G is Frobenius: its coefficient at the identity detects every nonzero ideal after multiplication by a suitable inverse basis element. The subgroup of basis units contains minus one. Coefficient vectors identify its Cayley graph with the binary Hamming graph. Coordinate changes connect the graph, and two changes through the complement connect each pair that differs in one coordinate. A proper homogeneous set in a connected triangle-free graph is independent, and two of its vertices would have identical neighbourhoods. Three available coordinates exclude such twins. A product of coordinate signs has eigenvalue card G − 2 card s; selecting half the coordinates gives a nonzero vector with eigenvalue zero. The cyclic group Multiplicative (ZMod d) therefore gives the family for every even d at least four. The settling contradiction uses d = 4. A polynomial-quotient isomorphism, a complete eigenbasis and the general multiplicity of zero are separate questions.

## References

- Truth anchor: `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.HasZeroEigenvalue`
- Truth anchor: `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.IsFrobenius`
- Truth anchor: `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.IsHomogeneousSet`
- Truth anchor: `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.IsPrimeGraph`
- Truth anchor: `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.claim`
- Truth anchor: `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.result`
- Truth anchor: `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.unitaryCayley`
- Dependency: [D5/S3/Combinatorics/Hamming/HammingMultipartitePartition](../Combinatorics/Hamming/HammingMultipartitePartition.md)
- Dependency: [D5/S3/Combinatorics/Hamming/InducedSubcubes](../Combinatorics/Hamming/InducedSubcubes.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../VertexAlgebra/LatticeTwistedGroundRealization.md)
