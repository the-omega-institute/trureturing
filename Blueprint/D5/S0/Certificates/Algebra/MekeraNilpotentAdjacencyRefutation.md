# Distinct nonzero nilpotents can be nonadjacent

## Abstract

Two opposite matrix units refute nilpotent adjacency in the annihilator digraph.

**Definition 1.1 (Vertices of the annihilator digraph).**

$$\operatorname{vertex}\left(x\right) \iff x \ne 0 \land (\exists t: R, t \ne 0 \land (x \cdot t = 0 \lor t \cdot x = 0))$$

*Formalization.* `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.vertex` (`✓ std3`).

*Citation.* Rasie Mekera, Defne Somer, and Didem Yeşil (2026). *Annihilator Digraphs and Extended Zero-Divisor Digraphs of Semigroups and Rings*. DOI: [10.48550/arXiv.2608.09243](https://doi.org/10.48550/arXiv.2608.09243). URL: <https://arxiv.org/html/2608.09243v2#S7.p2.1>.

*Commentary.*

A vertex is a nonzero element with a nonzero annihilator on at least one side.

**Definition 1.2 (The ordered arc relation).**

$$\operatorname{arc}\left(x, y\right) \iff \operatorname{vertex}\left(x\right) \land \operatorname{vertex}\left(y\right) \land x \ne y \land ((\exists t: R, t \cdot (x \cdot y) = 0 \land t \cdot x \ne 0 \land t \cdot y \ne 0) \lor (\exists t: R, (x \cdot y) \cdot t = 0 \land x \cdot t \ne 0 \land y \cdot t \ne 0))$$

*Formalization.* `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.arc` (`✓ std3`).

*Citation.* Rasie Mekera, Defne Somer, and Didem Yeşil (2026). *Annihilator Digraphs and Extended Zero-Divisor Digraphs of Semigroups and Rings*. DOI: [10.48550/arXiv.2608.09243](https://doi.org/10.48550/arXiv.2608.09243). URL: <https://arxiv.org/html/2608.09243v2#S7.p2.1>.

*Commentary.*

Definition 4.1 requires distinct vertices. Each witness is in the ambient ring. The left branch excludes both left endpoint annihilators, and the right branch excludes both right endpoint annihilators. Reversing the arc reverses the product.

**Definition 1.3 (Positive-power nilpotence).**

$$\operatorname{nilpotent}\left(x\right) \iff \exists k: \mathbb{N}, x^{k + 1} = 0$$

*Formalization.* `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.nilpotent` (`✓ std3`).

*Citation.* Rasie Mekera, Defne Somer, and Didem Yeşil (2026). *Annihilator Digraphs and Extended Zero-Divisor Digraphs of Semigroups and Rings*. DOI: [10.48550/arXiv.2608.09243](https://doi.org/10.48550/arXiv.2608.09243). URL: <https://arxiv.org/html/2608.09243v2#S7.p2.1>.

*Commentary.*

The exponent k + 1 is positive, so the power uses multiplication alone. For a nonzero nilpotent, the last nonzero power gives a nonzero annihilator.

**Definition 1.4 (The Section 7 adjacency assertion).**

$$\operatorname{claim} \iff \forall (R: \operatorname{Type}_{0}) [\operatorname{NonUnitalRing}\left(R\right)], \neg (\forall r, s: R, r \cdot s = s \cdot r) \to \forall x, y: R, x \ne y \to x \ne 0 \to y \ne 0 \to \operatorname{nilpotent}\left(x\right) \to \operatorname{nilpotent}\left(y\right) \to (\operatorname{arc}\left(x, y\right) \lor \operatorname{arc}\left(y, x\right))$$

*Formalization.* `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.claim` (`✓ std3`).

*Citation.* Rasie Mekera, Defne Somer, and Didem Yeşil (2026). *Annihilator Digraphs and Extended Zero-Divisor Digraphs of Semigroups and Rings*. DOI: [10.48550/arXiv.2608.09243](https://doi.org/10.48550/arXiv.2608.09243). URL: <https://arxiv.org/html/2608.09243v2#S7.p2.1>.

*Commentary.*

The assertion quantifies over associative rings in carrier universe zero whose multiplication is noncommutative. A multiplicative identity is optional. Either arc suffices for adjacency. The two nilpotence exponents can differ.

**Theorem 1.5 (The universal assertion is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mekera-somer-yesil-nilpotent-adjacency` (refuted) by `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mekera-somer-yesil-nilpotent-adjacency","declaration_gid":"D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rasie Mekera, Defne Somer, and Didem Yeşil (2026). *Annihilator Digraphs and Extended Zero-Divisor Digraphs of Semigroups and Rings*. DOI: [10.48550/arXiv.2608.09243](https://doi.org/10.48550/arXiv.2608.09243). URL: <https://arxiv.org/html/2608.09243v2#S7.p2.1>.

*Commentary.*

In the two-by-two matrix ring over the binary field, take the opposite off-diagonal matrix units A and B. They are distinct and nonzero and both square to zero, so each is a vertex. Their products AB and BA are different diagonal units, which exhibits noncommutativity.

Matrix-unit multiplication gives (AB)A = A and B(AB) = B. By associativity, a left annihilator of AB annihilates A on the left, and a right annihilator of AB annihilates B on the right. Thus neither can witness an arc from A to B.

The identities (BA)B = B and A(BA) = A give the corresponding contradictions for an arc from B to A. Lifting the coefficient type gives the same refutation at each carrier universe.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.arc`
- Truth anchor: `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.nilpotent`
- Truth anchor: `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.result`
- Truth anchor: `D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.vertex`
- Dependency: [D5/S0/Certificates/Algebra/BergmanQuestion15Refutation](BergmanQuestion15Refutation.md)
