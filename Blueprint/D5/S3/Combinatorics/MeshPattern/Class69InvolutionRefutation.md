# Class 69 Mesh Patterns Are Not Equidistributed on Involutions

## Abstract

The four Class 69 length-2 mesh patterns fail equidistribution on involutions at length three.

**Definition 1.1 (The four Class 69 shaded-cell sets).**

$$\forall a \in \operatorname{Fin}\left(4\right),\; \operatorname{R}\left(a\right) = \operatorname{ite}\left(\operatorname{val}\left(a\right) = 0, \{(1, 2), (1, 1), (2, 1), (0, 0)\}, \operatorname{ite}\left(\operatorname{val}\left(a\right) = 1, \{(2, 2), (0, 1), (1, 1), (1, 0)\}, \operatorname{ite}\left(\operatorname{val}\left(a\right) = 2, \{(0, 2), (1, 1), (2, 1), (1, 0)\}, \{(1, 2), (0, 1), (1, 1), (2, 0)\}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.R` (`✓ std3`).

*Citation.* Q. Fang, S. Fu, S. Kitaev, H. Li, X. Su, Z. Sun (2026). *On mesh patterns of short length: Equidistribution and enumeration*. DOI: [10.48550/arXiv.2606.14367](https://doi.org/10.48550/arXiv.2606.14367). URL: <https://arxiv.org/abs/2606.14367v1>.

*Commentary.*

The function R : Fin 4 → Finset (Nat × Nat) assigns the four shaded-cell sets in the source order. The source macro \pattern{scale=0.5}{2}{1/1,2/2}{x/y,...} shades the unit box with lower-left corner (x,y) for each listed x/y; its dots are at (1,1) and (2,2).

**Definition 1.2 (The relative box).**

$$\forall n \in \mathbb{N},\; \forall s \in Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \forall r \in \operatorname{Fin}\left(n\right),\; \operatorname{box}\left(s, i, j, r\right) = (\operatorname{ite}\left(i < r, 1, 0\right) + \operatorname{ite}\left(j < r, 1, 0\right), \operatorname{ite}\left(s\left(i\right) < s\left(r\right), 1, 0\right) + \operatorname{ite}\left(s\left(j\right) < s\left(r\right), 1, 0\right))$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.box` (`✓ std3`).

*Citation.* Q. Fang, S. Fu, S. Kitaev, H. Li, X. Su, Z. Sun (2026). *On mesh patterns of short length: Equidistribution and enumeration*. DOI: [10.48550/arXiv.2606.14367](https://doi.org/10.48550/arXiv.2606.14367). URL: <https://arxiv.org/abs/2606.14367v1>.

*Commentary.*

For two selected positions i and j and a third position r, box records the number of selected positions below r and the number of their values below the value at r.

**Definition 1.3 (A length-2 mesh occurrence).**

$$\forall n \in \mathbb{N},\; \forall R \in \operatorname{Finset}\left((\mathbb{N}) \times (\mathbb{N})\right),\; \forall s \in Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (\operatorname{IsOccurrence}\left(R, s, i, j\right)) \Leftrightarrow (i < j \land \left(s\left(i\right) < s\left(j\right) \land \left(\forall r \in \operatorname{Fin}\left(n\right),\; r \ne i \Rightarrow \left(r \ne j \Rightarrow \left(\neg \operatorname{mem}\left(\operatorname{box}\left(s, i, j, r\right), R\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.IsOccurrence` (`✓ std3`).

*Citation.* Q. Fang, S. Fu, S. Kitaev, H. Li, X. Su, Z. Sun (2026). *On mesh patterns of short length: Equidistribution and enumeration*. DOI: [10.48550/arXiv.2606.14367](https://doi.org/10.48550/arXiv.2606.14367). URL: <https://arxiv.org/abs/2606.14367v1>.

*Commentary.*

A pair is an occurrence when its positions and values are increasing and every other position has its relative box outside the selected shaded set.

**Definition 1.4 (The occurrence count).**

$$\forall n \in \mathbb{N},\; \forall R \in \operatorname{Finset}\left((\mathbb{N}) \times (\mathbb{N})\right),\; \forall s \in Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{occ}\left(R, s\right) = Finset.card\left(Finset.filter\left((p \mapsto \operatorname{IsOccurrence}\left(R, s, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right)), Finset.univ\left(\operatorname{Fin}\left(n\right)\right) \times Finset.univ\left(\operatorname{Fin}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.occ` (`✓ std3`).

*Citation.* Q. Fang, S. Fu, S. Kitaev, H. Li, X. Su, Z. Sun (2026). *On mesh patterns of short length: Equidistribution and enumeration*. DOI: [10.48550/arXiv.2606.14367](https://doi.org/10.48550/arXiv.2606.14367). URL: <https://arxiv.org/abs/2606.14367v1>.

*Commentary.*

The occurrence count is the cardinality of the filtered Cartesian product of all pairs of positions.

**Definition 1.5 (Conjecture 1).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; Finset.card\left(Finset.filter\left((s \mapsto s \cdot s = 1 \land \operatorname{occ}\left(\operatorname{R}\left(a\right), s\right) = k), Finset.univ\left(Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\right) = Finset.card\left(Finset.filter\left((s \mapsto s \cdot s = 1 \land \operatorname{occ}\left(\operatorname{R}\left(b\right), s\right) = k), Finset.univ\left(Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.claim` (`✓ std3`).

*Citation.* Q. Fang, S. Fu, S. Kitaev, H. Li, X. Su, Z. Sun (2026). *On mesh patterns of short length: Equidistribution and enumeration*. DOI: [10.48550/arXiv.2606.14367](https://doi.org/10.48550/arXiv.2606.14367). URL: <https://arxiv.org/abs/2606.14367v1>.

*Commentary.*

Fang, Fu, Kitaev, Li, Su and Sun write: "The patterns in the set {\pattern{scale=0.5}{2}{1/1,2/2}{1/2,1/1,2/1,0/0},\pattern{scale=0.5}{2}{1/1,2/2}{2/2,0/1,1/1,1/0},\pattern{scale=0.5}{2}{1/1,2/2}{0/2,1/1,2/1,1/0},\pattern{scale=0.5}{2}{1/1,2/2}{1/2,0/1,1/1,2/0}} are equidistributed on involutions. (The first two patterns, as well as the last two patterns, are trivially equidistributed via the composition of reverse and complement.)" (Conjecture 1, arXiv:2606.14367v1, Concluding remarks). The displayed formula encodes involutions as σ * σ = 1 and counts exactly k occurrences for every n and every pair of pattern indices.

**Theorem 1.6 (The conjecture is refuted).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/fang-fu-kitaev-li-su-sun-2026-class69-involutions` (refuted) by `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fang-fu-kitaev-li-su-sun-2026-class69-involutions","declaration_gid":"D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Q. Fang, S. Fu, S. Kitaev, H. Li, X. Su, Z. Sun (2026). *On mesh patterns of short length: Equidistribution and enumeration*. DOI: [10.48550/arXiv.2606.14367](https://doi.org/10.48550/arXiv.2606.14367). URL: <https://arxiv.org/abs/2606.14367v1>.

*Commentary.*

At n = 3 and k = 0, the involutions 132 and 321 avoid R 0 while only 321 avoids R 2. The two filtered cardinalities are therefore 2 and 1, contradicting equidistribution.

## References

- Truth anchor: `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.IsOccurrence`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.R`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.box`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.occ`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.result`
