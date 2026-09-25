# Latin Squares and Column Ascents

## Abstract

Latin squares carry a column-ascent statistic whose interior multiples are the target values.

**Definition 1.1 (Latin square).**

$$\forall n \in \mathrm{Nat},\; \forall L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \operatorname{IsLatin}\left(n, L\right) \Leftrightarrow \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Bijective}\left(\operatorname{row}\left(L, i\right)\right)\right) \land \left(\forall c \in \operatorname{Fin}\left(n\right),\; \operatorname{Bijective}\left(\operatorname{column}\left(L, c\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianDefs.IsLatin` (`✓ std3`).

*Citation.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

A map on a finite square is Latin when every row and every column is a bijection on the symbols.

**Definition 1.2 (Column ascent count).**

$$\forall n \in \mathrm{Nat},\; \forall L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \forall c \in \operatorname{Fin}\left(n\right),\; \operatorname{colAscents}\left(n, L, c\right) = \operatorname{card}\left(\{j \in \mathrm{Nat}| j + 1 < n \land \operatorname{L}\left(j, c\right) < \operatorname{L}\left(j + 1, c\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianDefs.colAscents` (`✓ std3`).

*Citation.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For a fixed column, count the adjacent row positions whose entries increase.

**Definition 1.3 (Total column ascents).**

$$\forall n \in \mathrm{Nat},\; \forall L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \operatorname{totalAscents}\left(n, L\right) = \sum c \in \operatorname{Fin}\left(n\right) \operatorname{colAscents}\left(n, L, c\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianDefs.totalAscents` (`✓ std3`).

*Citation.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The total ascent number is the sum of the column ascent counts over all columns.

**Definition 1.4 (Interior multiples).**

$$claim \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; 5 \le n \Rightarrow \left(\forall k \in \mathrm{Nat},\; \left(2 \le k \land k \le n - 3\right) \Rightarrow \left(\exists L \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)\right),\; \operatorname{IsLatin}\left(n, L\right) \land \operatorname{totalAscents}\left(n, L\right) = k \cdot n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianDefs.claim` (`✓ std3`).

*Citation.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For every order at least five and every integer k from two through n minus three, an order-n Latin square has total ascent number k n.

## References

- Truth anchor: `D5/S3/Combinatorics/LatinEulerianDefs.IsLatin`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianDefs.colAscents`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianDefs.totalAscents`
