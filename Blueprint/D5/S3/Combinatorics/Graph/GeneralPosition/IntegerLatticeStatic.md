# Sharp coordinate general position in integer lattices

## Abstract

Coordinate general position in dimension n+1 has sharp cardinality 2 raised to 2 raised to n.

Vertices are integer-valued functions on Fin k. Coordinate betweenness uses weak inequalities, so equal coordinates are included. The declarations are in the Lean namespace IntegerLatticeStatic. These statements concern finite static sets. Section 5 of Moving through Cartesian products, coronas and joins in general position cites Theorem 1 of Klavzar and Rus, The general position number of integer lattices, DOI 10.1016/j.amc.2020.125664, for the underlying static extremum.

**Definition 1.1 (Weak coordinate betweenness).**

$$\forall (k : \mathrm{Nat}), \forall (x : \operatorname{Fin}\left(k\right) \Rightarrow \mathrm{Int}), \forall (y : \operatorname{Fin}\left(k\right) \Rightarrow \mathrm{Int}), \forall (z : \operatorname{Fin}\left(k\right) \Rightarrow \mathrm{Int}), \operatorname{Between}\left(x, y, z\right) \Leftrightarrow \forall (j : \operatorname{Fin}\left(k\right)), \left(\operatorname{x}\left(j\right) \le \operatorname{y}\left(j\right) \land \operatorname{y}\left(j\right) \le \operatorname{z}\left(j\right)\right) \lor \left(\operatorname{z}\left(j\right) \le \operatorname{y}\left(j\right) \land \operatorname{y}\left(j\right) \le \operatorname{x}\left(j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.Between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

The middle point may be increasing in one coordinate and decreasing in another. Endpoints may agree in any coordinate.

**Definition 1.2 (Coordinate general position).**

$$\forall (k : \mathrm{Nat}), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right) \Rightarrow \mathrm{Int}\right)), \operatorname{CoordinateGP}\left(S\right) \Leftrightarrow \forall x \in S, \forall y \in S, \forall z \in S, x \ne y \Rightarrow \left(y \ne z \Rightarrow \left(x \ne z \Rightarrow \neg (\operatorname{Between}\left(x, y, z\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.CoordinateGP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Every ordered triple of pairwise distinct members is excluded from coordinate betweenness. The condition does not assume that coordinate projections are injective.

**Theorem 1.3 (The static upper bound).**

$$\forall (n : \mathrm{Nat}), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right) \Rightarrow \mathrm{Int}\right)), \operatorname{CoordinateGP}\left(S\right) \Rightarrow \operatorname{card}\left(S\right) \le 2^{2^{n}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.card_le` (`✓ std3`). ∎

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 5, second bullet, cites the static value in dimension k. Here k=n+1. Each of the 2 raised to n sign patterns orients the last n coordinates, while the first coordinate increases. A point is labelled by the orientations in which it has a distinct predecessor. Equal labels on two distinct points would give a three-point chain in one orientation, contradicting general position. Thus the labels inject the set into the subsets of the sign-pattern set.

**Theorem 1.4 (A bounded attaining set with injective coordinates).**

$$\forall (n : \mathrm{Nat}), \exists (S : \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right) \Rightarrow \mathrm{Int}\right)), \operatorname{CoordinateGP}\left(S\right) \land \left(\operatorname{card}\left(S\right) = 2^{2^{n}} \land \left(\operatorname{Nonempty}\left(S\right) \land \left(\forall x \in S, \forall (j : \operatorname{Fin}\left(n + 1\right)), 0 \le \operatorname{x}\left(j\right) \land \operatorname{x}\left(j\right) < 2^{2^{n}} \land \forall (j : \operatorname{Fin}\left(n + 1\right)), \forall x \in S, \forall y \in S, \operatorname{x}\left(j\right) = \operatorname{y}\left(j\right) \Rightarrow x = y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.exists_attaining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Start with the two points zero and one in dimension one. From an array A with N points, use pairs (p,r) as indices. The old coordinates become N times A(p,j) plus A(r,j); the additional first coordinate is N times A(p,0) plus N minus one minus A(r,0). All coordinates lie between zero and N squared minus one and remain injective. Three distinct blocks reduce to the preceding general-position property. One block reduces to the second indices. For exactly two equal blocks, the ordinary and reversed first coordinates force the two second indices to agree. Cardinality squares at every step, giving the stated power. No motion sequence is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.Between`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.CoordinateGP`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.card_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic.exists_attaining`
