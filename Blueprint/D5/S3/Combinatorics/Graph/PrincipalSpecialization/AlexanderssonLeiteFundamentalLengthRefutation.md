# A four-vertex counterexample to Question 6.7

## Abstract

The natural unit interval path on four vertices refutes real-rootedness of the weighted fundamental-length image.

**Definition 1.1 (The universal real-rootedness claim).**

$$\operatorname{claim} \Leftrightarrow (\forall (n: \mathbb{N}), (0 < n) \Rightarrow \forall (h: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)), (\operatorname{Monotone}\left(h\right)) \Rightarrow (\forall (i: \operatorname{Fin}\left(n\right)), i \le h\left(i\right)) \Rightarrow \forall (q: \mathbb{R}), (0 \le q) \Rightarrow \left(\operatorname{Splits}_{\mathbb{R}}\right)\left(\left(\operatorname{Psi}_{t}\right)\left(\left(X_{H_{h}}\right)\left(X, q\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.claim` (`✓ std3`).

*Citation.* Per Alexandersson and Leonardo Saud Maia Leite (2026). *Sink polynomials of line graphs and weighted matching polynomials*. DOI: [10.48550/arXiv.2610.41502](https://doi.org/10.48550/arXiv.2610.41502). URL: <https://arxiv.org/html/2610.41502v1#S6.Thmtheorem7>.

*Commentary.*

The source uses vertex labels 1 through n. Lean uses Fin n and adds one to each label in the correspondence. An ordered edge satisfies i < j and j ≤ h(i). The graph has the undirected closure of these edges. A proper coloring uses positive integer colors, and its weight is q to the number of ordered edges whose colors strictly increase.

The coefficient at a monomial sums the weights of all proper colorings with exactly its actual color multiplicities. Ranking its used colors preserves the multiplicities in increasing color order, properness, and the ascent count. The strict positions of the sorted color word give the proper partial sums of these multiplicities.

In degree n the fundamental element F indexed by S has coefficient one at each cut set T containing S. The map Ψ sends F to t to the power |S| + 1. The corresponding weight of cut set T is t to the power |T| + 1 times (1 − t) to the power n − |T| − 1. Summing over the optional cuts gives the prescribed value, and descending through the supersets of S gives uniqueness. The symbol X in the formula is the source alphabet, and t is the polynomial indeterminate. In degree zero Ψ sends 1 to 1.

**Theorem 1.2 (The weighted image can have nonreal roots).**

$$\neg(\forall (n: \mathbb{N}), (0 < n) \Rightarrow \forall (h: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right)), (\operatorname{Monotone}\left(h\right)) \Rightarrow (\forall (i: \operatorname{Fin}\left(n\right)), i \le h\left(i\right)) \Rightarrow \forall (q: \mathbb{R}), (0 \le q) \Rightarrow \left(\operatorname{Splits}_{\mathbb{R}}\right)\left(\left(\operatorname{Psi}_{t}\right)\left(\left(X_{H_{h}}\right)\left(X, q\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson and Leonardo Saud Maia Leite (2026). *Sink polynomials of line graphs and weighted matching polynomials*. DOI: [10.48550/arXiv.2610.41502](https://doi.org/10.48550/arXiv.2610.41502). URL: <https://arxiv.org/html/2610.41502v1#S6.Thmtheorem7>.

*Commentary.*

Take h = (2, 3, 4, 4) in the source's labels and q = 16. The ordered edges are (1, 2), (2, 3), and (3, 4). Grouping colorings by the number r of colors they use gives a packed coloring sum for each r, multiplied by the factor t to the power r times (1 − t) to the power 4 − r.

The weighted sums for two, three, and four colors are 272, 2448, and 7089. Their contribution is t²(272 + 1904t + 4913t²). Removing the two linear factors at zero leaves a quadratic with discriminant −1720128. A real root would make this discriminant a real square.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.result`
