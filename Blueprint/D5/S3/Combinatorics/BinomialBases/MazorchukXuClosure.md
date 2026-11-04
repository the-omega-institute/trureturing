# Triangular subsets and ordered closure

## Abstract

The literal Mazorchuk-Xu triangular family has a repeated-point closure rule equivalent to two universal rules on ordered edges.

**Definition 1.1 (The source triangle).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{triangle}\left(n\right) = \{p \in \operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)| (\operatorname{fst}\left(p\right) \le \operatorname{snd}\left(p\right)) \land (\operatorname{snd}\left(p\right) \le n)\}$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.triangle` (`✓ std3`).

*Citation.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Natural coordinates represent the nonnegative integer coordinates in Section 3, before Section 3.1. No nonempty-row condition is imposed.

**Definition 1.2 (Repeated-point closure).**

$$\forall Y \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; (\operatorname{Star}\left(Y\right)) \Leftrightarrow (\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall e \in \operatorname{Nat}\left(\right),\; \forall f \in \operatorname{Nat}\left(\right),\; ((((((((((a, b) \in Y) \land ((c, d) \in Y)) \land ((e, f) \in Y)) \land (a \le c)) \land (c \le b)) \land (a \le e)) \land (e \le b)) \land (b \le d)) \land (b \le f)) \Rightarrow (((\operatorname{max}\left(c, e\right), \operatorname{max}\left(d, f\right)) \in Y) \land ((b < \operatorname{min}\left(d, f\right)) \Rightarrow ((b + 1, \operatorname{min}\left(d, f\right)) \in Y))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.Star` (`✓ std3`).

*Citation.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The three selected points may coincide. Both forced points, including the conditional successor/minimum point, are retained.

**Definition 1.3 (First-column count).**

$$\forall Y \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; \operatorname{firstColumnCard}\left(Y\right) = \operatorname{card}\left(\{p \in Y| \operatorname{fst}\left(p\right) = 0\}\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.firstColumnCard` (`✓ std3`).

*Citation.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Only points whose first coordinate is zero are counted.

**Definition 1.4 (The finite family R(n,k)).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Nat}\left(\right),\; \operatorname{family}\left(n, k\right) = \{Y \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right)| ((Y \subseteq \operatorname{triangle}\left(n\right)) \land (\operatorname{Star}\left(Y\right))) \land (\operatorname{firstColumnCard}\left(Y\right) = k)\}$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.family` (`✓ std3`).

*Citation.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

All subsets of the triangle are tested. Empty subsets and empty rows remain in the domain.

**Definition 1.5 (The cardinal r(n,k)).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Nat}\left(\right),\; \operatorname{count}\left(n, k\right) = \operatorname{card}\left(\operatorname{family}\left(n, k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.count` (`✓ std3`).

*Citation.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The first argument is a natural number. This definition introduces no recurrence value at minus one.

**Definition 1.6 (The complete polynomiality question).**

$$(\operatorname{Conjecture}\left(\right)) \Leftrightarrow (\forall i \in \operatorname{Nat}\left(\right),\; \exists p \in \operatorname{Polynomial}\left(\operatorname{Rat}\left(\right)\right),\; ((\operatorname{natDegree}\left(p\right) = 2 \cdot i) \land (\operatorname{leadingCoeff}\left(p\right) = \operatorname{inv}\left(\operatorname{castRat}\left(\operatorname{factorial}\left(i\right)\right)\right))) \land (\forall n \in \operatorname{Nat}\left(\right),\; (i \le n + 1) \Rightarrow (\operatorname{eval}\left(p, \operatorname{castRat}\left(n\right)\right) = \operatorname{castRat}\left(\operatorname{count}\left(n, n + 1 - i\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.Conjecture` (`✓ std3`).

*Citation.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

For each deficit one rational polynomial must work at every valid natural rank, with exact degree and leading coefficient. Rational coefficients embed into real numerical values. This is the question's statement; no proof of this proposition is asserted here. Deficits zero through three are prior source results.

**Definition 1.7 (Point-to-edge relation).**

$$\forall Y \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; \forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; (\operatorname{pointEdges}\left(Y, a, b\right)) \Leftrightarrow ((a < b) \land ((a, b - 1) \in Y))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.pointEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The source point (a,b) becomes the strict edge (a,b+1). Natural subtraction appears only after strict endpoint order has ensured a positive upper endpoint.

**Definition 1.8 (The rules P and J).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(A\right)] \forall E \in A \to \left(A \to \operatorname{Prop}\left(\right)\right),\; (\operatorname{Rules}\left(E\right)) \Leftrightarrow (((\forall a \in A,\; \forall b \in A,\; (\operatorname{E}\left(a, b\right)) \Rightarrow (a < b)) \land (\forall a \in A,\; \forall b \in A,\; \forall c \in A,\; \forall d \in A,\; (((((\operatorname{E}\left(a, b\right)) \land (\operatorname{E}\left(c, d\right))) \land (a \le c)) \land (c < b)) \land (b < d)) \Rightarrow (\operatorname{E}\left(b, d\right)))) \land (\forall a \in A,\; \forall b \in A,\; \forall c \in A,\; \forall d \in A,\; \forall e \in A,\; \forall f \in A,\; (((((((((\operatorname{E}\left(a, b\right)) \land (\operatorname{E}\left(c, d\right))) \land (\operatorname{E}\left(e, f\right))) \land (a \le c)) \land (c < b)) \land (a \le e)) \land (e < b)) \land (b \le d)) \land (b \le f)) \Rightarrow (\operatorname{E}\left(\operatorname{max}\left(c, e\right), \operatorname{max}\left(d, f\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.Rules` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

P propagates an overlapping pair to its upper-right edge. J joins the two lower endpoints and the two upper endpoints by maxima. Ordered edges are strict.

**Theorem 1.9 (Triangle membership).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; ((a, b) \in \operatorname{triangle}\left(n\right)) \Leftrightarrow ((a \le b) \land (b \le n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.mem_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The finite range construction is exactly a less-than-or-equal b less-than-or-equal n.

**Theorem 1.10 (Literal source equivalence).**

$$\forall Y \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; (\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; ((a, b) \in Y) \Rightarrow (a \le b)) \Rightarrow ((\operatorname{Star}\left(Y\right)) \Leftrightarrow (\operatorname{Rules}\left(\operatorname{pointEdges}\left(Y\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.star_iff_rules` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Repeating the second source point gives P. J is the source's maximum conclusion. Conversely P, applied to the premise with the smaller upper endpoint, recovers the entire successor/minimum conclusion. This proves both directions for every triangular subset, including repetitions and empty subsets.

**Theorem 1.11 (Exact finite-family membership).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Nat}\left(\right),\; \forall Y \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; (Y \in \operatorname{family}\left(n, k\right)) \Leftrightarrow (((Y \subseteq \operatorname{triangle}\left(n\right)) \land (\operatorname{Rules}\left(\operatorname{pointEdges}\left(Y\right)\right))) \land (\operatorname{firstColumnCard}\left(Y\right) = k))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.mem_family_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The source-family test retains the triangle bound, both ordered-edge rules and the exact first-column statistic.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.Conjecture`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.Rules`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.Star`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.count`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.family`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.firstColumnCard`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.mem_family_iff`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.mem_triangle`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.pointEdges`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.star_iff_rules`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure.triangle`
