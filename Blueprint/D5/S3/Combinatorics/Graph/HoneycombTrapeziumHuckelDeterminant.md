# Honeycomb trapezia and reduced Pascal determinants

## Abstract

The determinant of a honeycomb trapezium's Hückel matrix equals the determinant of Molinari's reduced Pascal matrix, for arbitrary boundary weights in any commutative ring.

**Definition 1.1 (The horizontal blocks).**

$$\forall R \in \operatorname{Type},\; (\operatorname{CommRing}\left(R\right)) \Rightarrow (\forall x \in \mathbb{N} \to R,\; \forall y \in \mathbb{N} \to R,\; \forall m \in \mathbb{N},\; \forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{sourceT}\left(x, y, m, i, j\right) = \begin{cases}\operatorname{x}\left(0\right) + \operatorname{y}\left(0\right) & m = 0\\1 & (i + 1 = j) \lor (j + 1 = i)\\\operatorname{y}\left(m\right) & (i = 0) \land (j = 2 \cdot m)\\\operatorname{x}\left(m\right) & (i = 2 \cdot m) \land (j = 0)\\0 & \operatorname{otherwise}\end{cases})$$

*Formalization.* `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.sourceT` (`✓ std3`).

*Citation.* L. G. Molinari (2022). *Graphene nanocones and Pascal matrices*. DOI: [10.48550/arXiv.2206.14428](https://doi.org/10.48550/arXiv.2206.14428). URL: <https://arxiv.org/abs/2206.14428v2>.

*Commentary.*

Molinari, arXiv:2206.14428v2, page 4: “A block Tₘ(xₘ,yₘ) is a square matrix of size 2m+1 that describes a row of 2m+1 atoms with boundary parameters xₘ,yₘ:”. The displayed T_0 is x_0+y_0; for positive m, T_m has unit entries at adjacent sites, y_m at (0,2m), and x_m at (2m,0). sourceT gives exactly these entries. Its natural-number arguments i,j are restricted to Fin(2m+1) when used as a block. Cases are read in the displayed order.

**Definition 1.2 (The vertical blocks).**

$$\forall R \in \operatorname{Type},\; (\operatorname{CommRing}\left(R\right)) \Rightarrow (\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{sourceR}\left(i, j\right) = \begin{cases}1 & (\operatorname{mod}\left(i, 2\right) = 1) \land (i = j + 1)\\0 & \operatorname{otherwise}\end{cases})$$

*Formalization.* `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.sourceR` (`✓ std3`).

*Citation.* L. G. Molinari (2022). *Graphene nanocones and Pascal matrices*. DOI: [10.48550/arXiv.2206.14428](https://doi.org/10.48550/arXiv.2206.14428). URL: <https://arxiv.org/abs/2206.14428v2>.

*Commentary.*

Molinari, page 4: “The blocks Rₘ are (2m+1)×(2m−1), with unit elements for the vertical edges in the graph, joining atoms in rows m−1 and m:”. The displayed R_1, R_2 and R_3 put ones exactly at (2j+1,2j). sourceR is this entry rule; the block dimensions restrict its natural arguments. The operator mod is natural-number remainder.

**Definition 1.3 (The triangle matrix).**

$$\forall R \in \operatorname{Type},\; (\operatorname{CommRing}\left(R\right)) \Rightarrow (\forall n \in \mathbb{N},\; \forall x \in \mathbb{N} \to R,\; \forall y \in \mathbb{N} \to R,\; \forall a \in (\Sigma m: \operatorname{Fin}\left(n + 1 - 0\right), \operatorname{Fin}\left(2 \cdot (\operatorname{val}\left(m\right) + 0) + 1\right)),\; \forall b \in (\Sigma m: \operatorname{Fin}\left(n + 1 - 0\right), \operatorname{Fin}\left(2 \cdot (\operatorname{val}\left(m\right) + 0) + 1\right)),\; \operatorname{sourceTriangle}\left(n, x, y, a, b\right) = \begin{cases}\operatorname{sourceT}\left(x, y, \operatorname{val}\left(\operatorname{fst}\left(a\right)\right), \operatorname{val}\left(\operatorname{snd}\left(a\right)\right), \operatorname{val}\left(\operatorname{snd}\left(b\right)\right)\right) & \operatorname{fst}\left(a\right) = \operatorname{fst}\left(b\right)\\\operatorname{sourceR}\left(\operatorname{val}\left(\operatorname{snd}\left(a\right)\right), \operatorname{val}\left(\operatorname{snd}\left(b\right)\right)\right) & \operatorname{val}\left(\operatorname{fst}\left(a\right)\right) = \operatorname{val}\left(\operatorname{fst}\left(b\right)\right) + 1\\\operatorname{sourceR}\left(\operatorname{val}\left(\operatorname{snd}\left(b\right)\right), \operatorname{val}\left(\operatorname{snd}\left(a\right)\right)\right) & \operatorname{val}\left(\operatorname{fst}\left(b\right)\right) = \operatorname{val}\left(\operatorname{fst}\left(a\right)\right) + 1\\0 & \operatorname{otherwise}\end{cases})$$

*Formalization.* `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.sourceTriangle` (`✓ std3`).

*Citation.* L. G. Molinari (2022). *Graphene nanocones and Pascal matrices*. DOI: [10.48550/arXiv.2206.14428](https://doi.org/10.48550/arXiv.2206.14428). URL: <https://arxiv.org/abs/2206.14428v2>.

*Commentary.*

The source block tridiagonal matrix has T_m on its diagonal, R_m below the diagonal, and R_m transposed above it (page 4). Its dependent index type is Sigma m : Fin(n+1-k), Fin(2(val(m)+k)+1). An element a has first coordinate a.fst, second coordinate a.snd, and val extracts a Fin coordinate's natural value. At k=0 this retains the source's row order and within-row site order. All formulas use a commutative ring R and functions x,y : N to R. Natural subtraction truncates at zero; finite-type parameters have that same convention. The triangle entry formula includes every zero block.

**Definition 1.4 (The trapezium matrix).**

$$\forall R \in \operatorname{Type},\; (\operatorname{CommRing}\left(R\right)) \Rightarrow (\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall x \in \mathbb{N} \to R,\; \forall y \in \mathbb{N} \to R,\; \forall a \in (\Sigma m: \operatorname{Fin}\left(n + 1 - k\right), \operatorname{Fin}\left(2 \cdot (\operatorname{val}\left(m\right) + k) + 1\right)),\; \forall b \in (\Sigma m: \operatorname{Fin}\left(n + 1 - k\right), \operatorname{Fin}\left(2 \cdot (\operatorname{val}\left(m\right) + k) + 1\right)),\; \operatorname{huckel}\left(k, n, x, y, a, b\right) = \operatorname{sourceTriangle}\left(n, x, y, (\operatorname{mk}\left(\operatorname{val}\left(\operatorname{fst}\left(a\right)\right) + k\right), \operatorname{mk}\left(\operatorname{val}\left(\operatorname{snd}\left(a\right)\right)\right)), (\operatorname{mk}\left(\operatorname{val}\left(\operatorname{fst}\left(b\right)\right) + k\right), \operatorname{mk}\left(\operatorname{val}\left(\operatorname{snd}\left(b\right)\right)\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.huckel` (`✓ std3`).

*Citation.* L. G. Molinari (2022). *Graphene nanocones and Pascal matrices*. DOI: [10.48550/arXiv.2206.14428](https://doi.org/10.48550/arXiv.2206.14428). URL: <https://arxiv.org/abs/2206.14428v2>.

*Commentary.*

Molinari, page 9: “If rows 0,1,...,k−1 are removed from a honeycomb triangle, a trapezium results, with rows of lengths 2k+1, ... , 2n+1. The corresponding Hückel matrix Hₖ,ₙ(𝐱,𝐲) is obtained by deleting the first k² rows and columns of Hₙ(𝐱,𝐲). Its size is (n+1)²−k²=(2k+1) + ... + (2n+1).” The retained index adds k to the row coordinate and keeps the site coordinate. The entry formula is the principal submatrix along this retained index, so it deletes precisely the first 1+3+...+(2k−1)=k² sites. The notation mk means Fin.mk; its membership inequalities are exactly those forced by the source and retained index types. For k<=n there are the rows k through n, including their boundary weights.

**Definition 1.5 (The displayed reduced Pascal matrix).**

$$\forall R \in \operatorname{Type},\; (\operatorname{CommRing}\left(R\right)) \Rightarrow (\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall x \in \mathbb{N} \to R,\; \forall y \in \mathbb{N} \to R,\; \forall i \in \operatorname{Fin}\left(n + 1 - k\right),\; \forall j \in \operatorname{Fin}\left(n + 1 - k\right),\; \operatorname{reducedPascal}\left(k, n, x, y, i, j\right) = \begin{cases}\operatorname{x}\left(n - \operatorname{val}\left(i\right)\right) + \operatorname{y}\left(n - \operatorname{val}\left(i\right)\right) & i = j\\(-1)^{\operatorname{val}\left(j\right) - \operatorname{val}\left(i\right)} \cdot \operatorname{cast}\left(\begin{pmatrix}n - \operatorname{val}\left(i\right)\\\operatorname{val}\left(j\right) - \operatorname{val}\left(i\right)\end{pmatrix}\right) \cdot \operatorname{y}\left(n - \operatorname{val}\left(i\right)\right) & \operatorname{val}\left(i\right) < \operatorname{val}\left(j\right)\\\operatorname{cast}\left(\begin{pmatrix}n - \operatorname{val}\left(j\right)\\\operatorname{val}\left(i\right) - \operatorname{val}\left(j\right)\end{pmatrix}\right) \cdot \operatorname{x}\left(n - \operatorname{val}\left(j\right)\right) & \operatorname{otherwise}\end{cases})$$

*Formalization.* `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.reducedPascal` (`✓ std3`).

*Citation.* L. G. Molinari (2022). *Graphene nanocones and Pascal matrices*. DOI: [10.48550/arXiv.2206.14428](https://doi.org/10.48550/arXiv.2206.14428). URL: <https://arxiv.org/abs/2206.14428v2>.

*Commentary.*

This is the matrix displayed after Conjecture 2 on page 9. Its indices i,j run through Fin(n+1-k); index i labels source row n-val(i), so rows and columns run from n down to k. The two-line parenthesized symbols are binomial coefficients Nat.choose, mapped to R by its natural-number homomorphism. The upper entries have alternating signs multiplying y; the lower entries have positive binomial coefficients multiplying x. Cases use Fin equality on the diagonal and natural values for the strict order.

**Definition 1.6 (Conjecture 2).**

$$claim \Leftrightarrow (\forall R \in \operatorname{Type},\; (\operatorname{CommRing}\left(R\right)) \Rightarrow (\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; (k \le n) \Rightarrow (\forall x \in \mathbb{N} \to R,\; \forall y \in \mathbb{N} \to R,\; \operatorname{det}\left(\operatorname{huckel}\left(k, n, x, y\right)\right) = \operatorname{det}\left(\operatorname{reducedPascal}\left(k, n, x, y\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.claim` (`✓ std3`).

*Citation.* L. G. Molinari (2022). *Graphene nanocones and Pascal matrices*. DOI: [10.48550/arXiv.2206.14428](https://doi.org/10.48550/arXiv.2206.14428). URL: <https://arxiv.org/abs/2206.14428v2>.

*Commentary.*

Molinari, arXiv:2206.14428v2, section 5, page 9, Conjecture 2, verbatim: “The determinant of the Hückel matrix Hₖ,ₙ(𝐱, 𝐲) of a honeycomb trapezium with rows with 2k+1, 2k+3, ... , 2n+1 sites, size (n+1)²−k², is equal to the determinant of the following matrix of size n+1−k:”. The displayed matrix is reducedPascal. The encoding quantifies over every commutative ring R, every k,n in N with k<=n, and arbitrary functions x,y : N to R. The source's real and complex boundary parameters are specializations. At k=0 this gives the triangle identity in Conjecture 1; the assertion here is Conjecture 2.

**Theorem 1.7 (Equality of the determinants).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result` (`✓ std3`). ∎

*Resolves.* `Problems/molinari-2022-honeycomb-trapezium-huckel-determinant` (proved) by `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"molinari-2022-honeycomb-trapezium-huckel-determinant","declaration_gid":"D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* L. G. Molinari (2022). *Graphene nanocones and Pascal matrices*. DOI: [10.48550/arXiv.2206.14428](https://doi.org/10.48550/arXiv.2206.14428). URL: <https://arxiv.org/abs/2206.14428v2>.

*Commentary.*

Molinari's Conjecture 2 (the claim) holds. Separate even and odd sites in each row. Apart from the boundary weights, edges join different colours, giving a matrix with blocks X, B transposed, B and zero. The lift U at blue site (m,j), in row l, is (-1)^j times the binomial coefficient C(j,m-l) when l<=m, and zero otherwise. Pascal's recurrence gives BU=0, and the left endpoints give the identity. The restriction of B to the other blue sites is lower triangular with diagonal one. A change of blue coordinates and a Schur complement therefore give det(H)=(-1)^q det(U transposed X U), with q the number of red sites. The right endpoints of U give W_ml=(-1)^m C(m,l), hence U transposed X U=diag(y)W+W transposed diag(x). Multiplying columns by (-1)^l and then reversing the rows and the columns simultaneously gives reducedPascal; the column-sign determinant is (-1)^q and cancels the earlier sign. Every step takes place over an arbitrary commutative ring. The paper supplies the conjecture; the proof is repository-produced.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.huckel`
- Truth anchor: `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.reducedPascal`
- Truth anchor: `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.sourceR`
- Truth anchor: `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.sourceT`
- Truth anchor: `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.sourceTriangle`
