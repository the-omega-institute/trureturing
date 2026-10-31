# Hardin and Barker's five-column array formulas

## Abstract

Exact five-column array counts, parity, recurrence and formal generating series.

**Definition 1.1 (Distinct signed clockwise differences).**

$$\forall a \in \operatorname{Fin}\left(3\right),\; \forall b \in \operatorname{Fin}\left(3\right),\; \forall c \in \operatorname{Fin}\left(3\right),\; \forall d \in \operatorname{Fin}\left(3\right),\; \operatorname{DistinctClockwise}\left(a, b, c, d\right) = \operatorname{List}.\operatorname{Pairwise}\left((\operatorname{fun} x y : \mathbb{Z} \mapsto x \ne y), [(\operatorname{val}\left(b\right) : \mathbb{Z}) - (\operatorname{val}\left(a\right) : \mathbb{Z}), (\operatorname{val}\left(d\right) : \mathbb{Z}) - (\operatorname{val}\left(b\right) : \mathbb{Z}), (\operatorname{val}\left(c\right) : \mathbb{Z}) - (\operatorname{val}\left(d\right) : \mathbb{Z}), (\operatorname{val}\left(a\right) : \mathbb{Z}) - (\operatorname{val}\left(c\right) : \mathbb{Z})]\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.DistinctClockwise` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209723: five-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209723/internal>.

*Commentary.*

OEIS A209723, revision 11, NAME: "1/4 the number of (n+1) X 5 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences." For a square with top row a,b and bottom row c,d, clockwise differences are b-a,d-b,c-d,a-c in the integers. Entries have type Fin 3; val is the natural representative and each representative is coerced to the integers before subtraction.

**Definition 1.2 (The literal arrays).**

$$\forall n \in \mathbb{N},\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(5\right), \operatorname{Fin}\left(3\right)\right),\; \operatorname{IsSourceArray}\left(X\right) = (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \operatorname{DistinctClockwise}\left(X\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right), X\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), \operatorname{Fin}.\operatorname{succ}\left(j\right)\right), X\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right), X\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.IsSourceArray` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209723: five-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209723/internal>.

*Commentary.*

OEIS A209723, revision 11, NAME: "1/4 the number of (n+1) X 5 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences." Matrix has n+1 labelled rows and five labelled columns, with entries Fin 3. Fin.castSucc and Fin.succ select the two consecutive row or column positions. Every adjacent square is tested; rotations, reflections and translations are not identified.

**Definition 1.3 (One quarter of the raw count).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{card}\left(\{X : \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(5\right), \operatorname{Fin}\left(3\right)\right) // \operatorname{IsSourceArray}\left(X\right)\}\right) : \mathbb{Q})}{4}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209723: five-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209723/internal>.

*Commentary.*

OEIS A209723, revision 11, NAME: "1/4 the number of (n+1) X 5 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences." Nat.card counts the full subtype of these labelled arrays. The result is coerced to the rationals and divided by rational four. Offset 1,1 restricts the source formulas to positive n; a is defined for every natural input.

**Definition 1.4 (Coefficients of the ordinary formal series).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) = (\operatorname{PowerSeries}.\operatorname{coeff}\left(0, A\right) = 0 \land \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = \operatorname{a}\left(n\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.IsSourceSeries` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209723: five-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209723/internal>.

*Commentary.*

OEIS A209723, revision 11, FORMULA: "G.f.: x*(6 + x - 11*x^2) / ((1 - x)*(1 - 2*x^2))." With offset 1,1, the ordinary series has zero constant coefficient and coefficient a(n) for every n at least one. The carrier is PowerSeries over the rationals.

**Definition 1.5 (Parity, recurrence, existence and generating identity).**

$$\mathrm{claim} = ((\forall m \in \mathbb{N},\; \operatorname{a}\left(2 \cdot (m + 1)\right) = 3 \cdot (2 : \mathbb{Q})^{m} + 4) \land \left((\forall m \in \mathbb{N},\; \operatorname{a}\left(2 \cdot m + 1\right) = (2 : \mathbb{Q})^{m + 1} + 4) \land \left((\forall m \in \mathbb{N},\; \operatorname{a}\left(m + 4\right) = \operatorname{a}\left(m + 3\right) + 2 \cdot \operatorname{a}\left(m + 2\right) - 2 \cdot \operatorname{a}\left(m + 1\right)) \land \left((\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Rightarrow A \cdot ((1 - \operatorname{PowerSeries}.\operatorname{X}) \cdot (1 - 2 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2})) = \operatorname{PowerSeries}.\operatorname{X} \cdot (6 + \operatorname{PowerSeries}.\operatorname{X} - 11 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2}))\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.claim` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209723: five-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209723/internal>.

*Commentary.*

OEIS A209723, revision 11, FORMULA (the entry has no page numbers): Empirical: a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3). Conjectures from _Colin Barker_, Jul 12 2018: (Start) G.f.: x*(6 + x - 11*x^2) / ((1 - x)*(1 - 2*x^2)). a(n) = 3*2^(n/2 - 1) + 4 for n even. a(n) = 2^((n + 1)/2) + 4 for n odd. (End) The positive even index is 2*(m+1), the odd index is 2*m+1, and the recurrence index is m+4, for natural m. The series assertion includes existence and holds for every series with the specified coefficients. Multiplication by the denominator expresses the rational generating identity in PowerSeries, since its constant coefficient is one.

**Theorem 1.6 (The full five-column counting theorem).**

$$(\forall m \in \mathbb{N},\; \operatorname{a}\left(2 \cdot (m + 1)\right) = 3 \cdot (2 : \mathbb{Q})^{m} + 4) \land \left((\forall m \in \mathbb{N},\; \operatorname{a}\left(2 \cdot m + 1\right) = (2 : \mathbb{Q})^{m + 1} + 4) \land \left((\forall m \in \mathbb{N},\; \operatorname{a}\left(m + 4\right) = \operatorname{a}\left(m + 3\right) + 2 \cdot \operatorname{a}\left(m + 2\right) - 2 \cdot \operatorname{a}\left(m + 1\right)) \land \left((\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Rightarrow A \cdot ((1 - \operatorname{PowerSeries}.\operatorname{X}) \cdot (1 - 2 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2})) = \operatorname{PowerSeries}.\operatorname{X} \cdot (6 + \operatorname{PowerSeries}.\operatorname{X} - 11 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2}))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-barker-a209723-edge-differences` (proved) by `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-barker-a209723-edge-differences","declaration_gid":"D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2012). *OEIS A209723: five-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209723/internal>.

*Commentary.*

Reading consecutive rows gives an explicit equivalence between the array subtype and finite compatible row sequences. The exact row adjacency table has two branching three-vertex paths and sixteen deterministic starting rows. At odd length 2*m+1, the number from a fixed start is 2^m times its branching degree plus its deterministic indicator; at even length 2*m+2 it is 2^(m+1) times its branching indicator plus its deterministic indicator. The two-step induction holds for every natural m. Summing over starting rows and dividing by four proves both parity formulas. The affine relation a(n+3)=2*a(n+1)-4 yields the homogeneous recurrence. PowerSeries.mk gives existence, and coefficient extensionality gives the full generating identity without an analytic convergence premise.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.DistinctClockwise`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.IsSourceArray`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.IsSourceSeries`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.a`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.result`
