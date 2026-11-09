# Hardin and Barker's three-column array formulas

## Abstract

Exact three-column array counts, recurrence and formal generating series.

**Definition 1.1 (The literal arrays).**

$$\forall n \in \mathbb{N},\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right),\; \operatorname{IsSourceArray}\left(X\right) = (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(2\right),\; \operatorname{List}.\operatorname{Pairwise}\left((\operatorname{fun} x y : \mathbb{Z} \mapsto x \ne y), [(\operatorname{val}\left(X\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) : \mathbb{Z}) - (\operatorname{val}\left(X\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) : \mathbb{Z}), (\operatorname{val}\left(X\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) : \mathbb{Z}) - (\operatorname{val}\left(X\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) : \mathbb{Z}), (\operatorname{val}\left(X\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) : \mathbb{Z}) - (\operatorname{val}\left(X\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) : \mathbb{Z}), (\operatorname{val}\left(X\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) : \mathbb{Z}) - (\operatorname{val}\left(X\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) : \mathbb{Z})]\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.IsSourceArray` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209721: three-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209721/internal>.

*Commentary.*

OEIS A209721, revision 43, NAME: "1/4 the number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences." Matrix has n+1 labelled rows and three labelled columns, with entries Fin 3. Fin.castSucc and Fin.succ select the two consecutive row or column positions. For each square with top row a,b and bottom row c,d the integer list is [b-a,d-b,c-d,a-c], and List.Pairwise tests that all differences are unequal. val is the natural representative, coerced to the integers before subtraction. Every adjacent square is tested; rotations, reflections and translations are not identified.

**Definition 1.2 (One quarter of the raw count).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{card}\left(\{X : \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right) // \operatorname{IsSourceArray}\left(X\right)\}\right) : \mathbb{Q})}{4}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209721: three-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209721/internal>.

*Commentary.*

OEIS A209721, revision 43, NAME: "1/4 the number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences." Nat.card counts the full subtype of these labelled arrays. The result is coerced to the rationals and divided by rational four. Offset 1,1 restricts the source formulas to positive n; a is defined for every natural input.

**Definition 1.3 (Coefficients of the ordinary formal series).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) = (\operatorname{PowerSeries}.\operatorname{coeff}\left(0, A\right) = 0 \land \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = \operatorname{a}\left(n\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.IsSourceSeries` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209721: three-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209721/internal>.

*Commentary.*

OEIS A209721, revision 43, FORMULA: "Empirical g.f.: x*(3+x-5*x^2)/((1-x)*(1-2*x^2)). [_Colin Barker_, Mar 23 2012]" With offset 1,1, the ordinary series has zero constant coefficient and coefficient a(n) for every n at least one. The carrier is PowerSeries over the rationals.

**Definition 1.4 (Recurrence, existence and generating identity).**

$$\mathrm{claim} = ((\forall m \in \mathbb{N},\; \operatorname{a}\left(m + 4\right) = \operatorname{a}\left(m + 3\right) + 2 \cdot \operatorname{a}\left(m + 2\right) - 2 \cdot \operatorname{a}\left(m + 1\right)) \land \left((\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Rightarrow A \cdot ((1 - \operatorname{PowerSeries}.\operatorname{X}) \cdot (1 - 2 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2})) = \operatorname{PowerSeries}.\operatorname{X} \cdot (3 + \operatorname{PowerSeries}.\operatorname{X} - 5 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2}))\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.claim` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2012). *OEIS A209721: three-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209721/internal>.

*Commentary.*

OEIS A209721, revision 43, FORMULA (the entry has no page numbers): Empirical: a(n) = a(n-1) +2*a(n-2) -2*a(n-3). Empirical g.f.: x*(3+x-5*x^2)/((1-x)*(1-2*x^2)). [_Colin Barker_, Mar 23 2012] The recurrence index is m+4 for natural m, exactly the indices at least four. The series assertion includes existence and holds for every series with the specified coefficients. Multiplication by the denominator expresses the rational generating identity in PowerSeries, since its constant coefficient is one.

**Theorem 1.5 (The full three-column counting theorem).**

$$(\forall m \in \mathbb{N},\; \operatorname{a}\left(m + 4\right) = \operatorname{a}\left(m + 3\right) + 2 \cdot \operatorname{a}\left(m + 2\right) - 2 \cdot \operatorname{a}\left(m + 1\right)) \land \left((\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Rightarrow A \cdot ((1 - \operatorname{PowerSeries}.\operatorname{X}) \cdot (1 - 2 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2})) = \operatorname{PowerSeries}.\operatorname{X} \cdot (3 + \operatorname{PowerSeries}.\operatorname{X} - 5 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2}))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-barker-a209721` (proved) by `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-barker-a209721","declaration_gid":"D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2012). *OEIS A209721: three-column arrays with distinct clockwise edge differences*. URL: <https://oeis.org/A209721/internal>.

*Commentary.*

Reading consecutive rows gives an equivalence between the array subtype and walks in the exact 27-state compatibility graph. Prepending a state and taking the tail identify the finite successor fibers. Induction on arbitrary walk length proves the transfer count, including isolated states and disconnected graphs. The transfer vector satisfies u(n+4)+2*u(n+1)=u(n+3)+2*u(n+2); summing over starts and dividing by four gives the recurrence for the array count. PowerSeries.mk supplies a series with zero constant coefficient. Coefficient extensionality, the recurrence and a(1)=3, a(2)=4, a(3)=5 give the formal identity. No analytic convergence premise is used.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.IsSourceArray`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.IsSourceSeries`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.a`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.result`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences](HardinBarkerA209723EdgeDifferences.md)
