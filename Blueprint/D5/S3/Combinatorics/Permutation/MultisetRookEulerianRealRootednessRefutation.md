# The full multiset rook-Eulerian polynomial

## Abstract

Remaining-content counting for the full multiset rook-Eulerian polynomial.

The source is Alexandersson, Jal and Quemener, arXiv:2502.05939v1, Section 3.3, equation (10) and the first clause of Conjecture 28. A word contains a(c) copies of the positive letter c+1 and fits the row bounds l. Repeated letters and repeated columns are allowed. The polynomial R is the original sum of X raised to the strict adjacent ascent count, over distinct words W. The original W, asc and R definitions are used directly. There is no initial or terminal ascent, skew inner board, nonattacking restriction or first-letter refinement.

**Definition 1.1 (The full real-rootedness assertion).**

$$claim = \left(\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall l \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall a \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; 0 < n \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; 0 < \operatorname{l}\left(i\right)\right) \Rightarrow \left(\operatorname{Monotone}\left(l\right) \Rightarrow \left(\sum_{c\in\operatorname{Fin}\left(k\right)}\operatorname{a}\left(c\right) = n \Rightarrow \operatorname{Splits}\left(\operatorname{R}\left(l, a\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.claim` (`✓ std3`).

*Citation.* Per Alexandersson, Aryaman Jal, and Maena Quemener (2025). *Real-rootedness of rook-Eulerian polynomials*. DOI: [10.48550/arXiv.2502.05939](https://doi.org/10.48550/arXiv.2502.05939). URL: <https://arxiv.org/abs/2502.05939v1>.

*Commentary.*

The assertion quantifies every positive row count n, every alphabet size k, every positive weakly increasing row-bound function l, and every natural-valued content a summing to n. It requires the original full R to split over the real field, retaining algebraic multiplicity. Polynomial.Splits includes the zero polynomial; no admissible-word or nonzero-polynomial premise is added. This is only the first clause. The separate interlacing refutation concerns the second clause.

**Definition 1.2 (The boundary edge).**

$$\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{edge}\left(none, j\right) = 0 \land \operatorname{edge}\left(\operatorname{some}\left(i\right), j\right) = \operatorname{ite}\left(i < j, 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An absent previous letter contributes exponent zero. A present previous letter i contributes one exactly when i<j. Equal adjacent letters therefore contribute zero.

**Definition 1.3 (Remaining-content recurrence).**

$$\left(\forall m \in \operatorname{Multiset}\left(\mathbb{N}\right),\; \forall h \in \operatorname{Option}\left(\mathbb{N}\right),\; \operatorname{count}\left(nil, m, h\right) = \operatorname{ite}\left(m = 0, 1, 0\right)\right) \land \left(\forall r \in \mathbb{N},\; \forall s \in \operatorname{List}\left(\mathbb{N}\right),\; \forall m \in \operatorname{Multiset}\left(\mathbb{N}\right),\; \forall h \in \operatorname{Option}\left(\mathbb{N}\right),\; \operatorname{count}\left(\operatorname{cons}\left(r, s\right), m, h\right) = \sum_{j\in\operatorname{filter}\left(\operatorname{toFinset}\left(m\right), (j:\mathbb{N})\mapsto0 < j \land j \le r\right)}X^{\operatorname{edge}\left(h, j\right)} \cdot \operatorname{count}\left(s, \operatorname{erase}\left(m, j\right), \operatorname{some}\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state consists of the remaining row list r, a multiset m of remaining positive letters, and an optional previous letter h. On a nonempty row list, the recurrence chooses each distinct available label j once, subject to 0<j and j no larger than the next row bound. It erases one copy of j and multiplies the continuation by X to the boundary-edge exponent. There is no factor equal to the number of remaining copies of j. Each step shortens the row list. With no rows left, the value is one exactly when no letters remain, and zero otherwise. In particular an empty board with empty content contributes the unique empty word, and impossible completions contribute zero.

**Theorem 1.4 (Equality with the original full word sum).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall l \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall a \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; \sum_{c\in\operatorname{Fin}\left(k\right)}\operatorname{a}\left(c\right) = n \Rightarrow \operatorname{map}\left(\operatorname{count}\left(\operatorname{ofFn}\left(l\right), \operatorname{m}\left(a\right), none\right), \operatorname{NatCastReal}\left(\right)\right) = \operatorname{R}\left(l, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.count_eq_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiset m(a) contains a(c) copies of c+1 for each c in Fin(k), and ofFn(l) lists the row bounds in their original order. The map from natural to real coefficients is the canonical cast homomorphism. The total-content equality is essential: it makes each rearrangement have exactly n letters, so every original getD row query is in range. The theorem requires neither positivity nor monotonicity of the board and includes n=0, k=0 and zero-content labels.

Partition completions by their next letter. Erasing that letter and prepending it are inverse on the corresponding class, and classes for different next letters are disjoint. The multiset equality records the exact multiplicities. Pinned List.mem_permutations' identifies the original permutation-list membership with permutation of the content list; toFinset removes repeated listings of the same word. A separate head-edge calculation identifies the recursive weight with X to the original asc. Summing the disjoint classes proves the recurrence equality. Thus the recurrence computes the full polynomial of the source, including all repeated letters, rather than a refinement or a finite replacement.

**Theorem 1.5 (A counterexample to full real-rootedness).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/alexandersson-jal-quemener-2025-rook-eulerian-interlacing` (refuted) by `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alexandersson-jal-quemener-2025-rook-eulerian-interlacing","declaration_gid":"D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take n=120 and k=6. The board has three rows of length 2, four of length 3, ten of length 4, two of length 5, and 101 of length 6. All bounds are positive and weakly increasing. The content is (6,1,4,8,1,100), with total 120. The first 19 rows exclude the letter 6. Every remaining tail therefore contains 100 sixes and exactly one smaller letter j. For the last prefix letter h, its exact completion polynomial is X^(1+[h<j])+X+99X^2: the two endpoint positions and 99 internal positions account for every tail once. The source recurrence proves this identity by induction, then evaluates the 664 reachable prefix states. Applying the exact full-R counting bridge gives the following full polynomial, including its two zero low coefficients.

$R = X^{2} + 261 \cdot X^{3} + 21704 \cdot X^{4} + 591814 \cdot X^{5} + 5372605 \cdot X^{6} + 18550680 \cdot X^{7} + 27147806 \cdot X^{8} + 17137014 \cdot X^{9} + 4318325 \cdot X^{10} + 352440 \cdot X^{11}$

In particular R(1)=73492650 and the degree is 11. At x=-1/100 the value of (R'(x))^2-R(x)R''(x) is exactly -2294232329562528073294509555513/12500000000000000000000000000000000000, which is negative. The original laguerre_splits theorem in SourceJensenPositiveExtension states that every real polynomial splitting over the reals has a nonnegative value of this expression at every real argument. Its hypotheses require no positivity, monicity, nonzero condition, root sign or simple roots. Applying it directly contradicts the displayed value.

Thus the first clause of Conjecture 28 fails for the original full multiset polynomial. This conclusion uses neither refined interlacing nor numerical root isolation. It preserves repeated columns and strict adjacent ascents. The earlier six-row interlacing counterexample remains a separate result about the second clause. Rectangular-board theorems and the distinct-letter theorem are unaffected.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.count`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.count_eq_R`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.edge`
- Truth anchor: `D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.result`
- Dependency: [D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation](MultisetRookEulerianInterlacingRefutation.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenPositiveExtension](../../Zeros/Jensen/SourceJensenPositiveExtension.md)
