# Largest-gap cuts and real Golomb chambers

## Abstract

A cyclic perfect difference set cut at a largest gap gives the unique shortest ruler in its normalized real chamber.

**Definition 1.1 (Unique labelled cyclic differences).**

$$\begin{aligned}&\forall (m : \mathbb{N}) (x : \operatorname{Fin}\left(m+1\right) \to \mathbb{N}) (N : \mathbb{N}),\\&\operatorname{CyclicPerfectDifference}\left(x, N\right) \iff \forall (d : \mathbb{N}), 0 < d \to d < N \to\\&\quad\exists! (p : \operatorname{Fin}\left(m+1\right) \times \operatorname{Fin}\left(m+1\right)), p.1 \neq p.2 \land (x\left(p.2\right) : \mathbb{Z}) - (x\left(p.1\right) : \mathbb{Z}) \equiv (d : \mathbb{Z}) \pmod{(N : \mathbb{Z})}\end{aligned}$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.CyclicPerfectDifference` (`✓ std3`).

*Citation.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

For natural numbers m and N and natural marks x indexed by Fin (m + 1), every natural d with 0 < d < N has exactly one ordered pair (i, j) of distinct indices whose signed integer difference x(j) − x(i) is congruent to d modulo N in Int.ModEq. The labels and their order are part of the witness.

**Definition 1.2 (The normalized real chamber).**

$$\begin{aligned}&\forall (m : \mathbb{N}) (x : \operatorname{Fin}\left(m+1\right) \to \mathbb{N}) (y : \operatorname{Fin}\left(m+1\right) \to \mathbb{R}),\\&\operatorname{Chamber}\left(x, y\right) \iff y\left(0\right) = 0 \land\\&\quad(\forall (i j : \operatorname{Fin}\left(m+1\right)), i < j \to 1 \leq y\left(j\right) - y\left(i\right)) \land\\&\quad(\forall (i j k l : \operatorname{Fin}\left(m+1\right)), i < j \to k < l \to x\left(j\right) - x\left(i\right) < x\left(l\right) - x\left(k\right) \to\\&\quad\quad y\left(j\right) - y\left(i\right) + 1 \leq y\left(l\right) - y\left(k\right))\end{aligned}$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.Chamber` (`✓ std3`).

*Citation.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

For natural reference marks x and real marks y on the same Fin (m + 1), the chamber requires y(0) = 0 and y(j) − y(i) ≥ 1 for every i < j. For every i < j and k < l, whenever the reference natural distance x(j) − x(i) is strictly smaller than x(l) − x(k), the corresponding real distances satisfy y(j) − y(i) + 1 ≤ y(l) − y(k).

**Theorem 1.3 (Unique shortest ruler after a largest-gap cut).**

$$\begin{aligned}&\forall (m : \mathbb{N}) (x : \operatorname{Fin}\left(m+1\right) \to \mathbb{N}) (G : \mathbb{N}),\\&\quad0 < m \to x\left(0\right) = 0 \to \operatorname{StrictMono}\left(x\right) \to 0 < G \to\\&\quad(\forall (i : \operatorname{Fin}\left(m\right)), x\left(i.\operatorname{succ}\right) - x\left(i.\operatorname{castSucc}\right) \leq G) \to \operatorname{CyclicPerfectDifference}\left(x, x\left(\operatorname{Fin}.\operatorname{last}\left(m\right)\right) + G\right) \to\\&\quad(\forall (i j k l : \operatorname{Fin}\left(m+1\right)), i < j \to k < l \to x\left(j\right) - x\left(i\right) = x\left(l\right) - x\left(k\right) \to (i, j) = (k, l)) \land\\&\quad \operatorname{Chamber}\left(x, \lambda i \mapsto (x\left(i\right) : \mathbb{R})\right) \land (\forall (y : \operatorname{Fin}\left(m+1\right) \to \mathbb{R}), \operatorname{Chamber}\left(x, y\right) \to y\left(\operatorname{Fin}.\operatorname{last}\left(m\right)\right) \leq (x\left(\operatorname{Fin}.\operatorname{last}\left(m\right)\right) : \mathbb{R}) \to\\&\quad\quad\forall (i : \operatorname{Fin}\left(m+1\right)), y\left(i\right) = (x\left(i\right) : \mathbb{R}))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result` (`✓ std3`). ∎

*Resolves.* `Problems/notik-singer-chamber` (proved) by `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"notik-singer-chamber","declaration_gid":"D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Acknowledgement.* James Singer (1938). *A theorem in finite projective geometry and some applications to number theory*. DOI: [10.1090/s0002-9947-1938-1501951-4](https://doi.org/10.1090/s0002-9947-1938-1501951-4). URL: <https://doi.org/10.1090/s0002-9947-1938-1501951-4>.

*Commentary.*

Let m > 0, let x be strictly increasing natural marks on Fin (m + 1) with x(0) = 0, and write L for the last mark. Let G > 0 be a natural number with every adjacent gap of x at most G. Assume CyclicPerfectDifference for x modulo L + G, so G is a largest cyclic gap and ties are allowed. Equal ordinary distances for i < j and k < l imply (i, j) = (k, l). The real cast of x belongs to its chamber. Every real y in that chamber whose last mark is at most L equals x pointwise after casting. The formula writes casts as type ascriptions and uses natural subtraction for x-distances.

Each positive residue below G occurs as a forward distance because a wrapped difference is at least G. Induction using the chamber inequalities bounds every retained gap below by its reference value. The markwise deviations are therefore nondecreasing, and the two endpoint conditions force them all to be zero.

Lean checks chamber uniqueness for every cyclic perfect difference set with a largest-gap cut. For any prime power m, the classical Singer construction supplies m + 1 marks modulo N = m² + m + 1 whose ordered differences cover each nonzero residue exactly once. Unit multiplication permutes the differences and translation preserves them. Translate the first mark after any largest gap G to zero and sort the representatives in [0, N). This gives the required increasing marks, with last mark N − G and all retained gaps at most G. This classical specialization proves Notik’s §7 conjecture. The Lean theorem assumes the perfect difference property and compares lengths within one chamber.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.Chamber`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.CyclicPerfectDifference`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result`
