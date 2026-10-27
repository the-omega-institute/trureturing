# The largest root of the permaspin cubic

## Abstract

For positive real c and d, the supremum of the real roots of Dukes's cubic dominates c(1-d)^2 and c(1-d^2).

**Definition 1.1 (The cubic polynomial).**

$$\forall (c: \mathbb{R}), (\forall (d: \mathbb{R}), ((\operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.dukesCubic}\left(c, d\right): \operatorname{Polynomial}\left(\mathbb{R}\right)) = ((((\operatorname{Polynomial.C}\left((1: \mathbb{R})\right)) \cdot (((\operatorname{Polynomial.X}: \operatorname{Polynomial}\left(\mathbb{R}\right)))^{(3: \mathbb{N})})) + ((\operatorname{Polynomial.C}\left(-((((((c) \cdot ((d)^{(2: \mathbb{N})})) + ((c)^{(2: \mathbb{N})})) + ((((2: \mathbb{R})) \cdot (c)) \cdot (d))) + (c)) + ((1: \mathbb{R})))\right)) \cdot (((\operatorname{Polynomial.X}: \operatorname{Polynomial}\left(\mathbb{R}\right)))^{(2: \mathbb{N})}))) + ((\operatorname{Polynomial.C}\left(-(((c) \cdot (((((((((c) \cdot ((d)^{(3: \mathbb{N})})) + ((((3: \mathbb{R})) \cdot ((c)^{(2: \mathbb{N})})) \cdot (d))) + ((c) \cdot ((d)^{(2: \mathbb{N})}))) + ((c)^{(2: \mathbb{N})})) + ((c) \cdot (d))) + (c)) + (((3: \mathbb{R})) \cdot (d))) + ((1: \mathbb{R})))) \cdot ((d) - ((1: \mathbb{R}))))\right)) \cdot ((\operatorname{Polynomial.X}: \operatorname{Polynomial}\left(\mathbb{R}\right))))) + (\operatorname{Polynomial.C}\left(((((((d)^{(2: \mathbb{N})}) + (((4: \mathbb{R})) \cdot (d))) + ((1: \mathbb{R}))) \cdot ((c)^{(3: \mathbb{N})})) \cdot ((d) + ((1: \mathbb{R})))) \cdot (((d) - ((1: \mathbb{R})))^{(3: \mathbb{N})})\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.dukesCubic` (`✓ std3`).

*Citation.* Mark Dukes (2023). *An Ising model having permutation spin motivated by a permutation complexity measure*. DOI: [10.1016/j.physa.2023.129090](https://doi.org/10.1016/j.physa.2023.129090). URL: <https://arxiv.org/abs/2211.08908v3>.

*Commentary.*

The polynomial dukesCubic c d is Dukes's t with real coefficients. Polynomial.C embeds a real coefficient as a constant polynomial, and Polynomial.X is the indeterminate. The definition allows every real c and d. The polynomial is monic of degree three. In permaspin.tex, arXiv:2211.08908v3, lines 490-503 introduce c = a^4 and d = b^2 and the two explicit eigenvalues c(1-d)^2 and c(1-d^2); lines 504-509 give this cubic for the other three eigenvalues.

**Definition 1.2 (The supremum of the real roots).**

$$\forall (c: \mathbb{R}), (\forall (d: \mathbb{R}), ((\operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.largestRoot}\left(c, d\right): \mathbb{R}) = \operatorname{sSup}\left(\{(x: \mathbb{R}) \mid \operatorname{Polynomial.eval}\left(x, \operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.dukesCubic}\left(c, d\right)\right) = (0: \mathbb{R})\}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.largestRoot` (`✓ std3`).

*Citation.* Mark Dukes (2023). *An Ising model having permutation spin motivated by a permutation complexity measure*. DOI: [10.1016/j.physa.2023.129090](https://doi.org/10.1016/j.physa.2023.129090). URL: <https://arxiv.org/abs/2211.08908v3>.

*Commentary.*

The quantity largestRoot c d is the real supremum of the set of x for which dukesCubic c d evaluates to zero. It expresses the largest-root notion in permaspin.tex line 510 through the supremum operation. This is a total definition for all real parameters; nonemptiness and boundedness of the root set under positive parameters are included in the statement below.

**Definition 1.3 (The ordering for positive parameters).**

$$(\operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.claim}) \Leftrightarrow (\forall (c: \mathbb{R}), (\forall (d: \mathbb{R}), (((0: \mathbb{R}) < c) \to (((0: \mathbb{R}) < d) \to ((\operatorname{Set.Nonempty}\left(\{(x: \mathbb{R}) \mid \operatorname{Polynomial.eval}\left(x, \operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.dukesCubic}\left(c, d\right)\right) = (0: \mathbb{R})\}\right)) \land ((\operatorname{BddAbove}\left(\{(x: \mathbb{R}) \mid \operatorname{Polynomial.eval}\left(x, \operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.dukesCubic}\left(c, d\right)\right) = (0: \mathbb{R})\}\right)) \land (\operatorname{max}\left(\operatorname{max}\left(\operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.largestRoot}\left(c, d\right), (c) \cdot ((((1: \mathbb{R})) - (d))^{(2: \mathbb{N})})\right), (c) \cdot (((1: \mathbb{R})) - ((d)^{(2: \mathbb{N})}))\right) = \operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.largestRoot}\left(c, d\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mark Dukes (2023). *An Ising model having permutation spin motivated by a permutation complexity measure*. DOI: [10.1016/j.physa.2023.129090](https://doi.org/10.1016/j.physa.2023.129090). URL: <https://arxiv.org/abs/2211.08908v3>.

*Commentary.*

For every pair of positive real numbers c and d, the cubic has a real root, its real roots are bounded above, and the maximum of their supremum with c(1-d)^2 and c(1-d^2) is that supremum. The nesting of the two maxima is part of the statement. This is the ordering suggested by the numerical observations in permaspin.tex lines 510-513 and used as a hypothesis in line 517. The statement concerns the displayed cubic and the two explicit expressions; it does not assert the transfer-matrix calculation or the subsequent free-energy formula.

**Theorem 1.4 (A real root above both explicit expressions).**

$$\operatorname{D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.result` (`✓ std3`). ∎

*Resolves.* `Problems/dukes-2023-permaspin-eigenvalue-order` (proved) by `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dukes-2023-permaspin-eigenvalue-order","declaration_gid":"D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mark Dukes (2023). *An Ising model having permutation spin motivated by a permutation complexity measure*. DOI: [10.1016/j.physa.2023.129090](https://doi.org/10.1016/j.physa.2023.129090). URL: <https://arxiv.org/abs/2211.08908v3>.

*Commentary.*

Let c and d be positive real numbers, write t for dukesCubic c d, and put q = c(1+d)^2. The cubic has degree three and leading coefficient one. Expanding at q and collecting terms gives t(q) = -4c^2d^2(d+1)((d+1)(c-1)^2 + 4cd). The inner sum is positive: its first term is nonnegative and 4cd is positive. The remaining factors 4, c^2, d^2 and d+1 are positive, so t(q) < 0.

The evaluation of t is continuous, and its positive leading coefficient and positive degree imply that t(x) tends to positive infinity as x tends to positive infinity. The intermediate value theorem on the interval above q, together with t(q) < 0, therefore gives a real r with q < r and t(r) = 0. Since t has positive degree, it is nonzero. Its real roots form a finite set and hence are bounded above.

Choose this r. Boundedness of the real root set and membership of r imply r ≤ largestRoot c d by the defining upper-bound property of the supremum. Next, q - c(1-d)^2 = 4cd > 0 and q - c(1-d^2) = 2cd(d+1) > 0. Thus each explicit expression is strictly below q, which is strictly below r, and r is at most largestRoot c d. The root r establishes nonemptiness, and the preceding bound establishes boundedness. Finally, c(1-d)^2 ≤ largestRoot c d reduces the inner maximum to largestRoot c d, and c(1-d^2) ≤ largestRoot c d reduces the outer maximum to the same value.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.dukesCubic`
- Truth anchor: `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.largestRoot`
- Truth anchor: `D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.result`
