# A self-conjugate grid with Schur ratio above one

## Abstract

A self-conjugate pair in the closed unit disk violates the shifted Schur-ratio bound in Conjecture 6.2 of Ostrovskii and Shcherbakov. The tableau definition gives the ratio 73/60 at t = 3, n = 2, k = 1.

**Definition 1.1 (Self-conjugate grids).**

$$\forall n: \mathbb{N}, \forall z: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \operatorname{selfConjugate}\left(z\right) \Leftrightarrow ((\forall i: \operatorname{Fin}\left(n\right), (\operatorname{Im}\left(z\left(i\right)\right) \ne 0) \Rightarrow (\exists j: \operatorname{Fin}\left(n\right), z\left(j\right) = \operatorname{conj}\left(z\left(i\right)\right))) \land (\forall x: \mathbb{R}, \operatorname{Even}\left(\operatorname{card}\left(\{i:\operatorname{Fin}\left(n\right) \mid z\left(i\right) = \operatorname{ofReal}\left(x\right)\}\right)\right)))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.selfConjugate` (`✓ std3`).

*Citation.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Definition 6.1, page 15: “A list $z_{1:n} \in \mathbb{C}^{n}$ is self-conjugate if (i) for any $z \in \left\{z_{1}, ..., z_{n}\right\}$ with $\operatorname{Im}\left(z\right) \ne 0$, the conjugate $\overline{z}$ is also contained in $\left\{z_{1}, ..., z_{n}\right\}$; (ii) $z_{1:n}$ contains even number of copies of each $z \in \mathbb{R}$.”

Entries are indexed by Fin n, starting at zero. The first condition requires membership of each nonreal conjugate; the second counts every real value, including absent values. ofReal is the embedding from R into C.

**Definition 1.2 (Elementary symmetric functions).**

$$\forall n: \mathbb{N}, \forall d: \mathbb{N}, \forall z: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \operatorname{e}\left(d, z\right) = \sum_{s\in \operatorname{powersetCard}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), d\right)} \prod_{i\in s} z\left(i\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.e` (`✓ std3`).

*Citation.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Equation (17), page 7, defines e_d as the sum of products over strictly increasing index tuples, with e_0 = 1. A tuple is represented by its d-element subset of Fin n. univ(Fin n) is the finite set of all indices, and powersetCard(U,d) consists of the d-element subsets of U.

**Definition 1.3 (Complete homogeneous symmetric functions).**

$$\forall n: \mathbb{N}, \forall d: \mathbb{N}, \forall z: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \operatorname{h}\left(d, z\right) = \sum_{s:\operatorname{Sym}\left(\operatorname{Fin}\left(n\right), d\right)} \operatorname{prod}\left(\operatorname{map}\left(z, \operatorname{val}\left(s\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.h` (`✓ std3`).

*Citation.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Equation (17), page 7, defines h_d as the sum of products over weakly increasing index tuples, with h_0 = 1. Sym(Fin n,d) is the type of multisets of cardinality d. Sorting in the ordered alphabet Fin n identifies each multiset with exactly one such tuple, including repeated indices. val extracts the multiset; map applies z to every occurrence; prod multiplies with multiplicity.

**Definition 1.4 (Hook Schur functions by tableaux).**

$$\forall n: \mathbb{N}, \forall a: \mathbb{N}, \forall b: \mathbb{N}, \forall z: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \operatorname{schurHook}\left(a, b, z\right) = \sum_{c:\operatorname{Fin}\left(n\right)} \sum_{A:\operatorname{Sym}\left(\operatorname{Fin}\left(n\right), a\right)} \sum_{L\in \operatorname{powersetCard}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), b\right)} \operatorname{ite}\left((\forall i: \operatorname{Fin}\left(n\right), (i \in \operatorname{val}\left(A\right)) \Rightarrow (c \le i)) \land (\forall j: \operatorname{Fin}\left(n\right), (j \in L) \Rightarrow (c < j)), z\left(c\right) \cdot \operatorname{prod}\left(\operatorname{map}\left(z, \operatorname{val}\left(A\right)\right)\right) \cdot \prod_{j\in L} z\left(j\right), 0\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.schurHook` (`✓ std3`).

*Citation.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Page 8: “A semi-standard Young tableau (SSYT) with shape $\lambda \in \operatorname{Par}$ is a two-dimensional array $T$ that fills the cells of the Young diagram of $\lambda$ with positive integers, such that the entries (a) srtictly increase in each column; (b) do not decrease in each row.”

Equation (19) defines the Schur function by its Kostka expansion. For the hook (a+1,1^b), c is the corner, A is the arm multiset of cardinality a, and L is the leg set of cardinality b. Sorting A gives the weakly increasing arm; sorting L gives the strictly increasing leg. All arm entries are at least c, and all leg entries exceed c. Fin n relabels the source entries 1,...,n by 0,...,n-1. Grouping tableau monomials by weights and then permuted weights recovers the Kostka expansion. Each tableau occurs once. ite(P,u,v) is u when P holds and v otherwise.

**Definition 1.5 (The alternating Schur ratio).**

$$\forall t: \mathbb{N}, \forall n: \mathbb{N}, \forall k: \mathbb{N}, \forall \zeta: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \operatorname{Q}\left(t, n, k, \zeta\right) = \sum_{d=0}^{t - n} (-1)^{d} \cdot \frac{\operatorname{Nat.cast}\left(\mathbb{C}, \operatorname{choose}\left(t, n + d\right)\right) \cdot \operatorname{schurHook}\left(d, n - k - 1, \zeta\right)}{\operatorname{Nat.cast}\left(\mathbb{C}, \operatorname{choose}\left(t, n\right)\right) \cdot \operatorname{e}\left(n - k, \zeta\right)}$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.Q` (`✓ std3`).

*Citation.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Page 13: “Let us define the rational multivariate function $Q_{t,n,k}:\mathbb{C}^{n} \to \mathbb{C}$, symmetric in its arguments, by” the displayed alternating sum.

The defining alternating sum is displayed with every parameter bound. choose(t,r) is the natural binomial coefficient. Nat.cast gives the typed natural-to-complex coercions. Natural subtraction is truncated at zero. Fractions here are complex field division; Lean assigns value zero to division by zero. The counterexample denominator is 3/5, so this convention has no effect on the refutation.

**Definition 1.6 (Both clauses of Conjecture 6.2).**

$$claim \Leftrightarrow (\forall k: \mathbb{N}, \forall n: \mathbb{N}, \forall t: \mathbb{N}, (k < n) \Rightarrow ((n \le t) \Rightarrow (\forall z: \operatorname{Fin}\left(n\right) \to \mathbb{C}, (\operatorname{selfConjugate}\left(z\right)) \Rightarrow ((\forall i: \operatorname{Fin}\left(n\right), \left\lVert z\left(i\right) \right\rVert \le 1) \Rightarrow ((\left\lVert \operatorname{Q}\left(t, n, k, (z + 1)\right) \right\rVert \le 1) \land ((\forall i: \operatorname{Fin}\left(n\right), 0 \le \operatorname{Re}\left(z\left(i\right)\right)) \Rightarrow (\left\lVert \operatorname{schurHook}\left(t - n, n - k - 1, z\right) \right\rVert \le \operatorname{Nat.cast}\left(\mathbb{R}, \operatorname{choose}\left(t, n\right)\right) \cdot \left\lVert \operatorname{e}\left(n - k, z\right) \right\rVert)))))))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.claim` (`✓ std3`).

*Citation.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Conjecture 6.2 (Equivalent to Conjecture 6.1), page 15: “For all $0 \le k < n \le t$ and self-conjugate $z_{1:n} \in \mathbb{D}^{n}$, $\left|\left(Q_{t,n,k}\right)\left(z_{1:n} + 1_{n}\right)\right| \le 1$. Moreover, if the grid additionally satisfies $\operatorname{Re}\left(z_{1:n}\right) \in \left(\mathbb{R}^{n}\right)_{+}$, then $\left|\left(s_{(t - n \mid n - k - 1)}\right)\left(z_{1:n}\right)\right| \le (\begin{aligned}t\\n\end{aligned}) \cdot \left|\left(e_{n - k}\right)\left(z_{1:n}\right)\right|$.”

Natural k encodes 0 <= k. The complex norm is the absolute value; the disk is closed; the nonnegative orthant includes zero. The pointwise numeral 1 is added to z. The implication for nonnegative real parts belongs to the second conjunct only. All natural subtractions are truncated, in the source range k < n <= t.

**Theorem 1.7 (Refutation by a conjugate pair).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ostrovskii-shcherbakov-conjecture-62-refutation` (refuted) by `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ostrovskii-shcherbakov-conjecture-62-refutation","declaration_gid":"D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Take z = (-9/10 + (2/5)i, -9/10 - (2/5)i). Each entry has squared norm 97/100; the entries are nonreal conjugates, so each real multiplicity is zero. For w = z plus the pointwise numeral 1 on Fin 2, the finite sums give e_1(w) = 1/5, schurHook(0,0,w) = 1/5 and schurHook(1,0,w) = -13/100. Hence Q(3,2,1,w) = 73/60, whose norm exceeds one. The first conjunct fails, refuting the whole universal conjunction.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.Q`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.e`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.h`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.result`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.schurHook`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.selfConjugate`
