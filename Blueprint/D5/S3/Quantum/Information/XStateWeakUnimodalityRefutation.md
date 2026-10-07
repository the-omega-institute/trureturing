# The X-state conditional entropy f_1 need not be weakly unimodal

## Abstract

Yurischev (arXiv:1702.03728, Quantum Inf. Process. 16, 249) writes the conditional entropy of a two-qubit X state through the function f_1 of Eq. (A1) on [0, 1] and supposes that it is weakly unimodal for every choice of the parameters p_1, ..., p_5 with nonnegative Shannon arguments. It is not: for p = (-2466, -1107, 187, -163, 1138)/2500 one has f_1(0) > f_1(27/50) < f_1(177/200) > f_1(1).

**Definition 1.1 (Binary Shannon entropy).**

$$\forall a : \mathbb{R}, \forall b : \mathbb{R}, \operatorname{h2}\left(a, b\right) = \frac{\operatorname{shannonEntropy}\left((a, b)\right)}{\log 2}$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.h2` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

h_2(a, b) = -a log_2 a - b log_2 b: the existing shannonEntropy of the pair (a, b), the sum of Real.negMulLog t = -t log t over its entries, divided by log 2.

**Definition 1.2 (Quaternary Shannon entropy).**

$$\forall a : \mathbb{R}, \forall b : \mathbb{R}, \forall c : \mathbb{R}, \forall d : \mathbb{R}, \operatorname{h4}\left(a, b, c, d\right) = \frac{\operatorname{shannonEntropy}\left((a, b, c, d)\right)}{\log 2}$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.h4` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

h_4(a, b, c, d) = -a log_2 a - b log_2 b - c log_2 c - d log_2 d: the existing shannonEntropy of (a, b, c, d) divided by log 2.

**Definition 1.3 (The parameter w).**

$$\forall p_{3} : \mathbb{R}, \forall p_{4} : \mathbb{R}, \operatorname{wParam}\left(p_{3}, p_{4}\right) = \frac{|p_{3} + p_{4}| + |p_{3} - p_{4}|}{4}$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.wParam` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

w = (|p_3 + p_4| + |p_3 - p_4|)/4.

**Definition 1.4 (The quantity r_1).**

$$\forall x, p_{1}, p_{3}, p_{4}, p_{5} : \mathbb{R}, \operatorname{r1}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right) = (p_{1} + p_{5} \cdot x)^{2} + 4 \cdot \operatorname{wParam}\left(p_{3}, p_{4}\right)^{2} \cdot (1 - x^{2})$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.r1` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

r_1 = (p_1 + p_5 x)^2 + 4 w^2 (1 - x^2).

**Definition 1.5 (The quantity r_2).**

$$\forall x, p_{1}, p_{3}, p_{4}, p_{5} : \mathbb{R}, \operatorname{r2}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right) = (p_{1} - p_{5} \cdot x)^{2} + 4 \cdot \operatorname{wParam}\left(p_{3}, p_{4}\right)^{2} \cdot (1 - x^{2})$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.r2` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

r_2 = (p_1 - p_5 x)^2 + 4 w^2 (1 - x^2).

**Definition 1.6 (The function f_1).**

$$\forall x, p_{1}, p_{2}, p_{3}, p_{4}, p_{5} : \mathbb{R}, \operatorname{f1}\left(x, p_{1}, p_{2}, p_{3}, p_{4}, p_{5}\right) = -\operatorname{h2}\left(\frac{1 + p_{2} \cdot x}{2}, \frac{1 - p_{2} \cdot x}{2}\right) + \operatorname{h4}\left(\frac{1 + p_{2} \cdot x + \sqrt{\operatorname{r1}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right)}}{4}, \frac{1 + p_{2} \cdot x - \sqrt{\operatorname{r1}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right)}}{4}, \frac{1 - p_{2} \cdot x + \sqrt{\operatorname{r2}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right)}}{4}, \frac{1 - p_{2} \cdot x - \sqrt{\operatorname{r2}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right)}}{4}\right)$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.f1` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

Eq. (A1): f_1(x) = -h_2((1 + p_2 x)/2, (1 - p_2 x)/2) + h_4((1 + p_2 x + sqrt r_1)/4, (1 + p_2 x - sqrt r_1)/4, (1 - p_2 x + sqrt r_2)/4, (1 - p_2 x - sqrt r_2)/4) for x in [0, 1].

**Definition 1.7 (Nonnegative Shannon arguments).**

$$\forall x, p_{1}, p_{2}, p_{3}, p_{4}, p_{5} : \mathbb{R}, (\operatorname{ArgsNonneg}\left(x, p_{1}, p_{2}, p_{3}, p_{4}, p_{5}\right)) \Leftrightarrow ((((0 \le \frac{1 + p_{2} \cdot x}{2}) \land (0 \le \frac{1 - p_{2} \cdot x}{2})) \land ((0 \le \frac{1 + p_{2} \cdot x + \sqrt{\operatorname{r1}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right)}}{4}) \land (0 \le \frac{1 + p_{2} \cdot x - \sqrt{\operatorname{r1}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right)}}{4}))) \land ((0 \le \frac{1 - p_{2} \cdot x + \sqrt{\operatorname{r2}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right)}}{4}) \land (0 \le \frac{1 - p_{2} \cdot x - \sqrt{\operatorname{r2}\left(x, p_{1}, p_{3}, p_{4}, p_{5}\right)}}{4})))$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.ArgsNonneg` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

All six arguments of the Shannon functions in Eq. (A1) are nonnegative at x.

**Definition 1.8 (Weak unimodality).**

$$\forall f : \mathbb{R} \to \mathbb{R}, \forall a, b : \mathbb{R}, (\operatorname{WeaklyUnimodal}\left(f, a, b\right)) \Leftrightarrow (\exists x_{m} \in [a, b], ((\operatorname{MonotoneOn}\left(f, [a, x_{m}]\right)) \land (\operatorname{AntitoneOn}\left(f, [x_{m}, b]\right))) \lor ((\operatorname{AntitoneOn}\left(f, [a, x_{m}]\right)) \land (\operatorname{MonotoneOn}\left(f, [x_{m}, b]\right))))$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.WeaklyUnimodal` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

Appendix, definition of weak unimodality: f is weakly unimodal on [a, b] if for some x_m in [a, b] it is weakly increasing for x <= x_m and weakly decreasing for x >= x_m; the analogous definition for the minimum is weakly decreasing and then weakly increasing.

**Definition 1.9 (The unimodality hypothesis for f_1).**

$$(claim) \Leftrightarrow (\forall p_{1}, p_{2}, p_{3}, p_{4}, p_{5} : \mathbb{R}, (\forall x \in [0, 1], \operatorname{ArgsNonneg}\left(x, p_{1}, p_{2}, p_{3}, p_{4}, p_{5}\right)) \Rightarrow (\operatorname{WeaklyUnimodal}\left((x \mapsto \operatorname{f1}\left(x, p_{1}, p_{2}, p_{3}, p_{4}, p_{5}\right)), 0, 1\right)))$$

*Formalization.* `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.claim` (`✓ std3`).

*Citation.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

For all real p_1, ..., p_5 such that every Shannon argument of Eq. (A1) is nonnegative for every x in [0, 1], the function x -> f_1(x) is weakly unimodal on [0, 1], in the maximum form or in the minimum form.

**Theorem 1.10 (A non-unimodal conditional entropy).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/yurischev-2017-xstate-unimodality` (refuted) by `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yurischev-2017-xstate-unimodality","declaration_gid":"D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. A. Yurischev (2017). *Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states*. DOI: [10.1007/s11128-017-1701-0](https://doi.org/10.1007/s11128-017-1701-0). URL: <https://arxiv.org/abs/1702.03728v3>.

*Commentary.*

Take p = (-2466, -1107, 187, -163, 1138)/2500, so w = 187/5000. On [0, 1] the quadratic bounds (1 + p_2 x)^2 - r_1 >= 0 and (1 - p_2 x)^2 - r_2 >= 0, each a nonnegative combination of (1 - x)^2, x^2 and x (1 - x), make every Shannon argument nonnegative. At x = 0, 27/50, 177/200 and 1 the square roots are bracketed by rationals, every argument t lies in a rational interval [l, u] inside (0, 1], and l (-log u) <= -t log t <= u (-log l). Each log l and log u is bounded within 10^-8 by Real.abs_log_sub_add_sum_range_le after scaling by a power of 2 and by Real.log_two_near_10. This gives f_1 log 2 within 4 * 10^-8 of 0.033497172, 0.033489113, 0.033498565 and 0.033485902 at the four points, so f_1(0) > f_1(27/50) < f_1(177/200) > f_1(1). If f_1 were weakly increasing up to x_m and weakly decreasing after it, either 27/50 <= x_m contradicts f_1(0) > f_1(27/50), or x_m < 27/50 contradicts f_1(27/50) < f_1(177/200). In the minimum form, either 177/200 <= x_m contradicts f_1(27/50) < f_1(177/200), or x_m < 177/200 contradicts f_1(177/200) > f_1(1).

## References

- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.ArgsNonneg`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.WeaklyUnimodal`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.f1`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.h2`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.h4`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.r1`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.r2`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.wParam`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../Entropy/MaxEntropy.md)
