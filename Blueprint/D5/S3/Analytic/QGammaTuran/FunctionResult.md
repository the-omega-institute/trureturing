# The function clause of Conjecture 1 is false

## Abstract

A convergent reciprocal q-gamma series whose function Turanian is negative.

**Theorem 1.1 (qprod multipliable).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; \operatorname{Multipliable} \left((j: \mathbb{N} ) \mapsto (1 - a \cdot (q)^{j})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_multipliable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Geometric summability makes the q-product multipliable.

**Theorem 1.2 (qprod step).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; \operatorname{Result.qprod} \left(q, a\right) = \left(1 - a\right) \cdot \operatorname{Result.qprod} \left(q, a \cdot q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Removing the first product factor shifts its parameter by q.

**Theorem 1.3 (qprod nonneg).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow (0 \le \operatorname{Result.qprod} \left(q, a\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Nonnegative product factors give a nonnegative infinite product.

**Theorem 1.4 (qprod ne zero).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; (0 \le a) \Rightarrow ((a < 1) \Rightarrow (\neg \operatorname{Result.qprod} \left(q, a\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Strictly positive factors and geometric convergence exclude a zero product.

**Theorem 1.5 (qprod pos).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; (0 \le a) \Rightarrow ((a < 1) \Rightarrow (0 < \operatorname{Result.qprod} \left(q, a\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The infinite product is positive for a in the half-open unit interval.

**Theorem 1.6 (qprod le one).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow (\operatorname{Result.qprod} \left(q, a\right) \le 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Products of factors in the unit interval are at most one.

**Theorem 1.7 (qprod lower).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow (1 - \frac{a}{1 - q} \le \operatorname{Result.qprod} \left(q, a\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The geometric sum bounds the loss of the product from one.

**Theorem 1.8 (qprod split).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; \forall n \in \mathbb{N} ,\; \operatorname{Result.qprod} \left(q, a\right) = \prod_{j\in \operatorname{Finset.range} \left(n\right)} (1 - a \cdot (q)^{j}) \cdot \operatorname{Result.qprod} \left(q, a \cdot (q)^{n}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

A finite prefix times the remaining infinite product equals the full product.

**Theorem 1.9 (qprod bounds).**

$$\forall q \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow (\forall a \in \mathbb{R} ,\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow (\forall n \in \mathbb{N} ,\; (\prod_{j\in \operatorname{Finset.range} \left(n\right)} (1 - a \cdot (q)^{j}) \cdot \left(1 - \frac{a \cdot (q)^{n}}{1 - q}\right) \le \operatorname{Result.qprod} \left(q, a\right)) \land (\operatorname{Result.qprod} \left(q, a\right) \le \prod_{j\in \operatorname{Finset.range} \left(n\right)} (1 - a \cdot (q)^{j}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

A finite prefix gives both bounds, using the geometric tail loss for the lower bound.

**Theorem 1.10 (rqgamma eq).**

$$\forall q \in \mathbb{R} ,\; (0 < q) \Rightarrow (\forall x \in \mathbb{R} ,\; \operatorname{Result.rqgamma} \left(q, x\right) = \frac{\operatorname{Result.qprod} \left(q, (q)^{x}\right)}{\operatorname{Result.qprod} \left(q, q\right) \cdot (1 - q)^{1 - x}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.rqgamma_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The reciprocal q-gamma definition in q-Pochhammer notation.

**Definition 1.11 (qseries).**

$$\forall q \in \mathbb{R} ,\; \forall mu \in \mathbb{R} ,\; \forall x \in \mathbb{R} ,\; \forall g \in \mathbb{N}  \to \mathbb{R} ,\; \operatorname{qseries} \left(q, mu, x, g\right) = \sum'_{n: \mathbb{N} } ((g)\left(n\right) \cdot (x)^{n} \cdot \operatorname{Result.rqgamma} \left(q, mu + n\right))$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.qseries` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Theorem 3, printed page 11 of arXiv:1702.03788v1: “For a real sequence {gₙ}ₙ≥₀ and fixed 0 < q < 1 define g(µ; x) = ∑ₙ₌₀∞ gₙxⁿ/Γq(µ + n). (16)” The reciprocal is the infinite-product rqgamma of Result. Equation (6), printed page 4: “The q-gamma function is defined by Γq(z) = (1 − q)^(1−z) (q; q)∞/(q^z; q)∞ (6) for |q| < 1 and all complex z such that q^(z+k) ≠ 1 for k ∈ N₀.” At nonpositive integers the reciprocal extension is zero.

**Definition 1.12 (radius).**

$$\forall q \in \mathbb{R} ,\; \forall mu \in \mathbb{R} ,\; \forall g \in \mathbb{N}  \to \mathbb{R} ,\; \operatorname{radius} \left(q, mu, g\right) = \operatorname{FormalMultilinearSeries.radius} \left(\operatorname{FormalMultilinearSeries.ofScalars} \left(\mathbb{R} , (n: \mathbb{N} ) \mapsto ((g)\left(n\right) \cdot \operatorname{Result.rqgamma} \left(q, mu + n\right))\right)\right)$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.radius` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Rg is the radius of series (16) at the given µ, with coefficients gₙ rqgamma(q,µ+n). It takes values in the extended nonnegative reals. The standard scalar formal power series has coefficient norms |gₙ rqgamma(q,µ+n)|. Its Mathlib radius is the supremum of nonnegative radii at which these norms times the corresponding powers are bounded; equivalently it is the supremum of radii of absolute summability. Printed page 12: “Writing Rg > 0 for the radius of convergence in (16), we claim that the next conjecture is true.”

**Definition 1.13 (claim).**

$$claim = \left(\forall q \in \mathbb{R} ,\; (0 < q) \Rightarrow ((q < 1) \Rightarrow (\forall g \in \mathbb{N}  \to \mathbb{R} ,\; (\operatorname{D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq} \left(g\right)) \Rightarrow (\forall mu \in \mathbb{R} ,\; \forall alpha \in \mathbb{R} ,\; \forall beta \in \mathbb{R} ,\; (0 < alpha) \Rightarrow ((0 < beta) \Rightarrow ((\operatorname{max} \left(-beta, -1\right) \le mu) \Rightarrow (\forall x \in \mathbb{R} ,\; (0 < x) \Rightarrow ((\operatorname{ENNReal.ofReal} \left(x\right) < \operatorname{radius} \left(q, mu, g\right)) \Rightarrow (0 < \operatorname{qseries} \left(q, mu + alpha, x, g\right) \cdot \operatorname{qseries} \left(q, mu + beta, x, g\right) - \operatorname{qseries} \left(q, mu, x, g\right) \cdot \operatorname{qseries} \left(q, mu + alpha + beta, x, g\right)))))))))\right)$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.claim` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Theorem 3, printed page 11: “Suppose {gₙ}∞ₙ₌₀ is doubly positive. Then (16) has a positive radius of convergence Rg and the generalized Turánian ∆g(α, β; x) = g(µ + α; x)g(µ + β; x) − g(µ; x)g(µ + α + β; x) is positive for 0 < x < Rg if α ∈ N, β > 0 and µ ≥ max(−β, −1). If, in addition, α ≤ β + 1, then ∆g(α, β; x) has positive power series coefficients at all powers of x.” Conjecture 1, printed page 12: “All conclusions of Theorem 3 are valid for all α > 0, while conditions on other parameters remain intact. In particular, µ → g(µ; x) is log-concave for each fixed 0 < x < Rg.” The function clause quantifies over 0<x<Rg, where radius(q,µ,g) is the radius of (16) at the given µ. It has no α≤β+1 restriction. AdmissibleSeq is the nontrivial, nonnegative, log-concave sequence condition with no internal zeros; admissible_one supplies gₙ=1.

**Definition 1.14 (hsum).**

$$\forall q \in \mathbb{R} ,\; \forall a \in \mathbb{R} ,\; \forall y \in \mathbb{R} ,\; \operatorname{hsum} \left(q, a, y\right) = \sum'_{n: \mathbb{N} } ((y)^{n} \cdot \operatorname{Result.qprod} \left(q, a \cdot (q)^{n}\right))$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.hsum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The normalized series is expressed with a=q^s and y=x(1−q). This form includes the pole at s=0 without division by a vanishing q-number.

**Definition 1.15 (plower).**

$$\forall q \in \mathbb{R} ,\; \forall a \in \mathbb{R} ,\; \forall N \in \mathbb{N} ,\; \operatorname{plower} \left(q, a, N\right) = \prod_{j\in \operatorname{Finset.range} \left(N\right)} (1 - a \cdot (q)^{j}) \cdot \left(1 - \frac{a \cdot (q)^{N}}{1 - q}\right)$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.plower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

A finite q-product multiplied by the lower bound on its remaining factors.

**Definition 1.16 (pupper).**

$$\forall q \in \mathbb{R} ,\; \forall a \in \mathbb{R} ,\; \forall N \in \mathbb{N} ,\; \operatorname{pupper} \left(q, a, N\right) = \prod_{j\in \operatorname{Finset.range} \left(N\right)} (1 - a \cdot (q)^{j})$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.pupper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The finite product bounds the full product from above.

**Theorem 1.17 (hsummable).**

$$\forall q \in \mathbb{R} ,\; \forall a \in \mathbb{R} ,\; \forall y \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow ((0 \le a) \Rightarrow ((a \le 1) \Rightarrow ((0 \le y) \Rightarrow ((y < 1) \Rightarrow (\operatorname{Summable} \left((n: \mathbb{N} ) \mapsto ((y)^{n} \cdot \operatorname{Result.qprod} \left(q, a \cdot (q)^{n}\right))\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.hsummable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

When a and y lie in the unit interval, normalized terms are nonnegative and bounded by yⁿ. The geometric series proves summability.

**Theorem 1.18 (hshift).**

$$\forall q \in \mathbb{R} ,\; \forall a \in \mathbb{R} ,\; \forall y \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow ((0 \le a) \Rightarrow ((a \cdot q \le 1) \Rightarrow ((0 \le y) \Rightarrow ((y < 1) \Rightarrow (\operatorname{hsum} \left(q, a, y\right) = \operatorname{Result.qprod} \left(q, a\right) + y \cdot \operatorname{hsum} \left(q, a \cdot q, y\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.hshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Separating the first term shifts a to aq. This identity also applies when a exceeds one but aq does not.

**Theorem 1.19 (hbounds).**

$$\forall q \in \mathbb{R} ,\; \forall a \in \mathbb{R} ,\; \forall y \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow ((0 \le a) \Rightarrow ((a \le 1) \Rightarrow ((0 \le y) \Rightarrow ((y < 1) \Rightarrow (\forall K \in \mathbb{N} ,\; \forall N \in \mathbb{N} ,\; (\sum_{n\in \operatorname{Finset.range} \left(K\right)} ((y)^{n} \cdot \operatorname{plower} \left(q, a \cdot (q)^{n}, N\right)) \le \operatorname{hsum} \left(q, a, y\right)) \land (\operatorname{hsum} \left(q, a, y\right) \le \sum_{n\in \operatorname{Finset.range} \left(K\right)} ((y)^{n} \cdot \operatorname{pupper} \left(q, a \cdot (q)^{n}, N\right)) + \frac{(y)^{K}}{1 - y})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.hbounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

qprod_bounds bounds each product in a finite prefix. Summable.sum_le_tsum supplies the lower bound; the omitted normalized terms are at most a geometric tail y^K/(1−y).

**Theorem 1.20 (normalizedTerm).**

$$\forall q \in \mathbb{R} ,\; (0 < q) \Rightarrow ((q < 1) \Rightarrow (\forall s \in \mathbb{R} ,\; \forall x \in \mathbb{R} ,\; \forall n \in \mathbb{N} ,\; (x)^{n} \cdot \operatorname{Result.rqgamma} \left(q, s + n\right) = \frac{(x \cdot \left(1 - q\right))^{n} \cdot \operatorname{Result.qprod} \left(q, (q)^{s} \cdot (q)^{n}\right)}{\operatorname{Result.qprod} \left(q, q\right) \cdot (1 - q)^{1 - s}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.normalizedTerm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

rqgamma_eq and the real power addition law normalize each term. The denominator is independent of n.

**Theorem 1.21 (series eq).**

$$\forall q \in \mathbb{R} ,\; (0 < q) \Rightarrow ((q < 1) \Rightarrow (\forall s \in \mathbb{R} ,\; \forall x \in \mathbb{R} ,\; \operatorname{qseries} \left(q, s, x, (n: \mathbb{N} ) \mapsto (1)\right) = \frac{\operatorname{hsum} \left(q, (q)^{s}, x \cdot \left(1 - q\right)\right)}{\operatorname{Result.qprod} \left(q, q\right) \cdot (1 - q)^{1 - s}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.series_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Taking the infinite sum gives the normalized expression for the constant-sequence q-gamma series.

**Theorem 1.22 (hsummable any).**

$$\forall q \in \mathbb{R} ,\; \forall a \in \mathbb{R} ,\; \forall y \in \mathbb{R} ,\; (0 \le q) \Rightarrow ((q < 1) \Rightarrow ((0 \le a) \Rightarrow ((a \cdot q \le 1) \Rightarrow ((0 \le y) \Rightarrow ((y < 1) \Rightarrow (\operatorname{Summable} \left((n: \mathbb{N} ) \mapsto ((y)^{n} \cdot \operatorname{Result.qprod} \left(q, a \cdot (q)^{n}\right))\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.hsummable_any` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The first term may have either sign. After removing it, aq≤1 permits geometric domination.

**Theorem 1.23 (series summable).**

$$\forall q \in \mathbb{R} ,\; (0 < q) \Rightarrow ((q < 1) \Rightarrow (\forall s \in \mathbb{R} ,\; \forall x \in \mathbb{R} ,\; ((q)^{s} \cdot q \le 1) \Rightarrow ((0 \le x \cdot \left(1 - q\right)) \Rightarrow ((x \cdot \left(1 - q\right) < 1) \Rightarrow (\operatorname{Summable} \left((n: \mathbb{N} ) \mapsto (((n: \mathbb{N} ) \mapsto (1))\left(n\right) \cdot (x)^{n} \cdot \operatorname{Result.rqgamma} \left(q, s + n\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.series_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The normalized geometric comparison proves summability of the original real q-gamma series, hence absolute summability. It applies to all four shifts at the example.

**Definition 1.24 (r).**

$$r = \frac{93}{100}$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.r` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The rational base.

**Definition 1.25 (q).**

$$q = (r)^{10}$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The q parameter.

**Definition 1.26 (y).**

$$y = r \cdot \left(1 - q\right)$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/FunctionResult.y` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The normalized series variable at x=r.

**Theorem 1.27 (qpos).**

$$0 < q$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qpos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The example has positive q.

**Theorem 1.28 (qlt).**

$$q < 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qlt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The example has q less than one.

**Theorem 1.29 (ypos).**

$$0 \le y$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.ypos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The normalized series variable is nonnegative.

**Theorem 1.30 (ylt).**

$$y < 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.ylt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The example lies strictly in the geometric convergence disk.

**Theorem 1.31 (numH3).**

$$(\frac{621758}{1000000} \le \operatorname{hsum} \left(q, (r)^{3}, y\right)) \land (\operatorname{hsum} \left(q, (r)^{3}, y\right) \le \frac{627611}{1000000})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.numH3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Ten series terms and six factors enclose the normalized value at s=3/10.

**Theorem 1.32 (numH6).**

$$(\frac{779999}{1000000} \le \operatorname{hsum} \left(q, (r)^{6}, y\right)) \land (\operatorname{hsum} \left(q, (r)^{6}, y\right) \le \frac{786930}{1000000})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.numH6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Ten series terms and six factors enclose the normalized value at s=6/10.

**Theorem 1.33 (numH10).**

$$(\frac{986336}{1000000} \le \operatorname{hsum} \left(q, (r)^{10}, y\right)) \land (\operatorname{hsum} \left(q, (r)^{10}, y\right) \le \frac{993832}{1000000})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.numH10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Ten series terms and six factors enclose the normalized value at s=1.

**Theorem 1.34 (numP3).**

$$(\frac{80786}{1000000} \le \operatorname{Result.qprod} \left(q, (r)^{3}\right)) \land (\operatorname{Result.qprod} \left(q, (r)^{3}\right) \le \frac{82438}{1000000})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.numP3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Six factors enclose the product with parameter r³.

**Theorem 1.35 (numP6).**

$$(\frac{177796}{1000000} \le \operatorname{Result.qprod} \left(q, (r)^{6}\right)) \land (\operatorname{Result.qprod} \left(q, (r)^{6}\right) \le \frac{180709}{1000000})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.numP6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Six factors enclose the product with parameter r⁶.

**Theorem 1.36 (qpower).**

$$\forall n \in \mathbb{N} ,\; (q)^{\frac{n}{10}} = (r)^{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.qpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The required fractional powers of q are rational powers of r.

**Theorem 1.37 (series product).**

$$\forall q \in \mathbb{R} ,\; (0 < q) \Rightarrow ((q < 1) \Rightarrow (\forall s \in \mathbb{R} ,\; \forall t \in \mathbb{R} ,\; \forall x \in \mathbb{R} ,\; \operatorname{qseries} \left(q, s, x, (n: \mathbb{N} ) \mapsto (1)\right) \cdot \operatorname{qseries} \left(q, t, x, (n: \mathbb{N} ) \mapsto (1)\right) = \frac{\operatorname{hsum} \left(q, (q)^{s}, x \cdot \left(1 - q\right)\right) \cdot \operatorname{hsum} \left(q, (q)^{t}, x \cdot \left(1 - q\right)\right)}{(\operatorname{Result.qprod} \left(q, q\right))^{2} \cdot (1 - q)^{2 - s - t}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.series_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Products with the same sum of shifts have the same positive normalization denominator.

**Theorem 1.38 (negative bounds).**

$$(0 \le \operatorname{hsum} \left(q, ((r)^{4})^{-1}, y\right)) \land ((\operatorname{hsum} \left(q, ((r)^{4})^{-1}, y\right) \le \frac{317763}{1000000}) \land ((\frac{243809}{1000000} \le \operatorname{hsum} \left(q, ((r)^{7})^{-1}, y\right)) \land ((\frac{0}{1000000} \le \operatorname{hsum} \left(q, 1, y\right)) \land (\operatorname{hsum} \left(q, 1, y\right) \le \frac{476937}{1000000}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.negative_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

The first-factor product equation and hshift transfer positive-parameter estimates to s=−2/5 and s=−7/10. At s=0 the product's zero makes hsum(q,1,y)=y hsum(q,q,y).

**Theorem 1.39 (witness negative).**

$$\operatorname{qseries} \left(q, \frac{-2}{5}, r, (n: \mathbb{N} ) \mapsto (1)\right) \cdot \operatorname{qseries} \left(q, 0, r, (n: \mathbb{N} ) \mapsto (1)\right) - \operatorname{qseries} \left(q, \frac{-7}{10}, r, (n: \mathbb{N} ) \mapsto (1)\right) \cdot \operatorname{qseries} \left(q, \frac{3}{10}, r, (n: \mathbb{N} ) \mapsto (1)\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.witness_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

At gₙ=1, q=(93/100)^10 and x=93/100, the product of normalized values at −2/5 and zero is at most 0.151552931931. The product at −7/10 and 3/10 is at least 0.151590196222. Their common normalization denominator is positive, so the original Turanian is strictly negative.

**Theorem 1.40 (witness radius).**

$$\operatorname{ENNReal.ofReal} \left(r\right) < \operatorname{radius} \left(q, \frac{-7}{10}, (n: \mathbb{N} ) \mapsto (1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.witness_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

At µ=−7/10 and gₙ=1, series_summable gives absolute convergence at x=3/2, since (3/2)(1−q)<1. FormalMultilinearSeries.le_radius_of_summable gives 3/2≤Rg. As 93/100<3/2, the negative Turanian occurs strictly inside the disk of convergence of (16).

**Theorem 1.41 (Refutation of the function clause).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/FunctionResult.result` (`✓ std3`). ∎

*Resolves.* `Problems/kalmykov-karp-2018-qgamma-turanian-function` (refuted) by `D5/S3/Analytic/QGammaTuran/FunctionResult.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kalmykov-karp-2018-qgamma-turanian-function","declaration_gid":"D5/S3/Analytic/QGammaTuran/FunctionResult.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Take gₙ=1, µ=−7/10, α=3/10, β=7/10, q=(93/100)^10 and x=93/100. The shifts satisfy µ=max(−β,−1), and witness_radius proves 0<x<Rg for the radius of (16) at µ. The strictly negative function value contradicts the universal strict positivity assertion. The proof reuses Result.qprod and Result.rqgamma (definitions), Defs.admissible_one, and JordanCototientRecordLimitInfinity.one_sub_prod_le_sum. Here Defs is D5.S3.Analytic.ReciprocalGammaTuran.Defs and JordanCototientRecordLimitInfinity is D5.S3.Factorization.JordanCototientRecordLimitInfinity. FunctionResult’s private helpers derive the product estimates and reciprocal-product identity from these declarations and pinned Mathlib. Consequence in prose of witness_negative: at this q,x and gₙ=1, log-concavity on an interval containing [−7/10,3/10] is impossible. Indeed, −2/5=(7/10)(−7/10)+(3/10)(3/10) and 0=(3/10)(−7/10)+(7/10)(3/10), with respective right-endpoint weights 3/10 and 7/10. Multiplying the two log-concavity inequalities would give g(−2/5;x)g(0;x) ≥ g(−7/10;x)g(3/10;x), contradicting the proved strict reverse inequality. The endpoint values are strictly positive by the normalized lower bounds and positive denominators. This consequence is not a separate Lean theorem. Log-concavity restricted to nonnegative parameters µ remains OPEN. The integer-shift theorem is outside the example’s parameter choice.

## References

- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.claim`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.hbounds`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.hshift`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.hsum`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.hsummable`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.hsummable_any`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.negative_bounds`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.normalizedTerm`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.numH10`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.numH3`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.numH6`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.numP3`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.numP6`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.plower`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.pupper`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.q`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qlt`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qpos`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qpower`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_bounds`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_le_one`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_lower`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_multipliable`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_ne_zero`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_nonneg`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_pos`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_split`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qprod_step`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.qseries`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.r`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.radius`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.result`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.rqgamma_eq`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.series_eq`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.series_product`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.series_summable`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.witness_negative`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.witness_radius`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.y`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.ylt`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/FunctionResult.ypos`
- Dependency: [D5/S3/Analytic/QGammaTuran/Result](Result.md)
