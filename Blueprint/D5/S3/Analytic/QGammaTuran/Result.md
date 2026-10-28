# The coefficient clause of Conjecture 1 is false

## Abstract

A negative Cauchy coefficient for a reciprocal q-gamma series.

**Definition 1.1 (The q-Pochhammer infinite product).**

$$\forall q \in \mathbb{R} ,\; \forall a \in \mathbb{R} ,\; \operatorname{qprod} \left(q, a\right) = \prod'_{j: \mathbb{N}} (1 - a \cdot (q)^{j})$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/Result.qprod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product with parameter a has factors 1−aqʲ. It supplies the normalized series in FunctionResult.

**Definition 1.2 (Reciprocal q-gamma by its infinite product).**

$$\forall q \in \mathbb{R},\; \forall x \in \mathbb{R},\; \operatorname{rqgamma}\left(q, x\right) = \frac{\prod'_{j: \mathbb{N}} (1 - (q)^{x + j})}{\prod'_{j: \mathbb{N}} (1 - (q)^{j + 1}) \cdot (1 - q)^{1 - x}}$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/Result.rqgamma` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Equation (6), page 4 of arXiv:1702.03788v1: “The q-gamma function is defined by Γq(z) = (1 − q)^(1−z) (q; q)∞/(q^z; q)∞ (6) for |q| < 1 and all complex z such that q^(z+k) ≠ 1 for k ∈ N₀.” The preceding definition is “(a; q)∞ = lim n→∞ (a; q)n”, with (a; q)n the product of 1−aq^k for k from zero to n−1. For real 0<q<1 the numerator in rqgamma is (q^x;q)∞ and its denominator is (q;q)∞ times (1−q)^(1−x). Thus rqgamma is the reciprocal of equation (6) wherever Γq is finite. For 0<q<1 the denominator is nonzero. The numerator vanishes exactly when x is a nonpositive integer: a factor is zero precisely when x+j=0 for some natural j. This gives the reciprocal extension by zero used for the series coefficients.

**Definition 1.3 (The exact Cauchy coefficient).**

$$\forall q \in \mathbb{R},\; \forall g \in \mathbb{N} \to \mathbb{R},\; \forall mu \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall m \in \mathbb{N},\; \operatorname{qturanCoeff}\left(q, g, mu, alpha, beta, m\right) = \sum_{k\in \operatorname{Finset.range}\left(m + 1\right)} g\left(k\right) \cdot g\left(m - k\right) \cdot (\operatorname{rqgamma}\left(q, k + mu + alpha\right) \cdot \operatorname{rqgamma}\left(q, m - k + mu + beta\right) - \operatorname{rqgamma}\left(q, k + mu\right) \cdot \operatorname{rqgamma}\left(q, m - k + mu + alpha + beta\right))$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/Result.qturanCoeff` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Theorem 3 uses g(µ;x)=∑ₙ₌₀∞ gₙxⁿ/Γq(µ+n) and ∆g(α,β;x)=g(µ+α;x)g(µ+β;x)−g(µ;x)g(µ+α+β;x). The coefficient of x^m in these two Cauchy products is exactly qturanCoeff: k runs from zero to m and the second index is m−k. The subtraction order is unchanged.

**Definition 1.4 (The coefficient assertion for positive real shifts).**

$$claim = \left(\forall q \in \mathbb{R},\; (0 < q) \Rightarrow ((q < 1) \Rightarrow (\forall g \in \mathbb{N} \to \mathbb{R},\; (\operatorname{D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq}\left(g\right)) \Rightarrow (\forall mu \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; (0 < alpha) \Rightarrow ((0 < beta) \Rightarrow ((\operatorname{max}\left(-beta, -1\right) \le mu) \Rightarrow ((alpha \le beta + 1) \Rightarrow (\forall m \in \mathbb{N},\; 0 < \operatorname{qturanCoeff}\left(q, g, mu, alpha, beta, m\right))))))))\right)$$

*Formalization.* `D5/S3/Analytic/QGammaTuran/Result.claim` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Theorem 3, page 11 of arXiv:1702.03788v1: “For a real sequence {gₙ}ₙ≥₀ and fixed 0 < q < 1 define g(µ; x) = ∑ₙ₌₀∞ gₙxⁿ/Γq(µ + n). (16) Suppose {gₙ}∞ₙ₌₀ is doubly positive. Then (16) has a positive radius of convergence Rg and the generalized Turánian ∆g(α, β; x) = g(µ + α; x)g(µ + β; x) − g(µ; x)g(µ + α + β; x) is positive for 0 < x < Rg if α ∈ N, β > 0 and µ ≥ max(−β, −1). If, in addition, α ≤ β + 1, then ∆g(α, β; x) has positive power series coefficients at all powers of x.”

Conjecture 1, page 12: “All conclusions of Theorem 3 are valid for all α > 0, while conditions on other parameters remain intact. In particular, µ → g(µ; x) is log-concave for each fixed 0 < x < Rg.” The claim retains α≤β+1 and asks only for the coefficient conclusion. A counterexample with that restriction refutes the coefficient conclusion under either reading of the preceding discussion about removing restrictions.

The definition on page 3 states: “A sequence f : N₀ → R₊ is PF₂ (Pólya frequency sub two) or doubly positive if it is nontrivial, log-concave, fₖ² ≥ fₖ₋₁fₖ₊₁, k ∈ N, and has no internal zeros. The last claim means that fN = 0 implies either fN+i = 0 for all i ∈ N₀ or fN−i = 0 for i = 0, . . . , N.” These are exactly the nontriviality, nonnegativity, log-concavity and no-internal-zeros conditions of the reused D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq. Its frozen theorem admissible_one supplies the constant sequence gₙ=1.

**Theorem 1.5 (A negative coefficient of degree two).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/QGammaTuran/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/kalmykov-karp-2018-qgamma-turanian-coefficients` (refuted) by `D5/S3/Analytic/QGammaTuran/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kalmykov-karp-2018-qgamma-turanian-coefficients","declaration_gid":"D5/S3/Analytic/QGammaTuran/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2018). *Inequalities for series in q-shifted factorials and q-gamma functions*. DOI: [10.1016/j.jmaa.2017.11.041](https://doi.org/10.1016/j.jmaa.2017.11.041). URL: <https://arxiv.org/abs/1702.03788>.

*Commentary.*

Take gₙ=1, r=99/100, q=r^10, µ=−7/10 and α=β=7/10, and take m=2. All parameter inequalities in claim hold. The product recurrence gives rqgamma(q,x)=[x]q rqgamma(q,x+1), where [x]q=(1−q^x)/(1−q); in particular rqgamma(q,0)=0 and rqgamma(q,1)=rqgamma(q,2)=1.

The coefficient is 1−P C, with P=rqgamma(q,3/10)rqgamma(q,7/10) and C=[−7/10]q/([7/10]q[17/10]q)+1/[7/10]q+1/[3/10]q. The identities q^(3/10)=r^3 and q^(7/10)=r^7 reduce the required comparisons to rational powers of r. Finite partial products give upper bounds on each infinite product; multiplying a partial product by 1−a q^N/(1−q) gives a lower bound for (a;q)∞. With N=58 and outward rational enclosures at denominator 10^20, the lower bounds for (r^3;q)∞ and (r^7;q)∞ are respectively 4119/100000000000 and 23803/100000000000, while (q;q)∞ is at most 63655/100000000000. The rational q-number expression C exceeds 397/100. These bounds imply P C>1, so the degree-two coefficient is negative.

The conclusion concerns the coefficient clause. The function-positivity and parameter-log-concavity conclusions are not asserted here. The integer-shift theorem is unaffected because α=7/10 is not an integer.

## References

- Truth anchor: `D5/S3/Analytic/QGammaTuran/Result.claim`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/Result.qprod`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/Result.qturanCoeff`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/Result.result`
- Truth anchor: `D5/S3/Analytic/QGammaTuran/Result.rqgamma`
- Dependency: [D5/S3/Analytic/ReciprocalGammaTuran/Defs](../ReciprocalGammaTuran/Defs.md)
- Dependency: [D5/S3/Factorization/JordanCototientRecordLimitInfinity](../../Factorization/JordanCototientRecordLimitInfinity.md)
