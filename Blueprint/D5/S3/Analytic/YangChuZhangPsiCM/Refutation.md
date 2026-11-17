# Yang–Chu–Zhang Conjecture 1(ii)

## Abstract

A positive second derivative of G at x = 1/64 refutes the complete-monotonicity classification of -G.

**Definition 1.1 (Shifted digamma remainder).**

$$\forall x: Real, R\left(x\right) = \operatorname{Complex}.\operatorname{re}\left(\operatorname{Complex}.\operatorname{digamma}\left(val\left(x + \frac{1}{2}, Complex\right)\right)\right) - \operatorname{Real}.\operatorname{log}\left(x\right)$$

*Formalization.* `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.R` (`✓ std3`).

*Citation.* Zhen-Hang Yang, Yu-Ming Chu and Xiao-Hui Zhang (2015). *Necessary and sufficient conditions for functions involving the psi function to be completely monotonic*. DOI: [10.1186/s13660-015-0674-8](https://doi.org/10.1186/s13660-015-0674-8). URL: <https://arxiv.org/abs/1409.6411v1>.

*Commentary.*

Equation (1.10): R(x) = ψ(x + 1/2) − ln x. The argument x is real; the source uses x > 0. Equation (1.2), p. 1, defines ψ(x) = Γ′(x)/Γ(x) on positive real arguments. Here ψ is expressed through Complex.digamma and its real part; val(x, Complex) denotes the real-to-complex coercion.

**Definition 1.2 (The source polynomial family).**

$$\forall a: Real, \forall x: Real, G\left(a, x\right) = 24 \cdot (x^{4} + a \cdot x^{2} + \frac{7}{40} \cdot a - \frac{31}{336}) \cdot R\left(x\right) - (x^{2} - \frac{7}{40} + a)$$

*Formalization.* `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.G` (`✓ std3`).

*Citation.* Zhen-Hang Yang, Yu-Ming Chu and Xiao-Hui Zhang (2015). *Necessary and sufficient conditions for functions involving the psi function to be completely monotonic*. DOI: [10.1186/s13660-015-0674-8](https://doi.org/10.1186/s13660-015-0674-8). URL: <https://arxiv.org/abs/1409.6411v1>.

*Commentary.*

Theorem 4, equation (3.3), defines Gₐ(x) = 24(x⁴ + ax² + (7/40)a − 31/336)R(x) − (x² − 7/40 + a). The real parameter a is unrestricted.

**Definition 1.3 (The source equivalence).**

$$claim = (\forall a: Real, \operatorname{D5}.\operatorname{S3}.\operatorname{Analytic}.\operatorname{ExpRatioCM}.\operatorname{Defs}.\operatorname{CompletelyMonotoneOn}\left((\operatorname{fun} (x: Real) \mapsto -G\left(a, x\right))\right) \Leftrightarrow a \le \frac{155}{294})$$

*Formalization.* `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.claim` (`✓ std3`).

*Citation.* Zhen-Hang Yang, Yu-Ming Chu and Xiao-Hui Zhang (2015). *Necessary and sufficient conditions for functions involving the psi function to be completely monotonic*. DOI: [10.1186/s13660-015-0674-8](https://doi.org/10.1186/s13660-015-0674-8). URL: <https://arxiv.org/abs/1409.6411v1>.

*Commentary.*

Conjecture 1, p. 15: “Let R(x) be defined on (0, ∞) by (1.10). Then we conjecture that” “(ii) the function −Gₐ is completely monotone on (0, ∞) if and only if a ≤ 155/294.” The existing CompletelyMonotoneOn predicate means ContDiffOn Real ⊤ on Set.Ioi 0 together with nonnegative signed iterated derivatives for every natural order, including zero, at every positive real point. All real a are quantified, and both directions of the equivalence are retained.

**Theorem 1.4 (Failure of the sufficient direction).**

$$\neg (\forall a: Real, \operatorname{D5}.\operatorname{S3}.\operatorname{Analytic}.\operatorname{ExpRatioCM}.\operatorname{Defs}.\operatorname{CompletelyMonotoneOn}\left((\operatorname{fun} (x: Real) \mapsto -G\left(a, x\right))\right) \Leftrightarrow a \le \frac{155}{294})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ycz2015-psicm` (refuted) by `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ycz2015-psicm","declaration_gid":"D5/S3/Analytic/YangChuZhangPsiCM/Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zhen-Hang Yang, Yu-Ming Chu and Xiao-Hui Zhang (2015). *Necessary and sufficient conditions for functions involving the psi function to be completely monotonic*. DOI: [10.1186/s13660-015-0674-8](https://doi.org/10.1186/s13660-015-0674-8). URL: <https://arxiv.org/abs/1409.6411v1>.

*Commentary.*

At a = 155/294 − 1/10000 = 774853/1470000 and x = 1/64, the second derivative of G is greater than 1/2. Thus the second derivative of −G is negative although a < 155/294. The estimate uses the digamma derivative series, a reciprocal-cube tail bounded by a telescoping sum, and exact rational inequalities. The bound on the second derivative holds for every a ≥ 774853/1470000.

## References

- Truth anchor: `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.G`
- Truth anchor: `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.R`
- Truth anchor: `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.claim`
- Truth anchor: `D5/S3/Analytic/YangChuZhangPsiCM/Refutation.result`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Defs](../ExpRatioCM/Defs.md)
- Dependency: [D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder](../SeriesInequalities/GurlandLogRemainder.md)
