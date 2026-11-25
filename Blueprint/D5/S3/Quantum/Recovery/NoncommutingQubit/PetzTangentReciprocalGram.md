# Paired reciprocal Gram bounds for the Petz tangent

## Abstract

The two parity sectors of the qubit tangent residual obey the common marginal-dependent reciprocal Gram bound.

**Theorem 1.1 (Combined reciprocal parity estimate).**

$$\begin{aligned}&\forall g,\beta,\delta\in\mathbb{R},a,b,c,d\in\mathbb{C}\\&0<g\land 0<\delta\le1\land g^{2}+\beta^{2}\le1\Rightarrow\\\left\lVert g(a+b)+\beta(c+d) \right\rVert^{2}&\le K(\delta)[\int_{0}^{\infty}\frac{\sqrt{1+t}\left\lVert \frac{a}{1+t}+\frac{b\delta}{\delta^{2}+t} \right\rVert^{2}}{2}\,\mathrm{d}t\\&\quad+\int_{0}^{\infty}\frac{\sqrt{1+t}\left\lVert \frac{c(g+1)}{1+t}+\frac{d\delta(g+\delta)}{\delta^{2}+t} \right\rVert^{2}}{2(g^{2}+t)}\,\mathrm{d}t]\\K(\delta)&=\begin{cases}1&\delta=1\\1+\frac{2}{1+\delta^{2}}&\delta\neq1\end{cases}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive g, 0<δ≤1, and real β satisfying g²+β²≤1, the displayed estimate holds for arbitrary complex coefficients. For the arcsine functionals, the even coefficients are normalized by 1/x and the odd coefficients by 1/(x(x+g)), for nodes x in {1,δ}. At δ=1, the multiplier equals the sharp uniform value one.

The unweighted odd Gram splits into a common even lower Gram and a positive correction with unsquared reciprocal nodes. The even estimate uses the square-root chord bound. At coincident nodes, the even diagonal equals one and the unweighted odd diagonal is at least one. Both sector estimates retain the two-node cross terms.

The physical common-reference tangent application requires the arcsine evaluations and substitution back to the affine spectral variable, followed by identification with the actual arithmetic BKM residual and ordinary Petz sandwich.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](../../Divergence/UmegakiRareFlagBKM.md)
