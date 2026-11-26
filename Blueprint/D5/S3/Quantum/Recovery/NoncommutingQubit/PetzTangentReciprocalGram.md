# Paired reciprocal Gram bounds for the Petz tangent

## Abstract

The normalized even and odd scalar reciprocal profiles obey a common node-dependent Gram bound.

**Theorem 1.1 (Combined reciprocal parity estimate).**

$$\begin{aligned}&\forall g,\beta,\delta\in\mathbb{R},a,b,c,d\in\mathbb{C}\\&0<g\land 0<\delta\le1\land g^{2}+\beta^{2}\le1\Rightarrow\\\left\lVert g(a+b)+\beta(c+d) \right\rVert^{2}&\le K(\delta)[\int_{0}^{\infty}\frac{\sqrt{1+t}\left\lVert \frac{a}{1+t}+\frac{b\delta}{\delta^{2}+t} \right\rVert^{2}}{2}\,\mathrm{d}t\\&\quad+\int_{0}^{\infty}\frac{\sqrt{1+t}\left\lVert \frac{c(g+1)}{1+t}+\frac{d\delta(g+\delta)}{\delta^{2}+t} \right\rVert^{2}}{2(g^{2}+t)}\,\mathrm{d}t]\\K(\delta)&=\begin{cases}1&\delta=1\\\max(2,\frac{3-\delta}{1+\delta})&\delta\neq1\end{cases}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficients are arbitrary complex numbers. For the arcsine functionals, the even coefficients are normalized by 1/x and the odd coefficients by 1/(x(x+g)), for nodes x in {1,δ}. Positivity of g and δ keeps the reciprocal nodes positive for the integral identities and makes both coefficient normalizations invertible. The physical range δ≤1 corresponds to taking the positive ratio of the smaller node to the larger one. In the proof this ordering bounds the cross-entry denominators and gives the square-root chord estimate. The disk condition g²+β²≤1 makes the final linear combination a contraction and gives g≤1 for comparison of the odd kernels.

The unweighted odd Gram splits into a common even lower Gram and a positive correction with unsquared reciprocal nodes. The cross entries are bounded below by δ in the weighted even and unweighted odd Grams. For real coefficients of the same sign, completing the square gives the rational factor in the displayed maximum. For coefficients of opposite signs, the common even lower Gram gives the factor two. The real estimates apply to the real and imaginary parts of each profile. At δ=1 the even diagonal equals one and the unweighted odd diagonal is at least one. The multiplier one is sharp there.

The physical entry theorem `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.physical_entry_arcsine_and_bound` uses this bound for a positive joint spectral pair and a faithful qubit marginal. It identifies the entry of the ordinary Petz residual with an arcsine average of the arithmetic BKM residual at the same reference and tangent. `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentTraceNorm.faithful_traceNorm_tangent` uses the resulting weighted sum to bound the squared full trace norm by the same multiplier times the conditional BKM form for a positive definite joint reference of trace one. The aggregate estimate at a singular reference, including the support and kernel cross terms, and the recovery bound with this multiplier in terms of finite Umegaki entropy loss remain open in this formalization.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.physical_entry_arcsine_and_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentTraceNorm.faithful_traceNorm_tangent`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](../../Divergence/UmegakiRareFlagBKM.md)
