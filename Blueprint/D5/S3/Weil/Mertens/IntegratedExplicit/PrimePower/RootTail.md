# Root substitution and the Costa Pereira remainder

## Abstract

Integrated Chebyshev tails at root cutoffs

Write C(r,x) for the centered integral of (psi(t^(1/r))-t^(1/r))/t² over t>x, scaled by the square root of x. Write J(r,x) for the corresponding uncentered integral. Q(y) is the complete Chebyshev tail, W(r,y) is the integral of s^(-r)Q(s) over s>y, and E(x) is Q(x)-Qtheta(x) minus the two unscaled uncentered integrals at r=2 and r=3.

**Theorem 1.1 (The signed centered integral at a root cutoff).**

$$\forall r \in \mathbb{R},\; \forall x \in \mathbb{R},\; 1 < r \Rightarrow \left(1 \le x \Rightarrow \operatorname{C}\left(r, x\right) = r \cdot \operatorname{sqrt}\left(x\right) \cdot \left(\operatorname{Q}\left(x^{\frac{1}{r}}\right) \cdot {x^{\frac{1}{r}}}^{1 - r} - \left(r - 1\right) \cdot \operatorname{W}\left(r, x^{\frac{1}{r}}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.centered_root_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitute t=s^r with y=x^(1/r). The centered integral becomes r times the integral of the Chebyshev error kernel against s^(1-r). The triangular product of the absolute integrable Chebyshev kernel and s^(-r) on y<s<t is integrable. Fubini and the power primitive on y<s<t give the boundary term Q(y)y^(1-r) and the subtracted weighted integral.

**Theorem 1.2 (The explicit uncentered power contribution).**

$$\forall r \in \mathbb{R},\; \forall x \in \mathbb{R},\; 1 < r \Rightarrow \left(0 < x \Rightarrow \operatorname{J}\left(r, x\right) = \frac{r}{r - 1} \cdot x^{\frac{1}{r} - \frac{1}{2}} + \operatorname{C}\left(r, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.root_tail_main` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Chebyshev linear bound gives integrability for the uncentered root kernel. Integrating the subtracted power gives r/(r-1) times x^(1/r-1/2) after normalization by the square root.

**Theorem 1.3 (The integrated fifth-root majorant).**

$$\forall x \in \mathbb{R},\; 1 \le x \Rightarrow \left(0 \le \operatorname{E}\left(x\right) \land \operatorname{sqrt}\left(x\right) \cdot \operatorname{E}\left(x\right) \le \left(\operatorname{log}\left(4\right) + 4\right) \cdot \frac{5}{4} \cdot x^{-\frac{3}{10}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.root_cutoff_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Costa Pereira inequalities in Mathlib retain the square and cube cutoffs in psi minus theta. The seventh-root term makes the remainder nonnegative. The uncentered fifth-root term is bounded by (log(4)+4)t^(1/5), which integrates against t^(-2) to (log(4)+4)(5/4)x^(-4/5) before normalization. The source inequality is reproduced in Broadbent et al., arXiv:2002.11068v2, equation (3.16).

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.centered_root_tail`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.root_cutoff_remainder`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.root_tail_main`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection](../PrimeOnlyTailCorrection.md)
