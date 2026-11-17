# The paired Laplace representation

## Abstract

A logarithmic forward response has a paired Laplace expansion with a holomorphic quadratic-growth remainder.

**Theorem 1.1 (Quadratic growth on the Gaussian strip).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_gaussian_growth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_gaussian_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quadratic bound for the Mellin remainder on closed substrips gives quadratic growth of the regular part between real parts minus one sixth and three quarters.

**Theorem 1.2 (Logarithmic coordinates recover the forward Mellin transform).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.laplace_forwardLog_eq_forwardMellin`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.laplace_forwardLog_eq_forwardMellin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a cutoff x0 at least three, the Laplace transform of the forward response written in logarithmic coordinates equals the forward Mellin transform starting at x0. The change of variables x=exp(y) preserves the complete response and handles the cutoff by an indicator.

**Theorem 1.3 (The regular part is holomorphic).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_holomorphic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_holomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the Mellin remainder is differentiable on the half-plane Re(s)>-1/5, then adding the elementary pole, logarithmic, and digamma terms produces a function differentiable on that same half-plane.

**Theorem 1.4 (Quadratic growth of the regular part).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_growth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quadratic vertical-strip bound for the Mellin remainder implies a quadratic bound for the regular part on |Re(s)|<=1/20. The digamma estimate, logarithm bound, and the elementary denominator are absorbed into one nonnegative constant.

**Definition 1.5 (The forward response supplies paired Laplace data).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardPairedLaplaceData`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardPairedLaplaceData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the Riemann hypothesis, a von Koch error bound, and the paired xi expansion, the logarithmic forward response is measurable, locally bounded, initially convergent, and has a holomorphic regular part with quadratic growth. In the strip 1/2<Re(s)<1 its Laplace transform equals minus one half of the paired zeta-zero pole sum plus that regular part.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardPairedLaplaceData`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_gaussian_growth`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_growth`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.forwardRegularPart_holomorphic`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PairedLaplace.laplace_forwardLog_eq_forwardMellin`
- Dependency: [D5/S3/Analytic/Oscillation/FejerDirichletTransfer](../../../Analytic/Oscillation/FejerDirichletTransfer.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Fubini](Fubini.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MellinPolynomialGrowth](MellinPolynomialGrowth.md)
- Dependency: [D5/S3/Weil/Mertens/Cryptids/DigammaBinet](../../../Weil/Mertens/Cryptids/DigammaBinet.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace](../../../Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.md)
- Dependency: [D5/S3/Weil/ZeroData/PairedXiExpansion](../../../Weil/ZeroData/PairedXiExpansion.md)
