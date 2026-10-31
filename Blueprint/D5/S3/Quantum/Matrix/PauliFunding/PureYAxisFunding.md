# All-order funding for a pure-Y source

## Abstract

Every positive-order funding coefficient is nonnegative for an actual pure-Y Pauli source, with exact strict and degenerate cases.

Let C=(0,y,0) with y squared equal to one and let D=(X,Y,Z) be any real unit Bloch vector. These are the Bloch coordinates of complex pure qubit sources; the imaginary Pauli coordinate is retained. The section-20 parameters reduce to kappa=0, lambda=0 and mu=-yY. Thus the actual control blocks are H plus or minus=(I+aZ plus or minus mu sqrt(1-a squared) X)/4. In the notation below t=mu sqrt(1-a squared). Their real entries are embedded into complex matrices before taking shifted inverses and the positive square root. The function complexMoment is the real part of the trace of the j-th power of sqrt(P minus) P plus sqrt(P minus).

**Definition 1.1 (The matrix integral coefficient).**

$$\forall a \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall j \in \mathbb{N},\; \operatorname{resolventCoefficient}\left(a, t, j\right) = \frac{1}{j} \cdot \int_{0 < s} \operatorname{complexMoment}\left(a, t, j, s\right) \mathrm{d} s$$

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding.resolventCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real a,t and natural j, resolventCoefficient is defined using Lebesgue integration on s>0. In the physical domain the shifted inverses exist, the filters are positive semidefinite, and the integrability asserted below makes this the finite section-20 resolvent integral.

**Definition 1.2 (The actual local funding coefficient).**

$$\begin{aligned}\forall j \in \mathbb{N},\; \operatorname{zeroArgumentSeries}\left(j\right) = \sum^{'}_{n:\mathbb{N}} \begin{cases}\frac{\operatorname{choose}\left(n, j\right) \cdot 0^{2 \cdot \left(n - j\right)}}{2 \cdot n \cdot \left(2 \cdot n - 1\right)}&j \le n\\0&n < j\end{cases}\\\operatorname{zeroArgumentSeries}\left(0\right) = 0\\\forall a \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall j \in \mathbb{N},\; \operatorname{fundingCoefficient}\left(a, t, j\right) = \operatorname{resolventCoefficient}\left(a, t, j\right) + \left(1 - a^{2 \cdot j}\right) \cdot \operatorname{zeroArgumentSeries}\left(j\right) - \operatorname{zeroArgumentSeries}\left(j\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding.fundingCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed zeroArgumentSeries is the private Lean series expanded exactly: n and j are natural, n-j is truncated natural subtraction, and the binomial coefficient and denominator are cast to real numbers. Real division is total, with division by zero equal to zero; in particular zeroArgumentSeries(0)=0. For j at least one its value is 1/[2j(2j-1)]. For a pure-Y first factor, z=x=0 and y squared equals one. The scalar terms are L=(1-a^(2j))zeroArgumentSeries(j) and m=zeroArgumentSeries(j). The definition retains this series at every natural order.

**Theorem 1.3 (Nonnegativity, strictness and every equality case).**

$$\forall a \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall X \in \mathbb{R},\; \forall Y \in \mathbb{R},\; \forall Z \in \mathbb{R},\; \forall j \in \mathbb{N},\; (((0 \le a) \land (a \le 1)) \land ((y^{2} = 1) \land ((X^{2} + Y^{2} + Z^{2} = 1) \land (1 \le j)))) \Rightarrow ((\operatorname{IntegrableOn}\left(\lambda s:\mathbb{R}\mapsto\operatorname{complexMoment}\left(a, \left(0 - y\right) \cdot Y \cdot \operatorname{sqrt}\left(1 - a^{2}\right), j, s\right), \operatorname{Ioi}\left(0\right)\right)) \land ((0 \le \operatorname{fundingCoefficient}\left(a, \left(0 - y\right) \cdot Y \cdot \operatorname{sqrt}\left(1 - a^{2}\right), j\right)) \land (((0 < \operatorname{fundingCoefficient}\left(a, \left(0 - y\right) \cdot Y \cdot \operatorname{sqrt}\left(1 - a^{2}\right), j\right)) \Leftrightarrow ((a < 1) \land (\operatorname{abs}\left(Y\right) < 1))) \land ((\operatorname{fundingCoefficient}\left(a, \left(0 - y\right) \cdot Y \cdot \operatorname{sqrt}\left(1 - a^{2}\right), j\right) = 0) \Leftrightarrow ((a = 1) \lor (\operatorname{abs}\left(Y\right) = 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding.pure_y_axis_funding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a in [0,1], y squared equal to one, real unit partner (X,Y,Z), and natural j at least one, the actual complex matrix moment is integrable and fundingCoefficient is nonnegative. It is strictly positive exactly when a<1 and abs(Y)<1, and is zero exactly when a=1 or abs(Y)=1. The quantifier includes every finite positive order, a=0, singular unshifted blocks, and both partner-axis endpoints. Applying the same result after exchanging the two source labels gives the corresponding local coefficients for a pure-Y second factor.

The parity-conjugate resolvent identities give the exact even power sum of two real quadratic roots. Evaluating their characteristic polynomial at a/(1+2s) gives the pointwise lower comparison, strict when the block determinant is positive. Evaluation at 1/(1+2s) bounds both root magnitudes and dominates the full trace by 2/(1+2s)^(2j). The existing shifted inverse-power integral proves integrability and gives the reference integral 1/[2(2j-1)]. Strict positivity of the difference on s>0 gives a strictly positive integral. When the determinant vanishes, the moment equals the reference pointwise and direct integration gives d=0. For the actual source the determinant numerator is (1-a squared)(1-Y squared), so these are exactly the stated strict and equality alternatives.

This comparison concerns the complete pure-Y family of local funding coefficients. It asserts no coefficient sign for a general first source, no full funding inequality, and no sign for the original pure-product deficit.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding.fundingCoefficient`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding.pure_y_axis_funding`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding.resolventCoefficient`
- Dependency: [D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent](PureYAxisResolvent.md)
- Dependency: [D5/S3/Quantum/Subentropy/UniformIntegrals](../../Subentropy/UniformIntegrals.md)
