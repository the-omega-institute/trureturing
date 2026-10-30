# ProductMarginQubitOrder

## Abstract

The distinct pure-factor boundary

**Theorem 1.1 (The closed-disk common-trace bound).**

$$\forall xC,zC,xD,zD:\mathbb{R},\ {0\le xC\land xC< 1\land 0\le xD\land xD< 1\land (xC^{2})+(zC^{2})\le 1\land (xD^{2})+(zD^{2})\le 1}\implies \forall K:\operatorname{Matrix}(\operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2)), \operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2)), \mathbb{C}),\ {\operatorname{PosSemidef}(K)\land K\le \operatorname{kron}(\operatorname{qubitMatrix}(xC, zC), \operatorname{qubitMatrix}(xD, zD))\land K\le \operatorname{kron}(\operatorname{qubitMatrix}(xC, -zC), \operatorname{qubitMatrix}(xD, -zD))}\implies \operatorname{re}(\operatorname{trace}(K))\le \frac{(1)-(\sqrt{(\frac{zC^{2}}{(1)-(xC^{2})})\times (\frac{zD^{2}}{(1)-(xD^{2})})})}{(1)+(\sqrt{(\frac{zC^{2}}{(1)-(xC^{2})})\times (\frac{zD^{2}}{(1)-(xD^{2})})})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For independent local closed-disk coordinates with nonnegative x less than one, every complex PSD common lower matrix K of the two actual product margins has trace at most (1-s)/(1+s), where s is the square root of the product of the two reliabilities z squared divided by one minus x squared. The proof constructs an explicit identity split and evaluates its quadratic energy. A zero denominator forces a pure local factor, handled by the annihilating split below. Neither K nor the individual product margins are required to be invertible, and K need not commute with them. The exceptional x=1 factors require the separate product-state entropy argument.

**Theorem 1.2 (The distinct pure-factor boundary).**

$$\forall u:\operatorname{Level}(),\ \forall n:\operatorname{Type}(u),\ {\operatorname{Fintype}(n)\land \operatorname{DecidableEq}(n)}\implies \forall x,z:\mathbb{R},\ {0\le x\land x< 1\land (x^{2})+(z^{2})=1}\implies \forall R,S:\operatorname{Matrix}(n, n, \mathbb{C}),\ \forall K:\operatorname{Matrix}(\operatorname{Prod}(\operatorname{Fin}(2), n), \operatorname{Prod}(\operatorname{Fin}(2), n), \mathbb{C}),\ {\operatorname{PosSemidef}(K)\land K\le \operatorname{kron}(\operatorname{qubitMatrix}(x, z), R)\land K\le \operatorname{kron}(\operatorname{qubitMatrix}(x, -z), S)}\implies K=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_zero_of_pure_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For x nonnegative and less than one and x squared plus z squared equal to one, every PSD common lower matrix of the two stated tensor margins is zero. The other local matrices are arbitrary. An explicit complex split U+V=I annihilates the respective pure local margins. The split-energy bound then gives K at most zero, while positivity gives the reverse inequality. The argument does not invert K and imposes no commutation or real-entry restriction on it.

## References

- Truth anchor: `D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_trace_bound`
- Truth anchor: `D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_zero_of_pure_left`
- Dependency: [D5/S3/Quantum/Hiai/CommonLowerHarmonicBound](../Hiai/CommonLowerHarmonicBound.md)
- Dependency: [D5/S3/Quantum/Information/QubitNormalFormState](QubitNormalFormState.md)
