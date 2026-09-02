# Observer-Mode Critical Kernel

## Abstract

The symmetric completed-zeta digamma difference has its cosine kernel and is strictly positive on the zero-frequency axis for every nonzero shift.

**Theorem 1.1 (The polarized digamma kernel and its axis positivity).**

$$\forall t \in \operatorname{Real}\left(\right), tau \in \operatorname{Real}\left(\right),\; \operatorname{let} a: \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right) = u: \operatorname{Real}\left(\right) \mapsto \operatorname{re}\left(\operatorname{digamma}\left(\frac{1}{4} + \operatorname{I}\left(\right) \cdot \frac{u}{2}\right)\right) - \operatorname{log}\left(\operatorname{pi}\left(\right)\right), \left(\forall u \in \operatorname{Real}\left(\right),\; \operatorname{IntegrableOn}\left(x: \operatorname{Real}\left(\right) \mapsto \operatorname{archimedeanJumpDensity}\left(x\right) \cdot \left(1 - \operatorname{cos}\left(u \cdot x\right)\right), \operatorname{Ioi}\left(0\right), \operatorname{volume}\left(\right)\right) \land a\left(u\right) - a\left(0\right) = 2 \cdot \operatorname{setIntegral}\left(x, \operatorname{Real}\left(\right), \operatorname{Ioi}\left(0\right), \operatorname{archimedeanJumpDensity}\left(x\right) \cdot \left(1 - \operatorname{cos}\left(u \cdot x\right)\right), \operatorname{volume}\left(\right)\right)\right) \Rightarrow \left(\frac{1}{2} \cdot \left(a\left(t + tau\right) + a\left(t - tau\right)\right) - a\left(t\right) = 2 \cdot \operatorname{setIntegral}\left(x, \operatorname{Real}\left(\right), \operatorname{Ioi}\left(0\right), \operatorname{archimedeanJumpDensity}\left(x\right) \cdot \operatorname{cos}\left(t \cdot x\right) \cdot \left(1 - \operatorname{cos}\left(tau \cdot x\right)\right), \operatorname{volume}\left(\right)\right) \land \left(tau \ne 0 \Rightarrow 0 < \frac{1}{2} \cdot \left(a\left(0 + tau\right) + a\left(0 - tau\right)\right) - a\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ObserverModeCriticalKernel.observer_mode_critical_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplier a is displayed on its concrete real digamma carrier. The public premise is its positive-scale Levy representation, including integrability for every real frequency.

Polarization gives the cosine-modulated symmetric-difference kernel. At zero frequency, the imported Archimedean jump density and the nonzero shift produce a strictly positive integral.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ObserverModeCriticalKernel.observer_mode_critical_kernel`
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](ArchimedeanJumpDecomposition.md)
