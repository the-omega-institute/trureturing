# Pullbacks and open-core shadowing

## Abstract

Open pullbacks and an open compact shadowing core yield a forward-shadowing one-step extension.

**Theorem 1.1 (An open map remains open under pullback).**

Lean statement: `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.fibrePullbackSecond_isOpenMap`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.fibrePullbackSecond_isOpenMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

If p:T to B is open and rho:S to B is continuous, the second projection from the fibre pullback of p and rho onto S is open. The proof uses neighborhoods in the product and subspace topologies and does not assume rho is open. The projection is continuous; compact Hausdorff factors give a compact Hausdorff pullback.

**Theorem 1.2 (Forward shadowing for the binary full shift).**

Lean statement: `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.coreShift_uniformHasShadowing`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.coreShift_uniformHasShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Finite-prefix entourages are cofinal in the uniformity of binary names. Diagonal splicing of a controlled forward pseudo-orbit supplies one name tracing all times, including time zero.

**Theorem 1.3 (Shadowing for an open one-step extension).**

Lean statement: `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.open_core_extension_hasShadowing`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.open_core_extension_hasShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Let P and S be compact Hausdorff uniform spaces. Suppose h:P plus S to S is continuous, open, and onto, restricts on S to a continuous map g, and g has finite-open-cover shadowing. Then x maps to inr(h(x)) on the disjoint sum has shadowing. Finite shrinking controls are chosen before the pseudo-orbit. One core tracer controls all later times, while openness and surjectivity of h supply the separate lift at time zero.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.coreShift_uniformHasShadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.fibrePullbackSecond_isOpenMap`
- Truth anchor: `D5/S1/Dynamics/Shadowing/OpenCoreShadowing.open_core_extension_hasShadowing`
- Dependency: [D5/S1/Dynamics/Shadowing/GenericBinarySection](GenericBinarySection.md)
- Dependency: [D5/S1/Dynamics/Shadowing/MetricTracing](MetricTracing.md)
