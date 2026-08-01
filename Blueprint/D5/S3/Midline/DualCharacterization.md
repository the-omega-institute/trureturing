# Dual Characterization of the Critical Midline

## Abstract

Mirror fixed points and unitary half-density parameters define the same midline.

**Theorem 1.1 (Mirror fixed points and unitary parameters define the critical midline).**

$$\{s\in\mathbb{C}:\operatorname{mirror}(s)=s\}=\{s\in\mathbb{C}:\forall a,\Vert\operatorname{halfDensityReading}(\ell,s,a)\Vert=1\}\quad\land\quad\{s\in\mathbb{C}:\operatorname{mirror}(s)=s\}=\{s\in\mathbb{C}:\Re(s)=\frac{1}{2}\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/DualCharacterization.midline_dual_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any additive ledger with at least one nonzero length, the set of conjugate-reflection fixed points equals both the set of parameters whose half-density readings all have unit norm and the line of parameters with real part one half. This set-level theorem is derived from the existing pointwise critical-line characterizations. It locates no zeta zero and asserts no Riemann-hypothesis conclusion.
