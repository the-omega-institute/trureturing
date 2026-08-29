# Critical Damping Generator

## Abstract

The normalized diagonal zero generator is skew-adjoint exactly on the critical line.

**Theorem 1.1 (The normalized generator is skew-adjoint exactly on the critical line).**

$$\forall Z: \operatorname{ZeroData}, \forall omega: \mathbb{R}, \frac{1}{2} \le omega \Rightarrow \left(\left(\forall n \in \mathbb {N},\; \Re(Z.zero(n)) = \operatorname{criticalAbscissa}\left(\right)\right) \Leftrightarrow \left(\forall v \in \operatorname{zeroModeIndex}\left(Z\right),\; \operatorname{conj}\left(\operatorname{normalizedMode}\left(omega, Z.zero(\operatorname{first}\left(v\right))\right)\right) = \operatorname{neg}\left(\operatorname{normalizedMode}\left(omega, Z.zero(\operatorname{first}\left(v\right))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/CriticalDampingGenerator.normalized_generator_skew_iff_critical_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mode carrier is the sigma type of an enumerated zero index together with a multiplicity fiber Fin (Z.multiplicity n). At a mode v, the generator scalar is minus omega plus Re(Z.zero v.1) minus the critical abscissa, plus i times the ordinate, with the uniform omega shift added back. Pointwise conjugate-equals-negative is the skew-adjoint condition, and it is equivalent to the critical-line condition.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/CriticalDampingGenerator.normalized_generator_skew_iff_critical_line`
