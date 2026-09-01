# Multiscale Fingerprint Append

## Abstract

A finite damping-defect history is stable under scale append, while an unequal new defect separates extended fingerprints.

**Definition 1.1 (Finite damping-defect history).**

$$\forall Zero \in \operatorname{Type}\left(\right), n \in \operatorname{Nat}\left(\right), realPart \in \operatorname{Function}\left(Zero, \operatorname{Real}\left(\right)\right), scale \in \operatorname{Function}\left(\operatorname{Fin}\left(n\right), \operatorname{Real}\left(\right)\right), k \in \operatorname{Fin}\left(n\right),\; \operatorname{Fintype}\left(Zero\right) \Rightarrow \operatorname{multiscaleDampingFingerprint}\left(realPart, scale\right)\left(k\right) = \operatorname{criticalDampingDefect}\left(realPart, scale\left(k\right)\right)$$

*Formalization.* `D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend.multiscaleDampingFingerprint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate applies the frozen critical damping defect to the same finite carrier at one prescribed scale.

**Theorem 1.2 (Appending one scale preserves and separates).**

$$\forall Zero \in \operatorname{Type}\left(\right), ZeroPrime \in \operatorname{Type}\left(\right), n \in \operatorname{Nat}\left(\right), realPart \in \operatorname{Function}\left(Zero, \operatorname{Real}\left(\right)\right), realPartPrime \in \operatorname{Function}\left(ZeroPrime, \operatorname{Real}\left(\right)\right), scale \in \operatorname{Function}\left(\operatorname{Fin}\left(n\right), \operatorname{Real}\left(\right)\right), tauNew \in \operatorname{Real}\left(\right),\; \left(\operatorname{Fintype}\left(Zero\right) \land \operatorname{Fintype}\left(ZeroPrime\right)\right) \Rightarrow \left(\left(\forall k \in \operatorname{Fin}\left(n\right),\; \operatorname{multiscaleDampingFingerprint}\left(realPart, \operatorname{snoc}\left(scale, tauNew\right)\right)\left(\operatorname{castSucc}\left(k\right)\right) = \operatorname{multiscaleDampingFingerprint}\left(realPart, scale\right)\left(k\right)\right) \land \left(\operatorname{criticalDampingDefect}\left(realPart, tauNew\right) \ne \operatorname{criticalDampingDefect}\left(realPartPrime, tauNew\right) \Rightarrow \operatorname{multiscaleDampingFingerprint}\left(realPart, \operatorname{snoc}\left(scale, tauNew\right)\right) \ne \operatorname{multiscaleDampingFingerprint}\left(realPartPrime, \operatorname{snoc}\left(scale, tauNew\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend.multiscale_fingerprint_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The snoc-castSucc law identifies every old coordinate with its extended counterpart. Equality of extended functions would also identify the last coordinates, contradicting unequal defects at the appended scale.

**Theorem 1.3 (The preregistered collision separates at scale two).**

$$\operatorname{let} b := \operatorname{arcosh}\left(\frac{\operatorname{cosh}\left(1\right) + 1}{2}\right)\;\operatorname{let} X := \operatorname{Vector}\left(\frac{3}{2}, -\frac{1}{2}\right)\;\operatorname{let} Y := \operatorname{Vector}\left(\frac{1}{2} + b, \frac{1}{2} + b, \frac{1}{2} - b, \frac{1}{2} - b\right)\;\operatorname{criticalDampingDefect}\left(X, 1\right) = \operatorname{criticalDampingDefect}\left(Y, 1\right) \land \left(\operatorname{criticalDampingDefect}\left(X, 1\right) = 2 \cdot \left(\operatorname{cosh}\left(1\right) - 1\right) \land \left(\operatorname{criticalDampingDefect}\left(Y, 1\right) = 2 \cdot \left(\operatorname{cosh}\left(1\right) - 1\right) \land \left(\operatorname{criticalDampingDefect}\left(X, 2\right) - \operatorname{criticalDampingDefect}\left(Y, 2\right) = 2 \cdot (\operatorname{cosh}\left(1\right) - 1)^{2} \land \left(0 < 2 \cdot (\operatorname{cosh}\left(1\right) - 1)^{2} \land \operatorname{criticalDampingDefect}\left(X, 2\right) \ne \operatorname{criticalDampingDefect}\left(Y, 2\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend.two_scale_collision_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-point centered offsets plus and minus one collide at scale one with the four-point offsets plus and minus b. The double-angle identity makes their scale-two difference the displayed strictly positive square.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend.multiscaleDampingFingerprint`
- Truth anchor: `D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend.multiscale_fingerprint_append`
- Truth anchor: `D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend.two_scale_collision_separation`
- Dependency: [D5/S3/Zeros/Symmetry/CriticalDampingFlatness](CriticalDampingFlatness.md)
