# Scattering Resonance Lines

## Abstract

The zeta critical line becomes the resonance quarter line and its reflected antiresonance three-quarter line.

**Theorem 1.1 (Critical zeros map to the two scattering lines).**

$$\left(\left(\forall rho \in \mathbb{C},\ \operatorname{IsNontrivialZero}(rho) \Rightarrow \Re(rho) = \frac{1}{2}\right) \Leftrightarrow \left(\forall rho \in \mathbb{C},\ \operatorname{IsNontrivialZero}(rho) \Rightarrow \Re(\frac{rho}{2}) = \frac{1}{4}\right)\right) \land \left(\left(\forall rho \in \mathbb{C},\ \operatorname{IsNontrivialZero}(rho) \Rightarrow \Re(rho) = \frac{1}{2}\right) \Leftrightarrow \left(\forall rho \in \mathbb{C},\ \operatorname{IsNontrivialZero}(rho) \Rightarrow \Re(1 - \frac{rho}{2}) = \frac{3}{4}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/ScatteringResonanceLines.scattering_resonance_lines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The declaration uses the canonical critical-strip zeta-zero predicate. Dividing a zero parameter by two divides its real part by two, so the critical half-line is equivalent to the resonance quarter line.

Reflecting that parameter through one sends real part one quarter to real part three quarters, yielding the independent antiresonance equivalence in the second public conjunct.

## References

- Truth anchor: `D5/S3/Weil/Scattering/ScatteringResonanceLines.scattering_resonance_lines`
