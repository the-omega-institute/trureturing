# RH Locates ZeroData on the Critical Line

## Abstract

Under Mathlib's Riemann hypothesis, every zero in supplied ZeroData lies on the critical line.

**Theorem 1.1 (RH puts every supplied ZeroData zero on the critical line).**

$$\forall hRH: \operatorname{RiemannHypothesis}, \forall Z: \operatorname{ZeroData}, \forall n\in \mathbb{N}, \Re(Z.zero(n)) = \operatorname{criticalAbscissa}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/RhLocatesZeroData.zeroData_zero_on_critical_line_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ZeroData field zero_isNontrivial supplies the nontrivial-zero premise. Through the definitional identification with Zeta23.IsNontrivialZero, the frozen RH_implies_on_line theorem then gives real part one half; unfolding criticalAbscissa closes the displayed equality. Trivial-zero and pole exclusion are already inside that frozen theorem.

This is a conditional one-line composition for the R-F consumer. It does not prove the Riemann hypothesis, O-6, or any zero count.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/RhLocatesZeroData.zeroData_zero_on_critical_line_of_rh`
