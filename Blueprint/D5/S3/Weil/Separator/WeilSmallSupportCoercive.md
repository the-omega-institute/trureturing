# Small-support Weil coercivity

## Abstract

The completed-zeta gamma jump gives a mass margin on the fixed small support. The explicit formula transfers the margin to the Weil square with its full boundary term.

**Theorem 1.1 (Coercivity of the gamma term).**

$$\forall f \in WeilTestFunction, hSupport \in \operatorname{tsupport}\left(f\right) \subseteq [-\frac{1}{20}, \frac{1}{20}],\; \frac{1}{20} \cdot \operatorname{l2Mass}\left(f\right) \le \operatorname{archimedeanConstant} \cdot \operatorname{l2Mass}\left(f\right) + \operatorname{archimedeanJumpEnergy}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/WeilSmallSupportCoercive.smallSupport_gamma_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A shift above 1/20 confines the overlap to opposite half-intervals. The bound on twice the real cross term by the two half-interval masses leaves at least one full mass in the translation energy. A shift above 1/10 makes the supports disjoint and leaves two masses.

The first 24 exponential terms of the jump density give a joint lower bound of 277/50 on the integrals over the two tails. The first twelve nonnegative digamma terms give a correction of at least 329/1000. Together with the Euler–Mascheroni and log pi bounds this places the constant at or above −549/100 and leaves a margin of 1/20.

**Theorem 1.2 (Weil lower bound with the boundary contribution).**

$$\forall Z \in ZeroData, f \in WeilTestFunction, hSupport \in \operatorname{tsupport}\left(f\right) \subseteq [-\frac{1}{20}, \frac{1}{20}],\; 2 \cdot \operatorname{normSq}\left(\int_{\mathbb{R}} \operatorname{exp}\left(\frac{x}{2}\right) \cdot \operatorname{f}\left(x\right) dx\right) + \frac{1}{20} \cdot \operatorname{l2Mass}\left(f\right) \le \operatorname{realPart}\left(\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(f\right), \operatorname{symmetricConvergentOfZeroData}\left(Z, \operatorname{convolutionSquare}\left(f\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/WeilSmallSupportCoercive.smallSupport_weil_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At this support scale the exponential cutoff lies below two, so the active prime-power set is empty. The unconditional energy identity then gives the full boundary contribution plus the gamma margin for every zero presentation and every test supported in the stated interval.

## References

- Truth anchor: `D5/S3/Weil/Separator/WeilSmallSupportCoercive.smallSupport_gamma_coercive`
- Truth anchor: `D5/S3/Weil/Separator/WeilSmallSupportCoercive.smallSupport_weil_positive`
- Dependency: [D5/S3/Weil/Separator/UnconditionalExplicitFormula](UnconditionalExplicitFormula.md)
