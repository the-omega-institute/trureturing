# Escape Iteration

## Abstract

Past the threshold, one step multiplies the excess above it by the conjugate modulus.

Naming the excess above the threshold turns the escape into a single multiplicative statement. The multiplier identity is the threshold identity rearranged, so no new arithmetic about the base is needed: the modulus carries the threshold to the threshold plus two.

**Theorem 1.1 (The escape iterates).**

$$1 < \left|\mathit{betaThirteenConjugate}\right| \land \left(\forall x \in R, d \in R,\; \mathit{escapeThreshold} < \left|x\right| \Rightarrow \mathit{escapeThreshold} + \left|\mathit{betaThirteenConjugate}\right| \cdot \left(\left|x\right| - \mathit{escapeThreshold}\right) \le \left|\mathit{betaThirteenConjugate} \cdot x - d\right|\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotFrontier/EscapeIteration.escape_iterates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image stays past the threshold, so the step applies again. With the witness already established four steps along the orbit, the conjugate coordinates cannot remain bounded.

## References

- Truth anchor: `D5/S0/Tower/NonPisotFrontier/EscapeIteration.escape_iterates`
- Dependency: [D5/S0/Tower/NonPisotFrontier/EscapeThreshold](EscapeThreshold.md)
