# Actual occupation comparison from compensated tail estimates

## Abstract

The actual positive forcing supplies the finite-core part of a globally scaled subsolution.

**Theorem 1.1 (From eventual quadratic gain and loss to a global lower bound).**

$$\begin{gathered}(\forall x, \left\lvert x\right\rvert>N \longrightarrow (A\cdot \operatorname{f}\left(x\right)^{2}\le \operatorname{G}\left(x\right) \land \operatorname{L}\left(x\right)\le B\cdot \operatorname{f}\left(x\right)^{2}))\\{}\quad\longrightarrow \exists t>0, \forall x, t\cdot \operatorname{f}\left(x\right)\le \operatorname{rawOccupation}\left(x\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedTailComparison.actual_lower_from_tail_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be a nonnegative real profile on the integers bounded by F>0, with summable squares. Fix A>0, B>=0 and a natural cutoff N. Here G(x) is the actual kernel-weight series of f(x+i+1)+f(x-i-1)-2 f(x); L(x) is the actual loss-weight series of f(x+i+1)^2+f(x-i-1)^2, both for i>=0. The first line assumes the gain and loss estimates for every integer outside the stated core.

The finite core includes both endpoints. Its actual positive forcing has a positive minimum: away from zero, the count of shapes is positive because it includes the identity avoider. The scale is chosen so that the scaled values fit the actual mass box, every neighbor term is nonnegative on the core, and the scaled profile is smaller than the core forcing.

Outside the core, the actual kernel mass of one half converts the compensated series back to the paired linear sum minus f(x). The positive scale makes its linear gain dominate the actual rational loss, which is bounded by the squared scale divided by the positive denominator constant h. Square-summability supplies the required finite positive level sets for the existing comparison theorem. This does not claim that any particular nonzero profile meets the tail assumptions.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedTailComparison.actual_lower_from_tail_estimates`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedComparison](OccupiedComparison.md)
