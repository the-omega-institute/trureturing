# No Continuous Global Section of the Circle Double Cover

## Abstract

The squaring double cover of the unit circle has no continuous global section.

**Theorem 1.1 (The circle squaring map has no continuous right inverse).**

$$\neg \exists s: Circle \to Circle, \operatorname{Continuous}(s) \land \forall z: Circle, \operatorname{s}\left(z\right)^{2} = z.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection.no_continuous_global_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source map is the canonical squaring map on the exact unit-circle carrier: a section s would satisfy s(z)^2 = z at every point.

To rule out such a section, compose it with the angle exponential and divide by the half-angle exponential. The resulting continuous map takes values in the finite set {1,-1}, so connectedness of the real line forces it to be constant.

The values at 0 and 2*pi differ by a sign because Circle.exp(2*pi) = 1 while Circle.exp(pi) = -1. This contradicts the constant-sign conclusion, proving that no continuous global section exists.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection.no_continuous_global_section`
