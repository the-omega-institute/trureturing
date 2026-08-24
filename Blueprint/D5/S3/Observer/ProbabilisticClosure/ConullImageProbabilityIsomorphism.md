# Conull Image Probability Isomorphism

## Abstract

A conull measurable injection pulls a probability law back to its domain.

**Theorem 1.1 (A conull measurable injection is a probability isomorphism).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}\operatorname{StandardBorel}\left(X\right), \operatorname{StandardBorel}\left(O\right),\\{}q: X \to O, \operatorname{Measurable}\left(q\right), \operatorname{Injective}\left(q\right),\\{}\nu: \operatorname{ProbabilityMeasure}\left(O\right), \nu(\operatorname{range}\left(q\right)) = 1 \Rightarrow\\{}e = \operatorname{equivRange}\left(q\right), rho = \operatorname{comap}\left(coe, \nu\right),\\{}\exists \mu: \operatorname{ProbabilityMeasure}\left(X\right), \operatorname{map}\left(q, \mu\right) = \nu \land\\{}\operatorname{MeasurePreserving}\left(e, \mu, rho\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/ConullImageProbabilityIsomorphism.conull_measurable_injection_probability_isomorphism` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard Borel hypotheses turn the measurable injection q into a measurable embedding. Its canonical equivalence e identifies X directly with the measurable subtype range(q).

The measure rho is constructed by pulling nu back along subtype inclusion. Full mass of range(q) makes its pushforward exactly nu, and therefore makes rho a probability measure.

Mapping rho back through the measurable inverse of e constructs mu. The public conclusions state both map(q, mu) = nu and that e is measure-preserving from mu to rho, exposing the conull-space isomorphism rather than wrapping it in mere inhabitation.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/ConullImageProbabilityIsomorphism.conull_measurable_injection_probability_isomorphism`
