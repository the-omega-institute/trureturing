# No-Atom Christoffel Cost Decay

## Abstract

Unit-circle support gives an explicit polynomial witness and an exponential upper bound for the Christoffel evaluation cost.

**Theorem 1.1 (The exterior Christoffel cost decays to zero).**

$$\forall muA \in \operatorname{Measure}\left(\operatorname{Complex}\left(\right)\right), w \in \operatorname{Complex}\left(\right),\; \left(\operatorname{IsFiniteMeasure}\left(muA\right) \land \left(\operatorname{MeasureSupport}\left(muA\right) \subseteq \operatorname{ComplexUnitCircle}\left(\right) \land 1 < \operatorname{ComplexNorm}\left(w\right)\right)\right) \Rightarrow \left(\left(\forall N \in \operatorname{Nat}\left(\right),\; \operatorname{PolynomialEval}\left(\operatorname{ObservationPolynomial}\left(w, N\right), w\right) = 1\right) \land \left(\left(\forall N \in \operatorname{Nat}\left(\right), z \in \operatorname{Complex}\left(\right),\; z \in \operatorname{ComplexUnitCircle}\left(\right) \Rightarrow \operatorname{ComplexNorm}\left(\operatorname{PolynomialEval}\left(\operatorname{ObservationPolynomial}\left(w, N\right), z\right)\right) = \operatorname{Inverse}\left(\operatorname{ComplexNorm}\left(w\right)\right)^{N}\right) \land \left(\left(\forall N \in \operatorname{Nat}\left(\right),\; 0 \le \operatorname{ChristoffelEvaluationCost}\left(muA, w, N\right)\right) \land \left(\left(\forall N \in \operatorname{Nat}\left(\right),\; \operatorname{ChristoffelEvaluationCost}\left(muA, w, N\right) \le \operatorname{Product}\left(\operatorname{MeasureOf}\left(muA, \operatorname{ComplexUnitCircle}\left(\right)\right), \operatorname{ENNRealOfReal}\left(\operatorname{Inverse}\left(\operatorname{ComplexNorm}\left(w\right)\right)^{\operatorname{Product}\left(N, 2\right)}\right)\right)\right) \land \operatorname{Tendsto}\left(\operatorname{LambdaNat}\left(N, \operatorname{ChristoffelEvaluationCost}\left(muA, w, N\right)\right), \operatorname{atTop}\left(\operatorname{Nat}\left(\right)\right), \operatorname{nhds}\left(0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Christoffel/NoAtomCostDecay.no_atom_cost_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let muA be a finite measure on the complex plane whose support is contained in the unit circle, and let w have norm greater than one. For every natural degree N, the observation polynomial is the genuine complex polynomial with value (z/w)^N at z.

Its value at w is one and its norm on the unit circle is the Nth power of the inverse norm of w. The same polynomial is an admissible witness in the repository's existing Christoffel evaluation-cost infimum.

Consequently the cost is nonnegative, is bounded above by the unit-circle mass times the displayed inverse-norm power, and tends to zero. In the source volume the support premise for muA is equivalent to RH, so this declaration is conditional and does not assert RH.

## References

- Truth anchor: `D5/S3/Analytic/Christoffel/NoAtomCostDecay.no_atom_cost_decay`
- Dependency: [D5/S3/Analytic/ZetaObservation/ChristoffelAtomFloor](../ZetaObservation/ChristoffelAtomFloor.md)
