# Christoffel Atom Floor

## Abstract

A positive point mass forces a uniform positive floor on normalized polynomial energy and its degree-bounded Christoffel infimum.

**Theorem 1.1 (An atom gives every Christoffel cost a positive floor).**

$$\forall mu \in \operatorname{Measure}\left(\operatorname{Complex}\left(\right)\right), w \in \operatorname{Complex}\left(\right), m \in \operatorname{ENNReal}\left(\right),\; \left(\operatorname{MeasureSingleton}\left(mu, w\right) = m \land 0 < m\right) \Rightarrow \left(\left(\forall p \in \operatorname{Polynomial}\left(\operatorname{Complex}\left(\right)\right),\; \operatorname{PolynomialEval}\left(p, w\right) = 1 \Rightarrow \left(\operatorname{Product}\left(m, \operatorname{ENNRealOfReal}\left(\operatorname{ComplexNormSq}\left(\operatorname{PolynomialEval}\left(p, w\right)\right)\right)\right) \le \operatorname{LIntegral}\left(mu, (z \mapsto \operatorname{ENNRealOfReal}\left(\operatorname{ComplexNormSq}\left(\operatorname{PolynomialEval}\left(p, z\right)\right)\right))\right) \land \operatorname{Product}\left(m, \operatorname{ENNRealOfReal}\left(\operatorname{ComplexNormSq}\left(\operatorname{PolynomialEval}\left(p, w\right)\right)\right)\right) = m\right)\right) \land \left(\forall N \in \operatorname{Nat}\left(\right),\; m \le \operatorname{ChristoffelEvaluationCost}\left(mu, w, N\right) \land 0 < \operatorname{ChristoffelEvaluationCost}\left(mu, w, N\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/ChristoffelAtomFloor.christoffel_atom_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Christoffel evaluation cost is the literal infimum of the extended nonnegative squared-norm integral over complex polynomials whose degree is at most N and whose value at w is one.

Restricting the integral to the singleton w gives exactly the atom mass times the squared value there. Monotonicity from the singleton to the whole carrier yields the polynomial bound; taking the infimum yields the same positive floor for every degree.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/ChristoffelAtomFloor.christoffel_atom_floor`
