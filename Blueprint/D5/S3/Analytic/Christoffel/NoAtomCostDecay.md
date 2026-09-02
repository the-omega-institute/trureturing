# No-Atom Christoffel Cost Decay

## Abstract

Unit-circle support gives an explicit polynomial witness and an exponential upper bound for the source Cayley-zero Christoffel cost.

**Theorem 1.1 (The exterior Christoffel cost decays to zero).**

$$\forall cayleyZeros \in \operatorname{CayleyZeroMeasureData}\left(\right), w \in \operatorname{Complex}\left(\right),\; \left(\operatorname{MeasureSupport}\left(\operatorname{CayleyZeroMeasure}\left(cayleyZeros\right)\right) \subseteq \operatorname{ComplexUnitCircle}\left(\right) \land 1 < \operatorname{ComplexNorm}\left(w\right)\right) \Rightarrow \left(\left(\forall N \in \operatorname{Nat}\left(\right),\; \operatorname{PolynomialEval}\left(\operatorname{ObservationPolynomial}\left(w, N\right), w\right) = 1\right) \land \left(\left(\forall N \in \operatorname{Nat}\left(\right), z \in \operatorname{Complex}\left(\right),\; z \in \operatorname{ComplexUnitCircle}\left(\right) \Rightarrow \operatorname{ComplexNorm}\left(\operatorname{PolynomialEval}\left(\operatorname{ObservationPolynomial}\left(w, N\right), z\right)\right) = \operatorname{Inverse}\left(\operatorname{ComplexNorm}\left(w\right)\right)^{N}\right) \land \left(\left(\forall N \in \operatorname{Nat}\left(\right),\; 0 \le \operatorname{CayleyChristoffelCost}\left(cayleyZeros, w, N\right)\right) \land \left(\left(\forall N \in \operatorname{Nat}\left(\right),\; \operatorname{CayleyChristoffelCost}\left(cayleyZeros, w, N\right) \le \operatorname{Product}\left(\operatorname{MeasureOf}\left(\operatorname{CayleyZeroMeasure}\left(cayleyZeros\right), \operatorname{ComplexUnitCircle}\left(\right)\right), \operatorname{ENNRealOfReal}\left(\operatorname{Inverse}\left(\operatorname{ComplexNorm}\left(w\right)\right)^{\operatorname{Product}\left(N, 2\right)}\right)\right)\right) \land \operatorname{Tendsto}\left(\operatorname{LambdaNat}\left(N, \operatorname{CayleyChristoffelCost}\left(cayleyZeros, w, N\right)\right), \operatorname{atTop}\left(\operatorname{Nat}\left(\right)\right), \operatorname{nhds}\left(0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Christoffel/NoAtomCostDecay.no_atom_cost_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the Cayley-zero data contain the repository's nontrivial zeta-zero family, a scale a greater than one half, and positive real weights that are invariant under reflection and conjugation, absolutely summable, and normalized to sum to one. Let muA be their named weighted Dirac sum after the shifted zeros pass through the source Cayley map. Assume its support is contained in the unit circle and let w have norm greater than one.

Its value at w is one and its norm on the unit circle is the Nth power of the inverse norm of w. The same polynomial is an admissible witness for CayleyChristoffelCost, the named source object lambda_N^{mu_a}(w). An explicit Lean equality bridges that object to the repository's generic Christoffel infimum.

Consequently the cost is nonnegative, is bounded above by the unit-circle mass times the displayed inverse-norm power, and tends to zero. In the source volume the support premise for muA is equivalent to RH. Finiteness follows from normalization, so this declaration is conditional on support, does not add a generic finite-measure premise, and does not assert RH.

## References

- Truth anchor: `D5/S3/Analytic/Christoffel/NoAtomCostDecay.no_atom_cost_decay`
- Dependency: [D5/S3/Analytic/ZetaObservation/ChristoffelAtomFloor](../ZetaObservation/ChristoffelAtomFloor.md)
