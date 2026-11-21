# Probability laws on deterministic readout tables

## Abstract

Finite deterministic tables carry the marginals and fixed mass of equivariant calibrations.

**Theorem 1.1 (Push a finite calibration to its table law).**

$$\operatorname{Calibration}\left(G, P, a, f\right) \Rightarrow \operatorname{TableLawProperties}\left(G, P, a, \operatorname{TableLaw}\left(a, f\right)\right) \land \operatorname{FixedMass}\left(G, a\right) \le \operatorname{FixedMass}\left(G, \operatorname{TableLaw}\left(a, f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FiniteTableCalibration.calibration_table_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a group G act on X and Y, with decidable equality on Y and a finite table type from X to Y. Give the tables the action that applies the inverse group element to the input and the group element to the output. Let G also act on a finite seed type S. The weights a on S are nonnegative and have sum one. The function f takes an input and a seed to an output. It commutes with the actions, and every kernel entry P(x,y) equals the sum of a over seeds returning y at x.

The table law p assigns each table the sum of the weights of seeds giving that entire table. TableLawProperties means that p is nonnegative and sums to one, that G-invariance of a implies G-invariance of p, and that the sum of p over tables giving y at x equals P(x,y) for every x,y. The total weight of seeds fixed by the whole group is at most the total weight of tables fixed by the whole group.

The table map is equivariant by covariance of f. Summing over its fibers gives the marginal and normalization identities. Equivariance maps fixed seeds into fixed tables and allows reindexing the pushforward by a group element when the weights are invariant.

**Theorem 1.2 (Realize a table law on its positive support).**

$$\operatorname{InvariantTableLaw}\left(G, P, p\right) \Rightarrow \exists U, q, f, \operatorname{PositiveCalibration}\left(G, P, U, q, f\right) \land \operatorname{FixedMass}\left(H, q\right)=\operatorname{FixedMass}\left(H, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FiniteTableCalibration.positive_table_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G act on X and Y in universes v and w, with decidable equality on Y and a finite enumeration of the table type. Let H be a subgroup of G. InvariantTableLaw means that p is a nonnegative G-invariant function on tables with sum one and that the sum of p over tables giving y at x equals P(x,y) for every x,y.

The result supplies a finite seed type U in the maximum of v and w with a G-action, a real weight function q, and a readout f from X times U to Y. PositiveCalibration means that the weights are strictly positive, sum to one and are invariant under G. The readout commutes with G, and every P(x,y) is the total weight of seeds giving y at x. FixedMass uses the total weight fixed by every element of H.

The positive-weight tables are stable under the action. Use them as seeds and evaluate the table at the input. Every discarded table has zero weight, so normalization, every marginal and the subgroup-fixed mass all survive the restriction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FiniteTableCalibration.calibration_table_law`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FiniteTableCalibration.positive_table_calibration`
- Dependency: [D5/S3/ConceptDynamics/Attribution/FixedKernelMass](FixedKernelMass.md)
