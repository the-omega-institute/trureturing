# FiniteCouplingPushforwardLift

## Abstract

Lift a coarse rational coupling to the original carriers while preserving every original marginal and every paired-readout query.

X, Y, A and B are finite types, with decidable equality on A and B. left and right are FiniteResponseLaw values on X and Y. f : X to A, g : Y to B, and joint is a law on A times B. The parameters hl and hr denote exactly the two displayed coarse-marginal equalities. The lifted result is a law on X times Y. All scalar operations are rational, including total division by zero; validity on null fibers is proved separately.

**Definition 1.1 (Explicit disaggregation weights).**

$$\forall X, Y, A, B, left, right, f, g, joint, x, y, (\operatorname{liftedCouplingMass}(left, right, f, g, joint, \operatorname{pair}(x, y))) = (((\operatorname{mass}(joint, \operatorname{pair}(\operatorname{apply}(f, x), \operatorname{apply}(g, y)))) \cdot (\frac{\operatorname{mass}(left, x)}{\operatorname{mass}(\operatorname{pushforwardResponseLaw}(left, f), \operatorname{apply}(f, x))})) \cdot (\frac{\operatorname{mass}(right, y)}{\operatorname{mass}(\operatorname{pushforwardResponseLaw}(right, g), \operatorname{apply}(g, y))}))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.liftedCouplingMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each original atom receives its coarse cell mass times its two within-fiber shares. Null coarse marginals force the corresponding coarse cells to vanish.

**Definition 1.2 (Normalize the original-carrier law).**

$$\forall X, Y, A, B, left, right, f, g, joint, hl, hr, ((\forall a, (\operatorname{leftResponseMarginal}(\operatorname{mass}(joint), a)) = (\operatorname{mass}(\operatorname{pushforwardResponseLaw}(left, f), a))) \land (\forall b, (\operatorname{rightResponseMarginal}(\operatorname{mass}(joint), b)) = (\operatorname{mass}(\operatorname{pushforwardResponseLaw}(right, g), b)))) \Rightarrow ((\operatorname{mass}(\operatorname{liftCoarseCoupling}(left, right, f, g, joint, hl, hr))) = (\operatorname{liftedCouplingMass}(left, right, f, g, joint)))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.liftCoarseCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition supplies nonnegativity and total mass one from the exact two coarse-marginal contracts, without a strict-positivity premise.

**Theorem 1.3 (Preserve every original probability).**

$$\forall X, Y, A, B, left, right, f, g, joint, hl, hr, ((\forall a, (\operatorname{leftResponseMarginal}(\operatorname{mass}(joint), a)) = (\operatorname{mass}(\operatorname{pushforwardResponseLaw}(left, f), a))) \land (\forall b, (\operatorname{rightResponseMarginal}(\operatorname{mass}(joint), b)) = (\operatorname{mass}(\operatorname{pushforwardResponseLaw}(right, g), b)))) \Rightarrow ((\forall x, (\operatorname{leftResponseMarginal}(\operatorname{mass}(\operatorname{liftCoarseCoupling}(left, right, f, g, joint, hl, hr)), x)) = (\operatorname{mass}(left, x))) \land (\forall y, (\operatorname{rightResponseMarginal}(\operatorname{mass}(\operatorname{liftCoarseCoupling}(left, right, f, g, joint, hl, hr)), y)) = (\operatorname{mass}(right, y))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.liftCoarseCoupling_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire original marginal vectors are retained, including zero-probability states.

**Theorem 1.4 (Preserve all paired-readout expectations).**

$$\forall X, Y, A, B, left, right, f, g, joint, hl, hr, query, ((\forall a, (\operatorname{leftResponseMarginal}(\operatorname{mass}(joint), a)) = (\operatorname{mass}(\operatorname{pushforwardResponseLaw}(left, f), a))) \land (\forall b, (\operatorname{rightResponseMarginal}(\operatorname{mass}(joint), b)) = (\operatorname{mass}(\operatorname{pushforwardResponseLaw}(right, g), b)))) \Rightarrow ((\operatorname{linearObjective}(\lambda pair, \operatorname{apply}(query, \operatorname{pair}(\operatorname{apply}(f, \operatorname{fst}(pair)), \operatorname{apply}(g, \operatorname{snd}(pair)))), \operatorname{mass}(\operatorname{liftCoarseCoupling}(left, right, f, g, joint, hl, hr)))) = (\operatorname{linearObjective}(query, \operatorname{mass}(joint))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.liftCoarseCoupling_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

query is an arbitrary rational function on A times B, chosen after the lift. Its expectation equals that under the supplied coarse coupling.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.liftCoarseCoupling`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.liftCoarseCoupling_expectation`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.liftCoarseCoupling_marginals`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.liftedCouplingMass`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSparseLaw](FiniteMomentSparseLaw.md)
