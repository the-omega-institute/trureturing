# Independent Convergence Discernment

## Abstract

Finite independent views have monotone convergence discernment, while same-family same-input views contribute zero independent evidence.

**Theorem 1.1 (Independent convergence discernment is monotone).**

$$\begin{aligned}\forall I, F: Type,\\{}[\operatorname{DecidableEq}\left(I\right)], [\operatorname{DecidableEq}\left(F\right)],\\coarse, fine, right: \operatorname{FiniteView}\left(I, F\right),\\\operatorname{ViewRefinement}\left(coarse, fine\right) \Rightarrow \operatorname{Independent}\left(coarse, right\right) \Rightarrow \operatorname{Independent}\left(fine, right\right) \Rightarrow \operatorname{discernmentPower}\left(coarse, right\right) \le \operatorname{discernmentPower}\left(fine, right\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/IndependentConvergenceDiscernment.independent_discernment_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite view records its visible input set, model family, and Boolean readout. Independence is the conjunction of disjoint visible inputs and distinct model families.

The evidence set contains exactly the visible inputs on which the two readouts disagree. A refinement adds visible inputs and preserves the old readout, so the evidence set is a Finset subset and its cardinality cannot decrease.

**Theorem 1.2 (Same-family same-input discernment is zero).**

$$\begin{aligned}\forall I, F: Type,\\{}[\operatorname{DecidableEq}\left(I\right)], [\operatorname{DecidableEq}\left(F\right)],\\left, right: \operatorname{FiniteView}\left(I, F\right),\\\operatorname{SameFamilySameInput}\left(left, right\right) \Rightarrow \operatorname{discernmentPower}\left(left, right\right) = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/IndependentConvergenceDiscernment.same_family_same_input_discernment_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent evidence value is guarded by the independence predicate. Equal model families (together with equal visible inputs) therefore select the zero branch of the finite value.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/IndependentConvergenceDiscernment.independent_discernment_mono`
- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/IndependentConvergenceDiscernment.same_family_same_input_discernment_zero`
