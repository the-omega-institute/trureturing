# Model-Relative Completeness and the Difference Criterion

## Abstract

Completeness relative to a prior model is equivalent to the observer residual meeting the model difference set only at zero.

**Definition 1.1 (Model-relative completeness).**

Lean statement: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.modelRelativeComplete`

*Formalization.* `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.modelRelativeComplete` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A readout family is complete on a model when its joint readout is injective after the state type is restricted to that model.

**Definition 1.2 (The model difference set).**

Lean statement: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.modelDifference`

*Formalization.* `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.modelDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The difference set consists of every ordered difference x - y of two states belonging to the prior model.

**Definition 1.3 (The additive joint residual).**

Lean statement: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.jointDifferenceResidual`

*Formalization.* `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.jointDifferenceResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A difference belongs to the additive residual when the imported joint kernel cannot distinguish it from zero.

**Theorem 1.4 (Completeness is the zero-intersection criterion).**

$$\operatorname{modelRelativeComplete}\left(q, M\right) \iff \operatorname{Intersection}\left(\operatorname{jointDifferenceResidual}\left(q\right), \operatorname{modelDifference}\left(M\right)\right) = \{0\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.model_relative_completeness_difference_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Additivity turns equality of all readings at x and y into membership of x - y in the additive joint residual.

Thus a collision inside the model gives a nonzero point of the intersection, and every nonzero point of the intersection reconstructs a collision in the restricted joint readout.

The reverse implication reuses the frozen local-global residual criterion on the subtype of model states. Nonemptiness is used only to put zero into the model difference set. This closes atom generic-residual-3f7117a0063a50720284293a156821caec1fd36507f73246da479e340fd396b5.

**Theorem 1.5 (The nonempty-model premise is necessary).**

$$\operatorname{modelRelativeComplete}\left(id, \emptyset\right) \land \operatorname{Intersection}\left(\operatorname{jointDifferenceResidual}\left(id\right), \operatorname{modelDifference}\left(\emptyset\right)\right) \ne \{0\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.model_nonempty_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the empty subset of the integers, restricted completeness is vacuous. Its difference set is empty, so the intersection cannot equal the singleton zero set.

**Theorem 1.6 (Additivity is necessary).**

$$\neg\operatorname{modelRelativeComplete}\left(square, \{-1, 1\}\right) \land \operatorname{Intersection}\left(\operatorname{jointDifferenceResidual}\left(square\right), \operatorname{modelDifference}\left(\{-1, 1\}\right)\right) = \{0\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.additivity_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer squaring readout identifies -1 and 1 on the two-state model. Its zero residual contains only zero, while the model differences are zero and the two signed differences. Hence the intersection criterion holds although completeness fails.

**Theorem 1.7 (An additive carrier is nonempty).**

$$\forall X, \operatorname{AddGroup}\left(X\right) \implies \operatorname{Nonempty}\left(X\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.additive_carrier_is_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero element witnesses that an additive carrier cannot be empty.

**Theorem 1.8 (The unit model is complete).**

$$\operatorname{modelRelativeComplete}\left(unitReadout, univ\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.unit_model_is_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any readout is injective after restriction to a one-element state type.

**Theorem 1.9 (No coordinates suffice on a singleton model).**

$$\operatorname{modelRelativeComplete}\left(emptyReadoutFamily, \{0\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.empty_coordinate_singleton_model_is_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty readout family is complete when the prior model is the singleton integer zero.

**Theorem 1.10 (A constant readout is incomplete).**

$$\neg\operatorname{modelRelativeComplete}\left(constant, Bool\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.constant_readout_is_incomplete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant readout cannot separate false from true in the full Boolean model.

**Theorem 1.11 (Identity is complete on every model).**

$$\forall M, \operatorname{modelRelativeComplete}\left(id, M\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.identity_readout_is_complete_on_every_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An identity coordinate remains injective after restriction to any prior model.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.additive_carrier_is_nonempty`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.additivity_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.constant_readout_is_incomplete`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.empty_coordinate_singleton_model_is_complete`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.identity_readout_is_complete_on_every_model`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.jointDifferenceResidual`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.modelDifference`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.modelRelativeComplete`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.model_nonempty_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.model_relative_completeness_difference_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion.unit_model_is_complete`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/LocalGlobalResidualCriterion](LocalGlobalResidualCriterion.md)
