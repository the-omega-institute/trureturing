# Graded Prediction Shift

## Abstract

Consecutive finite prediction quotients carry a graded shift that closes after stabilization.

**Theorem 1.1 (The graded shift closes on a stabilized quotient).**

$$\forall m, y,\ s_{m}([y]_{m + 1}) = [\tau(y)]_{m} \land\ p_{m + 1,m}([y]_{m + 1}) = [y]_{m} \land\ \operatorname{deleteCurrent}\left(W_{m + 1}(y)\right) = W_{m}(\tau(y)) \land\ \operatorname{restrictFinal}\left(W_{m + 1}(y)\right) = W_{m}(y) \land\ (R_{m} = R_{m + 1} \Rightarrow\ \operatorname{Bijective}\left(p_{m + 1,m}\right) \land\ Z_{m} \equiv Z_{\infty} \land\ s_{m} = \overline{\tau}_{m} \circ p_{m + 1,m} \land\ e_{m} \circ \overline{\tau}_{m} = \overline{\tau}_{\infty} \circ e_{m}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/GradedPredictionShift.graded_prediction_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At depth m, states are identified when their readout words through m agree. Updating a representative of the depth m + 1 quotient gives a well-defined class at depth m, while the identity representative gives the forgetful projection.

On finite words, the first map deletes the current coordinate and the second deletes the final coordinate. These identities make the two quotient maps exact encodings of the finite-word shift.

If the depth m and depth m + 1 kernel relations agree, the repository's permanent-stability theorem identifies every later relation with the same kernel. The forgetful projection is then bijective, the stabilized finite quotient is equivalent to the complete-itinerary quotient, and the induced closed update is conjugate to the existing completion update.

Pinned Mathlib quotient-map, quotient-congruence, kernel-range, and bijection constructors are applied directly. Repository and library searches found no result combining both maps, both word identities, the stage bijection, and the closed dynamics.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/GradedPredictionShift.graded_prediction_shift`
- Dependency: [D5/S3/ObserverMemory/Prediction/PredictionPartitionStability](../Prediction/PredictionPartitionStability.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](PredictionCompletion.md)
