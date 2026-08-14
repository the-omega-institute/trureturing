# Joint Prediction Relation

## Abstract

A joint observation identifies exactly the pairs identified by every component observation.

**Theorem 1.1 (The joint prediction relation is the component intersection).**

$$\forall x, y,\ R_{q_{I}}(x, y) \iff (\forall i,\ R_{q_{i}}(x, y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/JointPredictionRelation.joint_prediction_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q_i be an arbitrary indexed family of observations on one carrier. The joint observation sends a point to the dependent function of all its component readings. Two points have the same joint reading exactly when every component gives them the same reading. Thus the relation induced by the joint observation is the indexed intersection of the component relations.

The pinned library was searched before proving. Exact declaration hits were funext_iff for equality of dependent functions and Set.mem_iInter for membership in an indexed intersection. Searches for predictionRelation, joint_prediction_relation, and a packaged joint observation kernel theorem returned no hit. The proof composes the two library declarations after set extensionality.

The statement is fully general in the carrier, index type, and the possibly index-dependent reading types. It asserts only equality of the induced relations; it does not claim finiteness, independence, a cardinality formula, or a metric fusion law. The source claim contains no numerical certificate.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/JointPredictionRelation.joint_prediction_relation`
