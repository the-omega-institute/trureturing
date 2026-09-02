# Register Validity History

## Abstract

Append-only validity deltas keep exactly one active settlement per assertion key.

**Lemma 1.1 (Revision never overwrites the history).**

$$\forall R \in Type, h \in \operatorname{List}\left(\operatorname{Assignment}\left(R\right)\right), s \in \operatorname{List}\left(R\right), p \in R,\; \operatorname{IsPrefix}\left(h, \operatorname{revise}\left(h, s, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RegisterValidityHistory.revise_preserves_history_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A validity history is a list of assignments, each setting one record to active or void; the effective status of a record is its latest assignment. Revision appends a delta that voids the superseded records and then appends the replacement as active, so the prior history is a prefix of the revised one and no record or delta is ever rewritten.

**Theorem 1.2 (Revision leaves exactly one active record per key).**

$$\forall R \in Type, K \in Type, k \in R \to K, h \in \operatorname{List}\left(\operatorname{Assignment}\left(R\right)\right), a \in K, s \in \operatorname{List}\left(R\right), p \in R,\; \left(\left(\forall r \in R,\; \operatorname{IsActive}\left(k, h, a, r\right) \Rightarrow r \in s\right) \land \left(\left(\neg p \in s\right) \land k\left(p\right) = a\right)\right) \Rightarrow \left(\forall r \in R,\; \operatorname{IsActive}\left(k, \operatorname{revise}\left(h, s, p\right), a, r\right) \Leftrightarrow r = p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RegisterValidityHistory.revise_leaves_exactly_one_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the delta voids every record that was active for the key and the replacement is a fresh record carrying that key. After revision a record is active for the key exactly when it is the replacement: a superseded record now ends in a void assignment, an untouched record keeps its old status and so was never active for the key, and the replacement ends in its active assignment.

This is the Step 5 validity invariant of the codex-formal-answer skill: after any revision of P or G, one active settlement per assertion key remains, and the superseded ones stay in the history as void rather than disappearing.

**Lemma 1.3 (Revision of one key leaves other keys unchanged).**

$$\forall R \in Type, K \in Type, k \in R \to K, h \in \operatorname{List}\left(\operatorname{Assignment}\left(R\right)\right), a \in K, b \in K, s \in \operatorname{List}\left(R\right), p \in R,\; \left(\left(\forall x \in R,\; x \in s \Rightarrow k\left(x\right) = a\right) \land \left(k\left(p\right) = a \land b \ne a\right)\right) \Rightarrow \left(\forall r \in R,\; \operatorname{IsActive}\left(k, \operatorname{revise}\left(h, s, p\right), b, r\right) \Leftrightarrow \operatorname{IsActive}\left(k, h, b, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RegisterValidityHistory.revise_preserves_other_keys` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every superseded record and the replacement carry the revised key, no appended assignment names a record of another key, so the effective status and the active set of every other key are the same before and after the revision.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/RegisterValidityHistory.revise_leaves_exactly_one_active`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/RegisterValidityHistory.revise_preserves_history_prefix`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/RegisterValidityHistory.revise_preserves_other_keys`
