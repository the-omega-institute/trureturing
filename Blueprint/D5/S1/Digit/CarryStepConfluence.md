# Confluence of Raw Zeckendorf Carries

## Abstract

Arbitrary raw Zeckendorf carry paths preserve value, select one canonical endpoint, and are globally confluent.

**Theorem 1.1 (Raw value is invariant along every carry path).**

$$\forall r, s \in \operatorname{RawDigits}, \operatorname{ReflTransGen}\left(CarryStep, r, s\right) \Rightarrow \operatorname{rawValue}\left(r\right) = \operatorname{rawValue}\left(s\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CarryStepConfluence.rawValue_reflTransGen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction over the reflexive-transitive closure composes the frozen one-step value law for each local carry.

**Theorem 1.2 (Normalization is invariant along every carry path).**

$$\forall r, s \in \operatorname{RawDigits}, \operatorname{ReflTransGen}\left(CarryStep, r, s\right) \Rightarrow \operatorname{normalize}\left(r\right) = \operatorname{normalize}\left(s\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CarryStepConfluence.normalize_eq_of_reflTransGen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both deterministic outputs are canonical and their raw values agree by pathwise preservation, so canonical uniqueness identifies them.

**Theorem 1.3 (Every reachable canonical endpoint is the fixed normal form).**

$$\forall r, s \in \operatorname{RawDigits}, \operatorname{ReflTransGen}\left(CarryStep, r, s\right) \land \operatorname{CanonicalRaw}\left(s\right) \Rightarrow s = \operatorname{normalize}\left(r\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CarryStepConfluence.reachable_canonical_eq_normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Canonical inputs are fixed by normalization, while normalization invariance transports the endpoint back to the original source.

**Theorem 1.4 (The raw carry relation is globally confluent).**

$$\forall r, s, t \in \operatorname{RawDigits}, \operatorname{ReflTransGen}\left(CarryStep, r, s\right) \land \operatorname{ReflTransGen}\left(CarryStep, r, t\right) \Rightarrow \exists u \in \operatorname{RawDigits}, \operatorname{ReflTransGen}\left(CarryStep, s, u\right) \land \operatorname{ReflTransGen}\left(CarryStep, t, u\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CarryStepConfluence.carryStep_confluent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalize both arms of an arbitrary peak. Path invariance identifies both deterministic normal forms, producing a common reduct without critical-pair enumeration.

Pinned Mathlib and D5 searches found generic closure and Church-Rosser infrastructure, but no theorem for this raw carry relation. The result therefore reuses those interfaces and proves the domain-specific global property requested by the paper review.

## References

- Truth anchor: `D5/S1/Digit/CarryStepConfluence.carryStep_confluent`
- Truth anchor: `D5/S1/Digit/CarryStepConfluence.normalize_eq_of_reflTransGen`
- Truth anchor: `D5/S1/Digit/CarryStepConfluence.rawValue_reflTransGen`
- Truth anchor: `D5/S1/Digit/CarryStepConfluence.reachable_canonical_eq_normalize`
