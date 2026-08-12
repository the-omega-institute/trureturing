# Entropy and Capacity under Carrier Forgetting

## Abstract

A genuine finite carrier merge lowers accessible capacity and cannot increase Shannon entropy.

**Definition 1.1 (Accessible capacity is carrier cardinality).**

$$\operatorname{capacity}(X)=\operatorname{card} X.$$

*Formalization.* `D5/S3/Entropy/Forgetting/CapacityMonotone.accessibleCapacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Capacity is the independently specified number of accessible outcomes: for a finite carrier X it is Fintype.card X. It is deliberately not defined as a complement of Shannon entropy or KL divergence.

This carrier-size quantity is the record-count side of forgetting. A later theorem can therefore compare capacities even when the input law changes.

**Theorem 1.2 (Deterministic forgetting lowers entropy and capacity).**

$$H(f_{*}p)\leq H(p) \land\\H(f_{*}p)\leq \log \operatorname{capacity}(Y) \land \operatorname{capacity}(Y)\leq \operatorname{capacity}(X).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/CapacityMonotone.deterministic_forgetting_entropy_capacity_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a normalized nonnegative mass function on a finite carrier X. A surjective map f : X -> Y merges records deterministically; pushforward f p is the resulting law on Y. When the carrier-size hypothesis says Y is strictly smaller than X, the theorem proves H(pushforward f p) <= H(p), bounds the output entropy by log(card Y), while the surjection independently proves that the accessible carrier cannot be larger after forgetting. The strict capacity decrease is supplied as a genuine shrink hypothesis, not repeated as a conclusion.

The entropy inequality is derived from the finite entropy chain rule applied to the graph-supported joint law of (f x, x). Its conditional entropy is nonnegative, while the first marginal is exactly the deterministic pushforward. The log-cardinality bound is the independent maximum-entropy theorem on the smaller output carrier.

Surjectivity is used only for the carrier comparison; the entropy argument itself remains valid for any deterministic map. No equality criterion for injectivity on support is claimed here.

**Theorem 1.3 (The Boolean-to-unit merge is strict).**

$$H(f_{*}u)< H(u) \land \operatorname{capacity}(\operatorname{Unit})< \operatorname{capacity}(\operatorname{Bool}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/CapacityMonotone.bool_unit_merge_strict_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform Boolean law is pushed through the genuine merge Bool -> Unit. The output is the unique unit record, so its entropy is zero, while the input entropy is log 2.

The same witness has accessible capacity 1 on Unit and 2 on Bool, with log 1 < log 2. It is therefore a concrete strict carrier-decrease and strict entropy-decrease example, rather than a restatement of an entropy deficit under a renamed capacity.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/CapacityMonotone.accessibleCapacity`
- Truth anchor: `D5/S3/Entropy/Forgetting/CapacityMonotone.bool_unit_merge_strict_witness`
- Truth anchor: `D5/S3/Entropy/Forgetting/CapacityMonotone.deterministic_forgetting_entropy_capacity_monotone`
- Dependency: [D5/S3/Entropy/ConditionalEntropy](../ConditionalEntropy.md)
- Dependency: [D5/S3/Entropy/EntropyNonneg](../EntropyNonneg.md)
