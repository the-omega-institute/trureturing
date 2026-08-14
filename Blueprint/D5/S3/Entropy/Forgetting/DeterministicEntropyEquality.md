# Equality and Strict Loss under Deterministic Forgetting

## Abstract

Deterministic finite pushforwards preserve entropy exactly on support-injective maps and lose entropy strictly otherwise.

**Theorem 1.1 (Pushforward entropy equality is injectivity on support).**

$$H(f_{*}p)= H(p) \Leftrightarrow \operatorname{InjOn}(f, \operatorname{supp}(p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/DeterministicEntropyEquality.pushforward_entropy_eq_iff_injective_on_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a normalized nonnegative mass function on a finite carrier X, and let f : X -> Y be any deterministic map. The entropy of the pushforward equals the entropy of p exactly when f is injective among the atoms x for which p(x) is nonzero.

The support qualification is essential. Several zero-mass atoms may lie in one fiber without changing either pushforward mass or entropy. The criterion therefore imposes no injectivity requirement on those atoms and does not replace support by the full carrier.

The proof uses the graph-supported joint law of (f(x), x). Its first marginal is the deterministic pushforward and its joint entropy is H(p), so the chain rule turns equality into vanishing conditional entropy. The frozen conditional equality theorem then says that every nonzero-marginal fiber has a point-mass conditional law, which is equivalent to support injectivity.

**Theorem 1.2 (Strict pushforward entropy loss is a support collision).**

$$H(f_{*}p)< H(p) \Leftrightarrow \neg \operatorname{InjOn}(f, \operatorname{supp}(p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/DeterministicEntropyEquality.pushforward_entropy_lt_iff_not_injective_on_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entropy loss is strict exactly when two distinct nonzero-mass atoms are identified by f. This is the complementary case of the equality classification, not a separate sufficient-condition witness.

For an arbitrary codomain, the nonincrease step factors f through its finite range. The range map is surjective, so the frozen deterministic forgetting theorem applies there; injective relabeling into Y only pads the output law with zero masses and preserves its entropy. Combining that inequality with failure of the equality criterion yields strict decrease.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/DeterministicEntropyEquality.pushforward_entropy_eq_iff_injective_on_support`
- Truth anchor: `D5/S3/Entropy/Forgetting/DeterministicEntropyEquality.pushforward_entropy_lt_iff_not_injective_on_support`
- Dependency: [D5/S3/Entropy/ConditionalEntropyEquality](../ConditionalEntropyEquality.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/Relabeling/InjectiveInvariance](../Relabeling/InjectiveInvariance.md)
