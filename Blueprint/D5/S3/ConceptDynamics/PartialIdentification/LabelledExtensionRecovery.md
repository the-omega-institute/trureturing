# Recovering Event Order from Labels

## Abstract

A complete label history identifies its event order exactly when every label fiber is a chain in the finite induced partial order.

Let E be any partially ordered type, A any alphabet, F any finite subset of E, and label a function from E to A. The two types have independent universes and may be empty or infinite. A complete extension has no repeated event, contains exactly F, and never places a predecessor after its successor. The order is the order induced on F. An arbitrary F need not be a lower set of E, so these lists do not assert global execution in the ambient event system. ExtensionList is the original EnabledPathSwapConnectivity predicate, with F viewed as its underlying set in the displayed formula.

**Theorem 1.1 (Exact classification of label recovery).**

$$\forall \left(E: Type\right), \forall \left(A: Type\right), [\operatorname{PartialOrder}\left(E\right)] \forall \left(F: \operatorname{Finset}\left(E\right)\right), \forall \left(label: E \to A\right), \left(\forall \left(a: E\right), \left(a \in F\right) \implies \left(\forall \left(b: E\right), \left(b \in F\right) \implies \left(\left(label\left(a\right) = label\left(b\right)\right) \implies \left(\left(a \le b\right) \lor \left(b \le a\right)\right)\right)\right)\right) \iff \left(\forall \left(l: \operatorname{List}\left(E\right)\right), \forall \left(m: \operatorname{List}\left(E\right)\right), \left(\operatorname{ExtensionList}\left(\emptyset, F, l\right)\right) \implies \left(\left(\operatorname{ExtensionList}\left(\emptyset, F, m\right)\right) \implies \left(\left(\operatorname{map}\left(label, l\right) = \operatorname{map}\left(label, m\right)\right) \implies \left(l = m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every two equal-labelled events in F are comparable if and only if any two complete extensions with the same label list are equal as event lists. Repeated labels are allowed, and neither a finite alphabet nor a finite ambient event type is assumed. The empty support is included.

For reconstruction, compare the first events of two extensions. Their labels agree. If they were distinct, each would occur in the other tail. The two extension conditions would then forbid both comparison directions, contradicting the chain condition on that label fiber. The heads agree, and recursion recovers the remaining events.

For the obstruction, take incomparable events with the same label. In the finite subtype of F, the union of their strict predecessor sets is a lower cut containing neither event. The existing finite-poset extension theorem supplies a prefix ending at this cut and a suffix after both events. Concatenating extension lists gives both adjacent orders with a shared prefix and suffix. They have the same label word and distinct event orders. The proof transports exact support, no repetitions, and the pairwise order condition between subtype lists and ambient lists.

This is a repository-derived classification with classical nice-labelling context; it makes no originality claim. Nice labels in finite conflict-free event structures separate incomparable events, equivalently giving chain fibers. See Santocanale, https://arxiv.org/html/0903.3462v1, Definition 2.3, Lemma 2.11, and Proposition 2.12. The present statement concerns complete extensions of arbitrary finite induced subsets and an arbitrary alphabet.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.result`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity](EnabledPathSwapConnectivity.md)
