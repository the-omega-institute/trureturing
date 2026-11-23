# Recovering Event Order from Labels

## Abstract

A complete label history identifies its event order exactly when every label fiber is a chain, for finite induced supports and for complete histories of countably infinite past-finite partial orders.

Let E be any partially ordered type, A any alphabet, F any finite subset of E, and label a function from E to A. The two types have independent universes and may be empty or infinite. A complete extension has no repeated event, contains exactly F, and never places a predecessor after its successor. The order is the order induced on F. An arbitrary F need not be a lower set of E, so these lists do not assert global execution in the ambient event system. ExtensionList is the original EnabledPathSwapConnectivity predicate, with F viewed as its underlying set in the displayed formula.

**Theorem 1.1 (Exact classification of label recovery).**

$$\forall \left(E: Type\right), \forall \left(A: Type\right), [\operatorname{PartialOrder}\left(E\right)] \forall \left(F: \operatorname{Finset}\left(E\right)\right), \forall \left(label: E \to A\right), \left(\forall \left(a: E\right), \left(a \in F\right) \implies \left(\forall \left(b: E\right), \left(b \in F\right) \implies \left(\left(label\left(a\right) = label\left(b\right)\right) \implies \left(\left(a \le b\right) \lor \left(b \le a\right)\right)\right)\right)\right) \iff \left(\forall \left(l: \operatorname{List}\left(E\right)\right), \forall \left(m: \operatorname{List}\left(E\right)\right), \left(\operatorname{ExtensionList}\left(\emptyset, F, l\right)\right) \implies \left(\left(\operatorname{ExtensionList}\left(\emptyset, F, m\right)\right) \implies \left(\left(\operatorname{map}\left(label, l\right) = \operatorname{map}\left(label, m\right)\right) \implies \left(l = m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every two equal-labelled events in F are comparable if and only if any two complete extensions with the same label list are equal as event lists. Repeated labels are allowed, and neither a finite alphabet nor a finite ambient event type is assumed. The empty support is included.

For reconstruction, compare the first events of two extensions. Their labels agree. If they were distinct, each would occur in the other tail. The two extension conditions would then forbid both comparison directions, contradicting the chain condition on that label fiber. The heads agree, and recursion recovers the remaining events.

For the obstruction, take incomparable events with the same label. In the finite subtype of F, the union of their strict predecessor sets is a lower cut containing neither event. The existing finite-poset extension theorem supplies a prefix ending at this cut and a suffix after both events. Concatenating extension lists gives both adjacent orders with a shared prefix and suffix. They have the same label word and distinct event orders. The proof transports exact support, no repetitions, and the pairwise order condition between subtype lists and ambient lists.

This is a repository-derived classification with classical nice-labelling context. Nice labels in finite conflict-free event structures separate incomparable events, equivalently giving chain fibers. See Santocanale, https://arxiv.org/html/0903.3462v1, Definition 2.3, Lemma 2.11, and Proposition 2.12. The present statement concerns complete extensions of arbitrary finite induced subsets and an arbitrary alphabet.

For the infinite statement, E is a countably infinite partially ordered type, and every strict past Iio x is finite. The alphabet A lies in an independent universe and is arbitrary. A History E is a bijection e from the natural numbers onto E satisfying, for every i < j, not (e j <= e i). Thus every event occurs exactly once, and each predecessor occurs before its successor. No total order on E or history is supplied as an additional premise.

**Theorem 1.2 (Complete natural histories and exact label recovery).**

$$\forall \left(E: Type_{u}\right), \forall \left(A: Type_{v}\right), [\operatorname{PartialOrder}\left(E\right)] [\operatorname{Countable}\left(E\right)] [\operatorname{Infinite}\left(E\right)] \left(\forall \left(x: E\right), \operatorname{Finite}\left(\operatorname{Iio}\left(x\right)\right)\right) \implies \left(\forall \left(label: E \to A\right), \operatorname{Nonempty}\left(\operatorname{History}\left(E\right)\right) \land \left(\left(\forall \left(a: E\right), \forall \left(b: E\right), \left(label\left(a\right) = label\left(b\right)\right) \implies \left(\left(a \le b\right) \lor \left(b \le a\right)\right)\right) \iff \operatorname{Injective}\left(\left(\lambda \left(h: \operatorname{History}\left(E\right)\right) \mapsto \lambda \left(n: \mathbb{N}\right) \mapsto label\left(h\left(n\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.infinite_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a complete natural history. On all such histories, the complete infinite label word determines the history exactly when all equal-label events are comparable. Countability and finite strict pasts apply to the original partial order; the statement imposes no bound on its width or on the alphabet.

For existence, choose an injective natural-number code c for E. The closed past of x is finite, so define its rank r(x) as the sum of c(y)+1 over y <= x. This rank bounds c(x) and increases strictly when x < y. Pair r(x) with c(x) using Nat.pair. Pairing is injective, and the square bounds for Nat.pair show that this key increases along strict comparisons: the key for x is less than (r(x)+1)^2, while the key for y is at least r(y)^2. Its range is an infinite subset of the natural numbers. Mathlib's Nat.Subtype.orderIsoOfNat enumerates this range in increasing order, and Equiv.ofInjective transports that enumeration back to E. The resulting bijection is compatible with the original partial order.

For recovery, use strong induction on the index. Suppose two histories agree before n and have the same label at n. If their current events differ, surjectivity places each event somewhere in the other history. Injectivity and equality at all earlier indices force both positions to be strictly after n. The two history conditions then forbid both order comparisons between those events, contradicting the chain-fiber hypothesis. This argument uses complete histories and does not assume that arbitrary prefixes of equal length have the same support.

For necessity, let a and b be incomparable events with the same label. The union of their closed pasts is a finite lower support F. The existing private incomparable_collision construction on the subtype F gives complete finite extensions with a shared prefix and suffix and with a,b in the two adjacent orders. The complement of F remains countably infinite and past-finite. Choose one complete history of that complement. The history_append construction joins each finite extension to this same actual continuation, proving bijectivity and order compatibility across the join. The two resulting complete histories differ at the swap position and have identical infinite label words.

Brightwell and Luczak, Order-invariant measures on fixed causal sets, https://arxiv.org/abs/0901.0242v2, abstract and Introduction, identify countably infinite past-finite posets precisely with posets admitting natural extensions. Their natural extension is the History object used here. The Lean construction combines countability, finite sums, natural-number pairing and Mathlib's exact infinite-subset enumeration API with the finite extension and collision machinery in this owner.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.infinite_result`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.result`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity](EnabledPathSwapConnectivity.md)
