# Alternative proofs obstruct intersection closure

## Abstract

Lawful proof supports need not be intersection closed or the finite downsets of any fixed digraph.

KernelData specifies accepted proofs, finite axiom and reference readouts, permitted axioms, negation and model semantics. SourceLaws requires soundness in every permitted-axiom model, a finite closed acyclic certificate for every proved proposition, and consistency between a proposition and its negation.

**Definition 1.1 (The support family).**

$$\operatorname{supportFamily}\left(k\right) = \{S \mid \exists C: \operatorname{CertifiedNodes}\left(k\right), S = \operatorname{nodes}\left(C\right)\}$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.supportFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The family consists of the finite node sets of all certified cores. A core selects one accepted proof per node, uses only permitted axioms, contains every selected proof's references, and has an acyclic reference graph. Different members of the support family may select different proofs of the same proposition.

**Definition 1.2 (Binary intersection closure).**

$$\operatorname{IntersectionClosed}\left(A\right) \iff \forall S, T \in A, \operatorname{inter}\left(S, T\right) \in A$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.IntersectionClosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here inter denotes set intersection. This property includes intersections that are empty; no nonemptiness assumption is imposed.

**Definition 1.3 (The finite downsets of a digraph).**

$$\operatorname{graphFamily}\left(e\right) = \{S \mid \operatorname{Finite}\left(S\right) \land (\forall p \in S, \forall q, \operatorname{e}\left(q, p\right) \implies q \in S)\}$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.graphFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The edge relation is arbitrary and is on the same proposition type as the support family. Membership requires finiteness and closure under every direct predecessor. No acyclicity assumption is needed for the intersection argument.

**Definition 1.4 (A universal closure or representation principle).**

$$claim \iff (\forall P, Proof, Ax, Model: Type, \forall k: \operatorname{KernelData}\left(P, Proof, Ax, Model\right), \operatorname{SourceLaws}\left(k\right) \implies (\operatorname{IntersectionClosed}\left(\operatorname{supportFamily}\left(k\right)\right) \lor (\exists e: P \to P \to Prop, \operatorname{supportFamily}\left(k\right) = \operatorname{graphFamily}\left(e\right))))$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposed principle quantifies over all proposition, proof, axiom and model types and all kernel data satisfying SourceLaws. It allows either binary intersection closure or representation as the finite downsets of some fixed digraph. Its negation therefore gives one lawful structure for which both alternatives fail.

**Theorem 1.5 (Both alternatives fail for one lawful kernel).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take six signed propositions: a, b, q and their negatives. Negation flips the sign; a proposition holds exactly when its sign is positive. There is one model, with empty permitted axioms. Four proofs conclude a, b, q and q respectively. The first two have no references; the last two reference a and b respectively. All axiom readouts are empty. Only the three positive propositions are proved, so soundness and consistency hold. The two cores {a,q} and {b,q} have closed accepted witnesses and strictly increasing ranks along edges, so they are acyclic and provide certificates for every proved proposition. Their intersection is {q}. Every accepted proof of q requires a or b, so this singleton admits no closed witness. Finally, finite downsets of any fixed relation are closed under intersection: each predecessor belongs to both sets. Thus this same support family cannot be the finite downsets of any fixed digraph, including any fixed acyclic digraph.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.IntersectionClosed`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.claim`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.graphFamily`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.result`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.supportFamily`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet](LegalLedgerFixedSet.md)
