# Unfolded Occurrences in Original HF Archives

## Abstract

The recursive mass of an actual hereditarily finite set counts its descending member paths.

**Definition 1.1 (A total member recursion).**

Lean statement: `D5/S0/History/Spacetime/HFMemberOccurrences.mass`

*Formalization.* `D5/S0/History/Spacetime/HFMemberOccurrences.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mass is defined on the existing HFEncoding.HF by well-founded recursion on membership of its toZF interpretation. Each set contributes one for its root, then the masses of all members in the existing finite members set. Equality of members removes duplicates within one set. Equal descendants reached at different positions remain separate occurrences.

**Theorem 1.2 (The exact recursion equation).**

$$\forall (x:HF), \operatorname{mass}(x)=1+\sum_{y\in \operatorname{members}(x)} \operatorname{mass}(y)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/HFMemberOccurrences.mass_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite sum is over every actual member once. Mathlib's well-founded membership relation supplies total recursion; HFEncoding.members_finite supplies the finite domain. There is no order chosen for the members and no common bound on the ranks or the sizes of the input sets.

**Definition 1.3 (Occurrences defined independently as lists).**

Lean statement: `D5/S0/History/Spacetime/HFMemberOccurrences.Occurrence`

*Formalization.* `D5/S0/History/Spacetime/HFMemberOccurrences.Occurrence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An occurrence of x is a finite list p satisfying Descends x p. The empty list denotes the root. A list y :: q is admissible precisely when toZF(y) belongs to toZF(x) and q descends from y. This definition refers only to actual membership and lists; it does not refer to mass or to an auxiliary tree representation. In ordinal two, both [ordinal zero] and [ordinal one, ordinal zero] reach zero and are distinct occurrences.

**Theorem 1.4 (Finiteness and exact occurrence count).**

$$\forall (x:HF), \operatorname{card}(\operatorname{Occurrence}(x))=\operatorname{mass}(x)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/HFMemberOccurrences.occurrence_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All occurrences are finite in number. Deleting the first member of a nonempty descending list gives a bijection between occurrences of x and the disjoint sum of its root and the occurrence families of its members. Well-founded induction proves finiteness of this disjoint sum and then identifies its cardinality with the recursive mass. Different first members occupy different summands even when later descendants coincide. The finite instance rules out the infinite-type zero convention for Nat.card.

**Theorem 1.5 (Every finite ordinal has exponential unfolded mass).**

$$\forall (n:\mathbb{N}), \operatorname{mass}(\operatorname{natCode}(n))=2^{n}$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/HFMemberOccurrences.mass_natCode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These are the original finite von Neumann ordinal codes. Ordinal zero is empty and has mass one. The code of n + 1 inserts the code of n into the code of n. No ordinal belongs to itself, so the insertion adds exactly the mass of that new member to the previous mass and doubles it. Induction therefore gives 2 to the n for every natural n, including zero. The path correspondence gives the same number of actual occurrences. These codes are ordinals, not cumulative hierarchy levels.

**Theorem 1.6 (An archived leaf bounds the complete rich code).**

$$\forall (x:\operatorname{Rich}(3)), \forall (e:\operatorname{Event}(x)), \forall (n:\mathbb{N}), \operatorname{source}(x,e)=\operatorname{of}(n) \implies 2^{n}\leq \operatorname{mass}(\operatorname{richCode}(x)) \land 2^{n}\leq \operatorname{card}(\operatorname{Occurrence}(\operatorname{richCode}(x)))$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/HFMemberOccurrences.richCode_leaf_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Event(x) is the archived event subtype of x's context, and source(x,e) is that event's actual source attribute. Let x be any original Rich 3, e any archived event and n any natural number whose source is FreeMagma.of n. Its source code contains the ordinal code n inside the original tagged Kuratowski pair. Membership bounds carry its mass through the source, sign, position and time tuple, the complete attribute graph, the archive record, the current-region pair and the selected-set pair. The actual path correspondence then gives the occurrence bound. Neither the current region nor the selection needs to contain e. The original causal graph and every attribute remain in the encoded object.

A Kuratowski pair contains both operands along actual member paths, including the diagonal case in which its inner or outer members coincide. The proof therefore allows identity/attribute equality, member overlap, repeated sources and all collisions between nested fields. It uses no noncollision hypothesis and no pruning of an archive.

For the family of Definition 497.1, take the typed event domain Fin N times Bool and any injective map of this domain into actual HF identities. TaggedPresentation transports the time i + 1, three zero coordinates, Boolean sign, source leaf (i + 1), and causal relation i < j to the exact archive. Take the entire event domain as the current region and any finite selected subset. For every event at layer n the theorem gives at least 2 to the n occurrences in the original full richCode, for both signs and every legal selection, including the empty set and the original Mobius mask. This application restricts neither identities nor collisions. At N = 0 the event assertions are vacuous; ordinal-zero and the general source-zero bound remain included.

Mass counts unfolded set nodes. It does not count distinct hereditary nodes, stored shared nodes, framed bits or machine work. The asymmetric relation identity, uniform two-sided full-family estimates, empty archive value 44, literal framing and cold-run costs, identity bit construction and native-input separation of Theorem 497.2 require additional arguments. No running-time or space claim follows here.

## References

- Truth anchor: `D5/S0/History/Spacetime/HFMemberOccurrences.Occurrence`
- Truth anchor: `D5/S0/History/Spacetime/HFMemberOccurrences.mass`
- Truth anchor: `D5/S0/History/Spacetime/HFMemberOccurrences.mass_eq`
- Truth anchor: `D5/S0/History/Spacetime/HFMemberOccurrences.mass_natCode`
- Truth anchor: `D5/S0/History/Spacetime/HFMemberOccurrences.occurrence_card`
- Truth anchor: `D5/S0/History/Spacetime/HFMemberOccurrences.richCode_leaf_bound`
- Dependency: [D5/S0/History/Spacetime/ArchiveEncoding](ArchiveEncoding.md)
