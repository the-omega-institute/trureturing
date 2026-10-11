# Recognition of Simple Groups of Order Sixty

## Abstract

Every finite nonabelian simple group of order sixty is multiplicatively equivalent to the alternating group on five letters.

**Definition 1.1 (The multiplicative equivalence).**

$$\forall G \in Typeu,\; Group\left(G\right) \to \left(Finite\left(G\right) \to \left(IsSimpleGroup\left(G\right) \to \left(\left(card\left(G\right) = 60\right) \to \left(Not\left(IsMulCommutative\left(G\right)\right) \to MulEquiv\left(G, alternatingGroup\left(Fin\left(5\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/SimpleOrderSixty.smallSimpleOrder60EquivAlt5` (`✓ std3`).

*Citation.* Moonshine-in-Kansas/atlas contributors (2026). *Elementary recognition of a nonabelian simple group of order sixty*. URL: <https://github.com/Moonshine-in-Kansas/atlas/blob/1bc46341457aab119f667c43b6ce7216cbb899b6/Atlas/GroupTheory/SimpleOrderSixty.lean>.

*Commentary.*

The type G and its universe are arbitrary. It carries a group structure, is finite and simple, has cardinality sixty, and is nonabelian. The conclusion is an actual multiplicative equivalence from G to the alternating group on Fin 5. No classifier or prescribed images of generators are assumed. The display gives the function type of the construction: Typeu denotes an arbitrary universe, card is Nat.card, Not is logical negation, and MulEquiv is the type of multiplicative equivalences. The chosen group structure is used throughout.

Simplicity makes every proper subgroup have index at least five: a smaller nontrivial coset action would embed G into a permutation group of order at most twenty-four. The Sylow two-subgroups have order four, and their number is five or fifteen. The Sylow five-subgroups have order five, and there are six of them.

Five Sylow two-subgroups give an index-five normalizer. If there are fifteen and their pairwise intersections are trivial, their forty-five nonidentity elements, together with twenty-four from the Sylow five-subgroups, exceed the order of G. Otherwise two distinct Sylow two-subgroups share a nonidentity element t. Both lie in its centralizer, since groups of order four are commutative. That centralizer is proper because the center of a nonabelian simple group is trivial. Its order is a multiple of four strictly larger than four, divides sixty, and is at most twelve. It therefore has order twelve and index five.

The action on the five cosets is faithful: its normal kernel is trivial or the whole simple group, and the latter would make the coset space a singleton. After choosing five coordinates, compose with the sign homomorphism. A faithful map from a group of order sixty into the two-element sign group is impossible, so the sign is trivial. The coset action thus embeds G into the alternating group on five letters. Both groups have order sixty, making this embedding bijective.

This is the classical finite-group recognition argument recorded in the cited ATLAS software source. A quotient application must supply its own cardinality, simplicity and noncommutativity proofs. The equivalence here does not identify specified generators or establish any geometric realization.

**Theorem 1.2 (An index-five subgroup).**

$$\forall G \in Typeu,\; \left(\left(\left(\left(Group\left(G\right) \land Finite\left(G\right)\right) \land IsSimpleGroup\left(G\right)\right) \land card\left(G\right) = 60\right) \land Not\left(IsMulCommutative\left(G\right)\right)\right) \Rightarrow \left(\exists H \in Subgroup\left(G\right),\; index\left(H\right) = 5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SimpleOrderSixty.subgroup_index_five_of_simple_card_sixty` (`✓ std3`). ∎

*Citation.* Moonshine-in-Kansas/atlas contributors (2026). *Elementary recognition of a nonabelian simple group of order sixty*. URL: <https://github.com/Moonshine-in-Kansas/atlas/blob/1bc46341457aab119f667c43b6ce7216cbb899b6/Atlas/GroupTheory/SimpleOrderSixty.lean>.

*Commentary.*

Sylow counting and the centralizer argument construct a subgroup of index five under the same finite, simple, nonabelian and order-sixty hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/SimpleOrderSixty.smallSimpleOrder60EquivAlt5`
- Truth anchor: `D5/S3/FiniteGroups/SimpleOrderSixty.subgroup_index_five_of_simple_card_sixty`
