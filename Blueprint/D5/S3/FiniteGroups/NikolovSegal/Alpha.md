# The Largest Alternating Section Degree

## Abstract

The alternating section degrees of a finite group form a nonempty bounded set whose supremum is attained.

**Definition 1.1 (The set of alternating degrees).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\forall k \in Nat,\; Member\left(k, alternatingDegrees\left(G\right)\right) \Leftrightarrow Involves\left(alternatingGroup\left(Fin\left(k\right)\right), G\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set alternatingDegrees(G) consists exactly of natural numbers k for which Alt(k) is a section of G. It includes the trivial alternating groups at small degrees.

**Definition 1.2 (The alternating section invariant).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow alpha\left(G\right) = sSup\left(alternatingDegrees\left(G\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The invariant alpha(G) is the natural-number supremum of alternatingDegrees(G). The supremum uses the conditional supremum operation on natural numbers. For finite G, the results below establish boundedness and show that this is an attained largest degree.

**Lemma 1.3 (Degree zero supplies a section).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow Nonempty\left(alternatingDegrees\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alternating group on Fin(0) is trivial, so the trivial homomorphism from G onto it is surjective. No finiteness hypothesis is needed for nonemptiness.

**Lemma 1.4 (A cardinal bound for every section degree).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(Finite\left(G\right) \Rightarrow \left(\forall k \in Nat,\; Involves\left(alternatingGroup\left(Fin\left(k\right)\right), G\right) \Rightarrow k \le add\left(mul\left(2, card\left(G\right)\right), 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Alpha.alternating_degree_card_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For degree at least two, twice the alternating order is k factorial. Section-order divisibility bounds that order by the finite ambient order, and k is at most k factorial. Degrees zero and one satisfy the displayed bound directly.

**Lemma 1.5 (Finite groups have bounded section degrees).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(Finite\left(G\right) \Rightarrow BddAbove\left(alternatingDegrees\left(G\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees_bddAbove` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every alternating section degree is at most twice the ambient order plus one. Thus the natural-number supremum has a finite upper bound.

**Theorem 1.6 (The supremum is an attained maximum).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(Finite\left(G\right) \Rightarrow \left(Involves\left(alternatingGroup\left(Fin\left(alpha\left(G\right)\right)\right), G\right) \land \left(\forall k \in Nat,\; Involves\left(alternatingGroup\left(Fin\left(k\right)\right), G\right) \Rightarrow k \le alpha\left(G\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite group, Alt(alpha(G)) is actually a section of G, and every alternating section degree is at most alpha(G). Nonemptiness and boundedness justify attainment; alpha is not merely an upper-bound surrogate.

**Lemma 1.7 (All large-degree transfers give the maximum bound).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\forall Q \in Typew,\; Group\left(Q\right) \Rightarrow \left(Finite\left(Q\right) \Rightarrow \left(\left(\forall k \in Nat,\; \left(5 \le k \land Involves\left(alternatingGroup\left(Fin\left(k\right)\right), G\right)\right) \Rightarrow Involves\left(alternatingGroup\left(Fin\left(k\right)\right), Q\right)\right) \Rightarrow alpha\left(G\right) \le max\left(alpha\left(Q\right), 4\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha_le_max_of_section_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source group need not be finite in this implication. Every degree at most four is bounded by the second maximum argument; every larger section transfers to the finite target and is bounded by its attained alpha.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha_le_max_of_section_transfer`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha_spec`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees_bddAbove`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees_nonempty`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Alpha.alternating_degree_card_bound`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Sections](Sections.md)
