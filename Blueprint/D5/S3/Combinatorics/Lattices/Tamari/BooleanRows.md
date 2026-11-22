# Boolean antichains and laminar rows

## Abstract

Maximum Boolean antichains of bracketing functions are laminar interval rows.

**Definition 1.1 (Brackets at the ambient rank).**

$$\forall n \in \mathbb{N},\; \operatorname{Brackets}\left(n\right) = \operatorname{BracketingFunctions}\left(n + 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.Brackets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Brackets(n) denotes brackets on Fin(n + 1).

**Definition 1.2 (The Boolean law).**

$$\forall L \in Type,\; (\operatorname{CompleteLattice}\left(L\right)), \forall C \in \operatorname{Set}\left(L\right),\; \operatorname{IsBooleanFamily}\left(C\right) \Leftrightarrow \left(\operatorname{IsAntichain}\left(\leq, C\right) \land \left(\left(\neg \operatorname{top} \in C\right) \land (\forall S \in \operatorname{Set}\left(L\right),\; \forall T \in \operatorname{Set}\left(L\right),\; \left(S \subseteq C \land T \subseteq C\right) \Rightarrow \operatorname{sup}\left(\operatorname{sInf}\left(S\right), \operatorname{sInf}\left(T\right)\right) = \operatorname{sInf}\left(\operatorname{inter}\left(S, T\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.IsBooleanFamily` (`✓ std3`).

*Citation.* Julien Garber, Lina S. Goltermann, Daniel Horiatakis, Dennis König and Tal Gottesman (2026). *Counting Boolean antichains*. DOI: [10.48550/arXiv.2608.27126](https://doi.org/10.48550/arXiv.2608.27126). URL: <https://arxiv.org/html/2608.27126v2#S6.Thmtheorem2>.

*Commentary.*

In a complete lattice, C is an antichain excluding top. For every S and T contained in C, the join of their meets is the meet of their intersection. Empty meets equal top. The Boolean law is equation (2.a) in the source.

**Definition 1.3 (Boolean bracket families).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{Set}\left(\operatorname{Brackets}\left(n\right)\right),\; \operatorname{BooleanFamily}\left(C\right) \Leftrightarrow \operatorname{IsBooleanFamily}\left(C\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.BooleanFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

BooleanFamily restricts IsBooleanFamily to sets of Brackets(n).

**Definition 1.4 (Laminar interval endpoints).**

$$\forall n \in \mathbb{N},\; \forall A \in \pi (s:\operatorname{RowIndex}\left(n\right)) \operatorname{LeftEndpoint}\left(s\right),\; \operatorname{Laminar}\left(A\right) \Leftrightarrow (\forall s \in \operatorname{RowIndex}\left(n\right),\; \forall t \in \operatorname{RowIndex}\left(n\right),\; \left(\operatorname{val}\left(s\right) < \operatorname{val}\left(t\right) \land \operatorname{val}\left(A\left(t\right)\right) \le \operatorname{val}\left(s\right)\right) \Rightarrow \operatorname{val}\left(A\left(t\right)\right) \le \operatorname{val}\left(A\left(s\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.Laminar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If s is earlier than t and the interval ending at t reaches s, that interval contains the interval ending at s.

**Theorem 1.5 (Boolean rows are exactly laminar rows).**

$$\forall n \in \mathbb{N},\; \forall A \in \pi (s:\operatorname{RowIndex}\left(n\right)) \operatorname{LeftEndpoint}\left(s\right),\; \operatorname{BooleanFamily}\left(\operatorname{range}\left(\operatorname{rowFamily}\left(A\right)\right)\right) \Leftrightarrow \operatorname{Laminar}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.boolean_rowFamily_iff_laminar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A crossing gives two subfamilies that violate the meet law. For laminar intervals, the largest admissible row endpoint establishes the law.

**Theorem 1.6 (Maximum cardinality in bracket coordinates).**

$$\forall n \in \mathbb{N},\; \operatorname{IsGreatest}\left(\{k \in \mathbb{N} \mid \exists C \in \operatorname{Set}\left(\operatorname{Brackets}\left(n\right)\right),\; \operatorname{BooleanFamily}\left(C\right) \land \operatorname{ncard}\left(C\right) = k\}, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.booleanFamily_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each non-top bracket has a proper fixed coordinate. Distinct members of a Boolean family cannot share such a coordinate. Singleton intervals attain n.

**Theorem 1.7 (The maximum Boolean families).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{Set}\left(\operatorname{Brackets}\left(n\right)\right),\; (\operatorname{BooleanFamily}\left(C\right) \land \operatorname{ncard}\left(C\right) = n) \Leftrightarrow (\exists A \in \pi (s:\operatorname{RowIndex}\left(n\right)) \operatorname{LeftEndpoint}\left(s\right),\; \operatorname{Laminar}\left(A\right) \land C = \operatorname{range}\left(\operatorname{rowFamily}\left(A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.maximum_boolean_iff_laminar_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At equality each proper endpoint occurs once, and the bracket is forced to be constant on one interval. The Boolean condition becomes laminarity.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.BooleanFamily`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.Brackets`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.IsBooleanFamily`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.Laminar`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.booleanFamily_maximum`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.boolean_rowFamily_iff_laminar`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.maximum_boolean_iff_laminar_rows`
- Dependency: [D5/S3/Combinatorics/Lattices/Tamari/BracketRows](BracketRows.md)
