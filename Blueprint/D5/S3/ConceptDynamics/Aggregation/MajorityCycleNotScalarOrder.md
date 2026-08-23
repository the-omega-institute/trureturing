# Majority Cycle Is Not a Scalar Order

## Abstract

A concrete three-voter majority cycle cannot be faithfully represented by any scalar linear order.

**Lemma 1.1 (A directed three-cycle has no scalar representation).**

$$\forall C \in Type, U \in Type, o \in \operatorname{LinearOrder}\left(U\right), R \in C \to \left(C \to Prop\right), a \in C, b \in C, c \in C,\; \left(R\left(a, b\right) \land \left(R\left(b, c\right) \land R\left(c, a\right)\right)\right) \Rightarrow \left(\neg \left(\exists u \in C \to U,\; \forall x \in C, y \in C,\; R\left(x, y\right) \Rightarrow u\left(x\right) > u\left(y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder.three_cycle_not_scalar_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a relation contains the directed edges a over b, b over c, and c over a. A faithful scalar representation would place u(a) above u(b), u(b) above u(c), and u(c) above u(a). Transitivity gives the opposite of the last strict inequality, so no map into a linear order can represent all three edges.

**Lemma 1.2 (Each Condorcet-cycle edge wins by two votes).**

$$\operatorname{votes}\left(0, 1\right) = 2 \land \left(\operatorname{votes}\left(1, 2\right) = 2 \land \operatorname{votes}\left(2, 0\right) = 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder.condorcet_cycle_vote_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three cyclic ballots rank the candidates as 0 over 1 over 2, 1 over 2 over 0, and 2 over 0 over 1. Consequently exactly two voters prefer 0 to 1, exactly two prefer 1 to 2, and exactly two prefer 2 to 0. These counts exhibit the three directed majority edges.

**Theorem 1.3 (The majority cycle has no scalar order).**

$$\forall U \in Type, o \in \operatorname{LinearOrder}\left(U\right),\; \neg \left(\exists u \in \operatorname{Fin}\left(3\right) \to U,\; \forall x \in \operatorname{Fin}\left(3\right), y \in \operatorname{Fin}\left(3\right),\; \operatorname{majorityPrefers}\left(x, y\right) \Rightarrow u\left(x\right) > u\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder.majority_cycle_not_scalar_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Requiring two of the three voters makes 0 beat 1, 1 beat 2, and 2 beat 0. Thus the concrete majority relation contains the directed cycle certified by the vote-count lemma.

Applying the abstract cycle obstruction shows that no assignment of utilities in any linear order can put every majority winner strictly above the candidate it defeats.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder.condorcet_cycle_vote_counts`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder.majority_cycle_not_scalar_order`
- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder.three_cycle_not_scalar_order`
