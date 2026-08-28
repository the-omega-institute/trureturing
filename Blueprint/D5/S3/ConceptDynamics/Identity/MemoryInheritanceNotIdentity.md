# Branching Memory Inheritance Is Not Equality

## Abstract

A branching memory relation is not right-unique and therefore cannot coincide with equality.

**Lemma 1.1 (Branching memory is not right-unique).**

$$\forall Person \in Type, M \in Person \to \left(Person \to Prop\right),\; \operatorname{AllowsBranching}\left(M\right) \Rightarrow \left(\neg \operatorname{RightUnique}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/MemoryInheritanceNotIdentity.branching_not_right_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A branch gives one predecessor two distinct successors. Right uniqueness would force those successors to be equal, contradicting the distinction that witnesses the branch.

**Theorem 1.2 (Branching memory inheritance is not equality).**

$$\forall Person \in Type, M \in Person \to \left(Person \to Prop\right),\; \operatorname{AllowsBranching}\left(M\right) \Rightarrow \left(\neg \left(\forall a \in Person, b \in Person,\; M\left(a, b\right) \Leftrightarrow a = b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/MemoryInheritanceNotIdentity.branching_memory_is_not_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a memory relation agreed with equality on every pair, then any two successors of the same predecessor would both equal that predecessor and hence equal each other.

Such a relation would be right-unique. A branching memory relation has two distinct successors for one predecessor, so it cannot coincide with equality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identity/MemoryInheritanceNotIdentity.branching_memory_is_not_equality`
- Truth anchor: `D5/S3/ConceptDynamics/Identity/MemoryInheritanceNotIdentity.branching_not_right_unique`
