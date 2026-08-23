# Triviality of Homomorphisms from A5 to Finite P-Groups

## Abstract

Every homomorphism from the alternating group A5 to a finite p-group is trivial.

**Theorem 1.1 (Every homomorphism from A5 to a finite p-group is trivial).**

$$\forall p \in \mathbb{N}, \operatorname{Prime}(p) \Rightarrow \forall P, (\operatorname{FiniteGroup}(P) \land \operatorname{IsPGroup}(p, P)) \Rightarrow \forall phi \in \operatorname{Hom}(A_{5}, P), \forall g \in A_{5}, phi(g) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/SimpleToPGroupTrivial.alternating_five_hom_to_pgroup_trivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prime p and a finite p-group P. Every group homomorphism from the alternating group A5 to P sends every element to the identity. Thus the trivial homomorphism is the only such map, uniformly in the prime and the target p-group.

The kernel is normal in the simple group A5, so it is either the identity subgroup or all of A5. An identity kernel would make the homomorphism injective and transfer the p-group structure of the target to A5. That would make A5 nilpotent, hence solvable and therefore commutative by simplicity, contradicting the noncommutativity of the alternating group of degree five. The kernel must therefore be all of A5, which makes the homomorphism trivial.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/SimpleToPGroupTrivial.alternating_five_hom_to_pgroup_trivial`
