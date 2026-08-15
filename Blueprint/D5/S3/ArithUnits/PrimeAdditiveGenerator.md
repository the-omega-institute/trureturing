# Additive Generators Modulo a Prime

## Abstract

Every nonzero residue modulo a prime generates the additive group.

**Theorem 1.1 (Every nonzero residue modulo a prime generates the additive group).**

$$\forall p \text{prime},\quad \forall a \in \mathbb{Z}/p\mathbb{Z},\quad a \neq 0 \Rightarrow \operatorname{AddSubgroup.zmultiples}(a) = \operatorname{top}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/PrimeAdditiveGenerator.nonzero_generates_additive_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p and every nonzero residue a modulo p, the additive subgroup formed by all integer multiples of a is the full additive group ZMod p.

This closes only the source clause saying that every nonzero element modulo a prime is a generator. The source atom's statements about deficits modulo twelve and its metamathematical discussion are not claimed here.

Loogle and the pinned Mathlib source were searched before implementation. The exact general theorem zmultiples_eq_top_of_prime_card states that any nonzero element of a finite additive group of prime cardinality generates the whole group. The Lean proof applies it directly with ZMod.card, so no group-generation argument is re-proved.

## References

- Truth anchor: `D5/S3/ArithUnits/PrimeAdditiveGenerator.nonzero_generates_additive_group`
