# Enumeration in increasing rank

## Abstract

An injective natural ranking of an infinite set determines a literal enumeration.

**Theorem 1.1 (An enumeration increasing in an injective rank).**

$$\forall S \in \operatorname{Set}\left(\mathbb{N}\right),\; \forall rank \in \mathbb{N} \to \mathbb{N},\; \left(\operatorname{Infinite}\left(S\right) \land \operatorname{InjOn}\left(rank, S\right)\right) \Rightarrow \left(\exists pi \in \mathbb{N} \to \mathbb{N},\; \left(\operatorname{Injective}\left(pi\right) \land \operatorname{range}\left(pi\right) = S\right) \land \left(\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; i < j \Rightarrow \operatorname{rank}\left(\operatorname{pi}\left(i\right)\right) < \operatorname{rank}\left(\operatorname{pi}\left(j\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationEnumeration.enumerateRank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every infinite subset S of the natural numbers and every natural-valued function rank injective on S, there is an injective map pi from the natural numbers onto S with rank(pi(i)) strictly increasing in i. Enumerate the infinite image rank(S) by Mathlib's Nat.nth, then select its unique preimages in S. Infinite(S) and InjOn(rank,S) denote these two hypotheses; Injective(pi) and range(pi)=S state the literal permutation conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationEnumeration.enumerateRank`
