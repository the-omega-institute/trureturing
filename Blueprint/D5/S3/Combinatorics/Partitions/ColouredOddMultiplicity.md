# Coloured odd multiplicity

## Abstract

Coloured odd occupations and multiplicity partitions

An occupation assigns a nonnegative integer to each colour and mode. Mode n contributes the positive odd weight 2n+1. Forgetting colours gives an ordinary partition; at each occurring part, its multiplicity is allocated among the finite colour set by a weak composition.

Conversely, every allocation at an odd part k contributes the corresponding exponents at mode k/2. Oddness makes this mode recovery injective. Counting each part and each colour proves both inverse laws, including the empty partition and the empty colour set.

The finite count is the coefficient of the weighted partition GenFun. At each positive odd part k, its local factor has coefficient multichoose(r,N/k) when k divides N and zero otherwise. Reindexing the positive part and positive multiplicity factors yields the formal product of (1-X^(2n+1))^(-r), including rank zero and degree zero.

**Definition 1.1 (The partition into ones).**

$$\forall N \in Nat,\; \operatorname{parts}\left(\operatorname{onesPartition}\left(N\right)\right) = \operatorname{replicate}\left(N, 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity.onesPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N, onesPartition N is the partition of N whose parts are N copies of one, including the empty partition at N = 0.

**Theorem 1.2 (Independent finite partition count).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity.card_colouredFiber`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity.card_colouredFiber` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every colour count r and grade N, the cardinal of the weighted occupation fibre equals the sum over partitions of N of the product of multichoose(r,m) for each occurring odd part of multiplicity m, with factor zero at an even part. The count is defined by this finite partition sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity.card_colouredFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity.onesPartition`
- Dependency: [D5/S3/Combinatorics/Partitions/ColouredOddOccupation](ColouredOddOccupation.md)
