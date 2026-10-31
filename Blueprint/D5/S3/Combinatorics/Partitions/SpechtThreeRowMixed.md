# Literal three-row shapes and the mixed pairing

## Abstract

Literal three-row shapes and the mixed pairing

For a natural triple r of total n, tripleShape(r) is the partition of n whose parts are the positive entries of r, with their multiplicities. This is the existing weightPartition of the finitely supported function r. When r0 is at least r1 and r1 is at least r2, its sorted parts are the list [r0,r1,r2] with zeros deleted. Its first three row lengths, padded with zeros, are exactly r. This includes n=0, equal rows and any number of zero rows.

The ordered-colouring character at a natural margin a equals the fixed-coset character of the literal Young subgroup for tripleShape(a). To see this, take the coefficient of the monomial a in the full-cycle power sum of the permutation. coeff_psumPart_partition computes it as the number of invariant colourings. coeff_psumPart_eq_card_fixedPoints computes the same coefficient as fixed cosets of youngSubgroup(weightPartition(a)). These are independently defined actual permutation actions. The comparison retains labels on equal or empty colours and introduces no factorial for equal rows or zero rows.

For a natural weight a, the existing permutation carrying a to partWeight gives a permutation of its three entries to the first three literal row lengths. The latter decrease. Therefore a0 is at most the first row length and a0+a1 is at most the sum of the first two row lengths. Checking the possible distinct positions of the two selected entries proves these inequalities, uniformly in the entries and total n.

Let s be a nonidentity permutation of the three indices. The integer shifted entries are r(i)-i+s(i). Their sum is n. If s(0) is positive, the first shifted prefix strictly exceeds r0. If s(0)=0, injectivity forces s(1) to be positive; if it were 1 then s would be the identity, so s(1)=2 and the second shifted prefix strictly exceeds r0+r1. When all shifted entries are nonnegative, sorting increases these prefixes. Thus tripleShape(r) does not dominate the shifted weight partition. The existing finrank_hom_spechtModuleComplex_permutationModuleComplex_eq_zero kills its actual mixed pairing. A negative shifted entry gives no colourings at all.

At the identity shift, the Young partition is tripleShape(r) itself. Its actual complex Hom dimension from the same Specht module is one. The full-cycle trace pairing is n factorial times this dimension. Summing with the six signs leaves n factorial. The resulting mixed pairing enters the integer sum-of-squares criterion for the ordinary trace; only its self-Gram hypothesis remains at this stage.

**Theorem 1.1 (The actual same-shape mixed pairing).**

$$\forall n \in \operatorname{Nat},\; \forall r \in \operatorname{NatTriple},\; (\operatorname{totalEq}\left(r, n\right)) \Rightarrow ((\operatorname{decreasing}\left(r\right)) \Rightarrow (\operatorname{mixedSpechtThetaSum}\left(\operatorname{tripleShape}\left(r\right), r\right) = \operatorname{intFactorial}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowMixed.sum_spechtChar_mul_virtualCharacter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The character chi is the integral trace of the existing complex polytabloid Specht module with literal partition tripleShape(r). Theta is the signed sum of the actual ordered-colouring characters. The identity holds for every natural degree n.

**Theorem 1.2 (The trace criterion with the mixed pairing supplied).**

$$\forall n \in \operatorname{Nat},\; \forall r \in \operatorname{NatTriple},\; \forall rho \in \operatorname{Partition}\left(n\right),\; \forall g \in \operatorname{PermFin}\left(n\right),\; \forall tau \in \operatorname{ListNat},\; (\operatorname{totalEq}\left(r, n\right)) \Rightarrow ((\operatorname{decreasing}\left(r\right)) \Rightarrow ((\operatorname{signedContingencyGram}\left(n, r, r\right) = 1) \Rightarrow ((\operatorname{hasFullConjugacyPartition}\left(g, rho\right)) \Rightarrow ((\operatorname{multisetEqParts}\left(tau, rho\right)) \Rightarrow (\operatorname{ordinarySpechtTrace}\left(\operatorname{tripleShape}\left(r\right), g\right) = \operatorname{complexIntCast}\left(\operatorname{HSWfrobChar}\left(r, tau\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowMixed.ordinaryTrace_eq_frobChar_of_selfGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The full conjugacy partition rho and the full multiset of tau include every one-cycle and every repeated part. The only additional scalar hypothesis is signedContingencyGram(n,r,r)=1.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowMixed.ordinaryTrace_eq_frobChar_of_selfGram`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowMixed.sum_spechtChar_mul_virtualCharacter`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtThreeRowVirtual](SpechtThreeRowVirtual.md)
