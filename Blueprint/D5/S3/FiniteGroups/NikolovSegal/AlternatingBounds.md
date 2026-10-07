# Orders of Large Alternating Groups

## Abstract

Alternating groups of degree at least five have order divisible by sixty and cannot be 2-groups.

**Lemma 1.1 (Sixty divides the alternating order).**

$$\forall k \in Nat,\; 5 \le k \Rightarrow 60 \mid card\left(alternatingGroup\left(Fin\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.sixty_dvd_card_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Alt(k) denotes the alternating group on Fin(k). Twice its order equals k factorial. For k at least five, divisibility by 5 factorial gives divisibility of the order by sixty.

**Lemma 1.2 (Large alternating groups have even order).**

$$\forall k \in Nat,\; 5 \le k \Rightarrow 2 \mid card\left(alternatingGroup\left(Fin\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.two_dvd_card_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the even-order consequence of divisibility by sixty, used when applying the Sylow 2-subgroup obstruction.

**Lemma 1.3 (Large alternating groups are not 2-groups).**

$$\forall k \in Nat,\; 5 \le k \Rightarrow \left(\neg IsPGroup\left(2, alternatingGroup\left(Fin\left(k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.alternating_not_twoGroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite 2-group has order a power of two. Three divides sixty and hence the order of Alt(k) for k at least five, contradicting that power-of-two order.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.alternating_not_twoGroup`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.sixty_dvd_card_alternating`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.two_dvd_card_alternating`
