# Uniqueness in the 902160 Cell

## Abstract

The order of three modulo 179 selects exactly one member of the scaled cell.

**Lemma 1.1 (An unbounded exponent characterization).**

$$\forall n \in \mathbb{N}, 3^{n} \equiv 2241 (\mathrm{mod} 179) \iff n \equiv 23 (\mathrm{mod} 89)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell902160Uniqueness.three_pow_modEq_179_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order of three modulo 179 is 89: its eighty ninth power is one, three is not one, and 89 is prime. Its twenty third power and 2241 both have residue 93. Equality of powers therefore determines the exponent modulo 89. This statement applies to every natural exponent.

**Theorem 1.2 (The unique member is 1804320).**

$$\forall n \in \left\{902160, 1804320, 2706480, 3608640, 5412960, 10825920\right\}, 3^{n} \equiv 2241 (\mathrm{mod} n) \iff n = 1804320$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell902160Uniqueness.goldenCell902160_modEq_2241_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every listed index is divisible by 179. Projecting its power congruence to that modulus forces its exponent to be congruent to 23 modulo 89, which excludes the other five indices. The old prime exponent windows alone do not make these exclusions.

For the surviving index, lift the frozen congruence at 10080 to any nonzero multiple of its exponent. The residues modulo 32, 5 and 7 are one, and the residue modulo 9 is zero. Coprime CRT combines these with the congruence modulo 179. The large powers stay symbolic; only small certificates and exponent residues are normalized.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell902160Uniqueness.goldenCell902160_modEq_2241_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell902160Uniqueness.three_pow_modEq_179_iff`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenCell5040Congruence](GoldenCell5040Congruence.md)
