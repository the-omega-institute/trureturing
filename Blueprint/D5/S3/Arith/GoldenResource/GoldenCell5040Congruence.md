# Power Congruence on the 5040 Cell

## Abstract

Five small multiplicative orders and coprime CRT determine the power residue on the 5040 cell.

**Theorem 1.1 (The common residue is 2241).**

$$\forall n \in \left\{5040, 10080, 15120, 20160, 30240, 60480\right\}, 3^{n} \equiv 2241 (\mathrm{mod} n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Congruence.goldenCell5040_modEq_2241` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis is membership in the set containing 5040, 10080, 15120, 20160, 30240 and 60480. Write each member as a power of three times m. The exponent of three is two or three, and m is 560, 1120 or 2240.

The multiplicative orders of three modulo 16, 32, 64, 5 and 7 are respectively 4, 8, 16, 4 and 6. Each relevant order divides the member n, so the power of three with exponent n is congruent to one modulo each prime-power factor of m. Coprime CRT combines these congruences.

Since m divides 2240, the target 2241 has residue one modulo m. Both the target and the power of three are divisible by the three-primary factor of n. A second coprime CRT step gives the claim. The large power is kept symbolic throughout the synthesis.

This is a repository-derived statement. The upstream search reported OEIS A066601 as the general sequence of power residues, and did not find this six-member statement in the sources searched. That search was not exhaustive and establishes no claim of literature priority.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Congruence.goldenCell5040_modEq_2241`
