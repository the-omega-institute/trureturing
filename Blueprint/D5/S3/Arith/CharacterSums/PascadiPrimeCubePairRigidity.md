# Exact prime-cube word pairs

## Abstract

A fixed difference package determines at most one prime-square midpoint on each simple unit branch.

**Theorem 1.1 (Derive the midpoint equations).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_midpoint_equations`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_midpoint_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For an odd prime p and a unit coefficient g, use endpoints x± = z ± pu/2 and slopes ρ± = a ± pt/2. The full slopes y± = ρ±x± and y+ − y− = pv give v = au + tz modulo p². The average of the two exact words gives the central word. Their difference, divided by p, gives its linear coefficient. Putting D = v − au gives t²N = gaQ and aP + NQ = 0, where N and Q are the sum and product of D, and P is the sum of uᵢDⱼDₖ(Dⱼ + Dₖ) over the complementary pairs.

**Theorem 1.2 (Lift a simple slope and a unit branch).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_midpoint_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_midpoint_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Fix g, u and v and the lower residues of a and t. If the lower root of the difference quartic is simple and t and N are nonzero modulo p, then a, t and z are uniquely determined modulo p² among exact pairs. The difference of two candidate slopes has square zero, so the polynomial Taylor identity and the unit derivative determine a. The sum of two lifts of t is a unit because it reduces to 2t. The square equation then determines t, and v − au = tz gives z.

**Theorem 1.3 (Determine the integer endpoints).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_literal_pair_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_literal_pair_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Two first triples congruent modulo p² are equal as integer triples when each coordinate varies by less than p². Unit first coordinates allow the exact words to recover both slopes modulo p³. The full slope congruences recover the second triples modulo p³, giving literal equality for coordinate widths less than p³.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_literal_pair_unique`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_midpoint_equations`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiPrimeCubePairRigidity.primeCube_midpoint_unique`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola](PascadiPrimeSquareHyperbola.md)
