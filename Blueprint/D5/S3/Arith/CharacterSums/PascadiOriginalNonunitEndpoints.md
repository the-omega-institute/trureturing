# The removed nonunit endpoint piece

## Abstract

Actual original return rows with either nonzero endpoint nonunit obey the outer error estimate.

**Theorem 1.1 (Count actual ReturnRows with a nonunit endpoint).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalNonunitEndpoints.actual_nonunit_endpoint_tuple_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalNonunitEndpoints.actual_nonunit_endpoint_tuple_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For every epsilon>0 choose one positive C before all primes p, original coefficient units a1,a2 modulo p^3, positive X<=Y,H with H^2=XY, p^2<=XY and 2Y<p^2, and finite sets T of actual ReturnRows. All three first-row entries have absolute value at most X and all three second-row entries at most Y. Every row satisfies the literal original sixReturnWord=-I. The middle letters w=h1(2),t=h2(2) and the original right side 1+a1*a2*t*w are units modulo p^3. At least one endpoint (h1(0),h2(0)) or (h1(1),h2(1)) is a nonzero integer vector with nonunit first coordinate modulo p^3. Then card(T)<=C*p^epsilon*(XY/p+(XY)^2/p^4). In particular this controls the long, unit-shortest-vector subpiece that was removed from the retained chart.

For a bad first endpoint, map the actual row to its original middle parameter and that endpoint. The existing unit_right_side_second_residue theorem recovers the opposite endpoint's first coordinate modulo p^3 from the original word. The literal physical widths lift this to integer equality; the actual lattice relation and unit w recover its second coordinate. Thus the incidence map is proved injective on actual rows. Consume the actual nonunit endpoint incidence bound. Partition T by whether its first endpoint is bad; on the other part swap the two actual endpoints, prove that the four original MinusEquations and hence the original word are preserved, and use the same count. This costs only a factor two.

The zero endpoint is outside this removed piece and must be included in the separate retained anchor case when restoring the original rows. The source problem and outer-piece estimate are attributed to Pascadi. The full original conjecture still requires combining all actual charts and their parameter estimates; no worldwide priority or official acceptance is asserted.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalNonunitEndpoints.actual_nonunit_endpoint_tuple_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers](PascadiOriginalLinearFibers.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalNonunitIncidence](PascadiOriginalNonunitIncidence.md)
