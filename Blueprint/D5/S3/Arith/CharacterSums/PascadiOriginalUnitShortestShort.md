# The actual short unit-vector charts

## Abstract

Short unit-vector charts of the original six-return word contribute at most an explicit constant times XY log(2p), with all parameters and endpoint multiplicities counted in their actual common lattice.

**Theorem 1.1 (A direct original-tuple bound over every short physical scale).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalUnitShortestShort.actual_unit_shortest_short_tuple_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalUnitShortestShort.actual_unit_shortest_short_tuple_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be prime and X,Y,H positive with H^2=XY, p^3<=XY, 2X<p^2 and 2Y<p^3. Fix the original alternating units a1,a2. Let T be any finite set of literal ReturnRows with the separate X,Y bounds, the unchanged six-return word equal to minus the identity, and unit original middle entries. At each actual h in T require a genuine reduced index-p^3 middle basis whose shortest vector is the selected R(h), with unit first coordinate and H^2 Q(R(h))<=p^6. Then |T|<=148992 XY (1+log(2p)/log 2). Basis witnesses are required only on T; no coordinate height, scale count, injection or lattice-section cardinality is supplied.

For a dyadic scale s0<=sqrt(Q(R))<2s0, shortness gives H*s0<=p^3. The area lower bound gives H/s0>=1, while the volume term XY/p^3 is at most H/s0. The actual reduced-basis section estimate therefore bounds all original middle parameters and endpoints in that same lattice by 48H/s0. Each original middle parameter has at most 2|F|+1 endpoint pairs by actual_endpoint_pair_elementary_count, including nonunit hyperbola right sides. The proof constructs their images from T and proves their injections, giving at most 4656(H/s0)^2 rows per common lattice.

The unit first coordinate of R determines the entire original congruence lattice, so there is no independent slope lift. The unit middle entries and lattice relation make the second coordinate of R nonzero as well. The area-preserving anisotropic ball bound gives at most 16s0^2 actual vector labels at this scale, hence at most 74496 XY tuples. Reduction and the nonzero integer coordinates put every actual length between 1 and 2p^2. An explicit dyadic finite cover uses at most 2(1+log(2p)/log 2) scales and proves the stated bound. All signs, literal integer multiplicities and the original even-row order y2,y0,y1 are retained.

This proves the short unit-vector branch needed in the original prime-cube decomposition. The nonunit-shortest, long nonunit-right-side and nonunit-endpoint branches have separate actual-count bounds. Combining every branch, the retained long-chart count and the final parameter cutoffs is still required for the complete conjecture.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalUnitShortestShort.actual_unit_shortest_short_tuple_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces](PascadiOriginalChartPieces.md)
