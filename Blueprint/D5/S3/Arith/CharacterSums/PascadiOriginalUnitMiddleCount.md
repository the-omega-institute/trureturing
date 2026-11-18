# The complete original unit-middle contribution

## Abstract

Six actual subsets of the original integer rows give the complete unit-middle count under one structural seventh-height gap, without supplied shortness, shortest-vector, right-side or endpoint restrictions. The earlier numerical-cutoff statement retains its original type as a consequence.

Write K7=seventhHeightConstant=max(10368·3^9, max(14256, 24·(8·18)^4)).

**Theorem 1.1 (Assemble the unit-middle charts under seventh height).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount.actual_unit_middle_tuple_count_seventh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount.actual_unit_middle_tuple_count_seventh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 there is K>0 uniform in prime p, real widths 1<=X<=Y with 3Y<p^2, positive H with H^2=A=XY and p^3<=A<=p^4, the two alternating units modulo p^3, and the actual finite integer row set T. Require the separate literal X,Y bounds, the original six-return word in order (a,t,b,d,w,v) to equal minus the identity, and both original middle entries w,t to be units. The single gap K7*(32*(A/p^3))^7<p^5 implies card(T)<=K*p^epsilon*(A*(1+L)+A^2/p^4)+sqrt(K*p^epsilon*A^6*L/p^15), where L=1+log(2p)/log 2. No M parameter, supplied reduced basis, right-side unit, endpoint unit or shortness restriction is imposed.

Choose one reduced congruence-lattice basis internally at each occupied actual middle pair and partition T into the same six actual branches. The retained long branch now consumes actual_retained_long_tuple_count_seventh; the other branches use the existing physical counts. The common K absorbs their contributions and the moment square root. Thus seventh height propagates to the entire unit-middle contribution without assuming a count for a removed stratum.

**Theorem 1.2 (Assemble all original unit-middle charts).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount.actual_unit_middle_tuple_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount.actual_unit_middle_tuple_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 there is K>0 uniform in prime p, M, real widths 1<=X<=Y with 3Y<p^2, positive H with H^2=A=XY and p^3<=A<=p^4, the two alternating units modulo p^3, and the finite original integer row set T. Require the separate literal X,Y bounds, the unchanged original six-return word in order (a,t,b,d,w,v) to equal minus the identity, and both original middle entries w,t to be units. Write L=1+log(2p)/log 2. Then card(T)<=K p^epsilon (A(1+L)+A^2/p^4)+sqrt(K p^epsilon A^6 L/p^15), subject to the three explicit numerical long-chart separations (32A/p^3)^5<=M^5 p^3, (10368*3^9)^5 M^35<p^4 and (24*(8*18)^4)^5 M^40<p.

This preserves the earlier numerical-cutoff type. The area lower bound p^3<=A gives 1<=32A/p^3; seventh_height_gap_of_old_cutoffs obtains the new gap from the retained old cap and eighth-height cutoff. The count then follows from actual_unit_middle_tuple_count_seventh. The old residual cutoff remains in this compatibility statement.

Filter T into six actual subsets: nonunit shortest first coordinate; unit shortest first coordinate in the short range H^2 Q<=p^6; the complementary long range with nonunit original hyperbola right side; either physical endpoint zero; unit right side with a nonzero nonunit endpoint; and the retained long range with unit shortest first coordinate, unit right side and unit first entries of both endpoints. The proof establishes that these subsets cover T. They may overlap; finite union cardinality bounds the total by the sum of their actual cardinalities.

The nonunit-shortest branch contributes at most 66048 A^2/p^4 and the short unit-vector branch at most 148992 A L. The original long nonunit-right-side theorem contributes C_epsilon p^epsilon A^2/p^4. The zero-endpoint branch contributes at most 18A. The actual nonzero nonunit-endpoint incidence theorem contributes C_epsilon p^epsilon (A/p+A^2/p^4). Finally the retained original-row theorem contributes C_epsilon p^epsilon (A+(A/p)L+A^2/p^4)+sqrt(C_epsilon p^epsilon A^6 L/p^15). The original small-width inequalities needed by these theorems follow from 1<=X<=Y and 3Y<p^2; p<=H follows from p^3<=A. Since p^epsilon>=1 and p>=1, the six bounds are absorbed into the displayed common K bound, including monotonicity of its square root.

Every count is in the original integer ReturnRows and keeps the original even-row order y2,y0,y1. This module removes all geometric and endpoint branch restrictions from the unit-middle contribution. The new theorem retains only the single seventh-height numerical gap; the earlier theorem retains its three old cutoffs. The complementary area and bounded-prime ranges, nonunit-middle recovery and all-scalar-center assembly belong to subsequent full estimates. The source problem and original word model are due to Pascadi, and an arbitrary-modulus solution is not asserted here.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount.actual_unit_middle_tuple_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount.actual_unit_middle_tuple_count_seventh`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalNonunitEndpoints](PascadiOriginalNonunitEndpoints.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalNonunitShortest](PascadiOriginalNonunitShortest.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalRetainedCount](PascadiOriginalRetainedCount.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalUnitShortestShort](PascadiOriginalUnitShortestShort.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalZeroEndpoints](PascadiOriginalZeroEndpoints.md)
