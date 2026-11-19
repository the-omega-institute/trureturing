# Retained original endpoints and their derivative defects

## Abstract

The actual derivative-zero partner sets and bounded good records control the second and first moments of retained original endpoint fibers.

For one original integer parameter wt=(w,t), E(wt) is a finite set of actual ordered endpoint coordinate pairs. actualRecordBadPartners filters E by zero pencil derivative at beta=V.1/R.1 reduced modulo p. actualRecordBadDegree is the maximum cardinality of these actual filters over baselines in E, and is zero when E is empty. actualRecordGoodPairs consists of the complementary ordered endpoint pairs with nonzero derivative. These are actual finite sets, not assumed estimates or free record suppliers.

**Theorem 1.1 (Second moment of actual large retained fibers).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment.actual_large_retained_second_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment.actual_large_retained_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 there is C>0 uniform in prime p, widths 0<X<=Y with 3Y<p^2, J1,J2>=1 and fixed alternating units modulo p^3. Let s be any finite set of original integer parameters and choose physical vectors R,V only subject to actual reduced-basis witnesses on s. Require physical(R,V,q(wt))=-wt, longness, unit R.1 and t, the original WordSolution for every endpoint, unit first entries of both endpoints, and J1,J2 bounds on the anchor and endpoint coordinates. If card(E(wt))>=2 D(wt) for the actual bad degree D, then sum over s of card(E(wt))^2 is at most C p^epsilon (9J1J2)^5.

At every baseline, the bad and good partner filters partition E. Their exact cardinality identity and the definition of the actual maximum give m^2<=G+mD, where m=card(E) and G counts good ordered endpoint pairs. The large-fiber condition implies m^2<=2G. Tag these actual pairs by wt. The original words, retained units and actual slope derivative construct full GoodRecordRealization witnesses. The already proved bounded-good-record theorem bounds their disjoint union, and summation gives the second moment. No reduced basis is required at parameter values outside s.

**Theorem 1.2 (Count all retained endpoints by their actual defect and good records).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment.actual_retained_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment.actual_retained_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same original-word, reduced-basis, longness, unit and bounded-coordinate conditions, with no large-fiber hypothesis, the total endpoint count is at most 2 sum D(wt) + sqrt(card(s) C p^epsilon (9J1J2)^5). The constant precedes all chart parameters.

Partition the actual parameter set by 2D<=m. On the complementary small fibers m<=2D. Apply the proved second moment to the large fibers and finite Cauchy--Schwarz with the constant vector 1; their number is at most card(s). The square-root bound and the small-fiber sum give the claimed first moment. The original integer wt is counted once throughout.

The actual defect is intrinsic to E and is not assumed small by this module. A later consumer must bound it using the original singular and zero-reduction partner estimates, then sum physical scales, restore removed charts and prove the original parameter cutoff. These two moment estimates do not alone settle the full Pascadi six-word conjecture.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment.actual_large_retained_second_moment`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment.actual_retained_endpoint_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordCount](PascadiOriginalGoodRecordCount.md)
