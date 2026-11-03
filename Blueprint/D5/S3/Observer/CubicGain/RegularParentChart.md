# RegularParentChart

## Abstract

An analytic lift in the original source coordinates

Write Lambda for parentLambda and B(b)=6/(1+b)-2/(1+2b). On the regular parent the drift increment is e=-(24/5)(b-1/8)B(b)/Lambda(r,b). For independent coordinates x=(t,b), set r=tb and reconstruct the same whole cubic by parentGain(r,b,e). Encoding its samples as ordinary polynomial coefficients gives chartWorld(x). The eight entries of chartSource are exactly r,b,r(1-r)/b,d and the four ordinary coefficients. The two entries of chartRead are the fifth response p and the actual eighth M response of this one world, at absolute clock eight.

For 9005/10000 <= r <= 9006/10000 and 12758/100000 <= b <= 12759/100000, j=b+r(1-r)/b is less than 83/100 and n=j+r is less than 1731/1000. Positive denominators then give Lambda < 0 by rational division inequalities. Thus the reconstructed drift has a nonzero denominator throughout this strip. All other denominators are positive at strict sources.

The lift is analytic, includes all five literal history equations and the nonzero whole polynomial, and exhausts every original parent world with the same r and b. This is a chart of the original parent, including its ordinary coefficient topology; it is not a change of the eight coordinate norm. Recovering t=r/b gives the original independent source coordinate. Analyticity also holds for both actual read functions.

The strip assertion alone identifies no algebraic center. Applying this chart at the exact critical world requires its independent algebraic definition and source enclosures. On this source strip, the polynomial derivative estimate and the inverse function theorem give a local inverse of (p,f_M), with a convex image neighborhood and a finite bound for the derivative of the complete source lift.

**Theorem 1.1 (The regular strip denominator).**

Lean statement: `D5/S3/Observer/CubicGain/RegularParentChart.strip_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularParentChart.strip_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r and b with 9005/10000 <= r <= 9006/10000 and 12758/100000 <= b <= 12759/100000, parentLambda(r,b) is strictly negative.

**Theorem 1.2 (analytic original parent chart).**

Lean statement: `D5/S3/Observer/CubicGain/RegularParentChart.analytic_original_parent_chart`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularParentChart.analytic_original_parent_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x=(t,b) whose r=tb and b satisfy the displayed closed rational strip bounds, chartWorld(x) belongs to OriginalParent. The maps chartWorld, chartSource and chartRead are real analytic at x. Every original parent W with W.r=tb and W.b=b equals chartWorld(x). Its original fifth and sixth response pair equals response(chartCoordinates(x)), and its recovered quotient r/b is t.

In independent source coordinates x=(t,b), put r=tb, j=t+b(1-t^2), n=j+tb, T=1+b and U=1+2b. The denominator is D=5((b^2+8b+4)jn-2TU(j+n)); put A=(8b-1)(2+5b). The four gain-sample numerators are C0=-24D+3Ajn, C1=3An, C2=3(49b+34)jn-54U(j+n), C3=3Aj. These formulas describe one polynomial of degree at most three, including all possible degree drops.

On every strict regular source, D=(5/2)TUjn Lambda is nonzero. The drift is -C0/D and the gain interpolates Ci/D at the fixed nodes 0,1,2,3. The correspondence is an equality of source entries, drift and the four ordinary coefficients of the same whole polynomial. It does not divide by a gain sample, a coefficient or the drift increment.

The fifth chronological product has trace U+n. The clock-eight product after the actual eighth M action is [[3,1],[8,3]], whose trace against the original source matrix is 3+8b+t(1-tb). The fixed-node interpolation rows at clocks five and eight are (-4,15,-20,10) and (-35,120,-140,56). Consequently both actual reads are rational functions with the common denominator D.

**Theorem 1.3 (The same whole gain).**

Lean statement: `D5/S3/Observer/CubicGain/RegularParentChart.regular_whole_gain_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularParentChart.regular_whole_gain_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real pair x=(t,b), assume 0<tb<1, b>0 and parentLambda(tb,b) is nonzero. Then circuitD(x) is nonzero, -C0/D=24+regularError(tb,b), and the complete four-sample function i maps to Ci/D equals parentGain(chartCoordinates(x)).

**Theorem 1.4 (Original coefficient world correspondence).**

Lean statement: `D5/S3/Observer/CubicGain/RegularParentChart.regular_world_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularParentChart.regular_world_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real pair x=(t,b) with 0<tb<1, b>0 and parentLambda(tb,b) nonzero, chartWorld(x) equals encodeWorld(tb,b,-C0/D,i maps to Ci/D). Equality holds for the original world, including all four ordinary polynomial coefficients.

**Theorem 1.5 (Actual fifth and eighth reads).**

Lean statement: `D5/S3/Observer/CubicGain/RegularParentChart.regular_actual_read_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularParentChart.regular_actual_read_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real pair x=(t,b) with 0<tb<1, b>0 and parentLambda(tb,b) nonzero, chartRead(x)=(circuitP(x)/D,circuitM(x)/D). Here circuitP=-C0+(U+n)(-4C0+15C1-20C2+10C3), while circuitM=-C0+(3+8b+t(1-tb))(-35C0+120C1-140C2+56C3). Thus these are the literal fifth and clock-eight M reads of the same world.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/RegularParentChart.analytic_original_parent_chart`
- Truth anchor: `D5/S3/Observer/CubicGain/RegularParentChart.regular_actual_read_correspondence`
- Truth anchor: `D5/S3/Observer/CubicGain/RegularParentChart.regular_whole_gain_correspondence`
- Truth anchor: `D5/S3/Observer/CubicGain/RegularParentChart.regular_world_correspondence`
- Truth anchor: `D5/S3/Observer/CubicGain/RegularParentChart.strip_denominator`
- Dependency: [D5/S3/Observer/CubicGain/CommonWordSensitivity](CommonWordSensitivity.md)
