# RegularResponseCircuit

## Abstract

The integral circuit of the original whole world

In independent source coordinates x=(t,b), put r=tb, j=t+b(1-t^2), n=j+tb, T=1+b and U=1+2b. The denominator is D=5((b^2+8b+4)jn-2TU(j+n)); put A=(8b-1)(2+5b). The four gain-sample numerators are C0=-24D+3Ajn, C1=3An, C2=3(49b+34)jn-54U(j+n), C3=3Aj. These formulas describe one polynomial of degree at most three, including all possible degree drops.

On every strict regular source, D=(5/2)TUjn Lambda is nonzero. The drift is -C0/D and the gain interpolates Ci/D at the fixed nodes 0,1,2,3. The correspondence is an equality of source entries, drift and the four ordinary coefficients of the same whole polynomial. It does not divide by a gain sample, a coefficient or the drift increment.

The fifth chronological product has trace U+n. The clock-eight product after the actual eighth M action is [[3,1],[8,3]], whose trace against the original source matrix is 3+8b+t(1-tb). The fixed-node interpolation rows at clocks five and eight are (-4,15,-20,10) and (-35,120,-140,56). Consequently both actual reads are rational functions with the common denominator D.

**Theorem 1.1 (The same whole gain).**

Lean statement: `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_whole_gain_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_whole_gain_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real pair x=(t,b), assume 0<tb<1, b>0 and parentLambda(tb,b) is nonzero. Then circuitD(x) is nonzero, -C0/D=24+regularError(tb,b), and the complete four-sample function i maps to Ci/D equals parentGain(chartCoordinates(x)).

**Theorem 1.2 (Original coefficient world correspondence).**

Lean statement: `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_world_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_world_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those same strictness and regularity assumptions, chartWorld(x) equals encodeWorld(tb,b,-C0/D,i maps to Ci/D). Equality holds for the original world, including all four ordinary polynomial coefficients.

**Theorem 1.3 (Actual fifth and eighth reads).**

Lean statement: `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_actual_read_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_actual_read_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every strict regular source x, chartRead(x)=(circuitP(x)/D,circuitM(x)/D). Here circuitP=-C0+(U+n)(-4C0+15C1-20C2+10C3), while circuitM=-C0+(3+8b+t(1-tb))(-35C0+120C1-140C2+56C3). Thus these are the literal fifth and clock-eight M reads of the same world.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_actual_read_correspondence`
- Truth anchor: `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_whole_gain_correspondence`
- Truth anchor: `D5/S3/Observer/CubicGain/RegularResponseCircuit.regular_world_correspondence`
- Dependency: [D5/S3/Observer/CubicGain/RegularParentChart](RegularParentChart.md)
