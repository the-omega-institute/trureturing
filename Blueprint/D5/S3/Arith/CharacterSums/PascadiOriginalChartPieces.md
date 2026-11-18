# Removed original unit-chart pieces

## Abstract

Original long unit-middle charts with nonunit hyperbola right side contribute at most a prime subpower times (XY)^2/p^4. Both the parameter fibers and the endpoint fibers count the original integer variables.

**Theorem 1.1 (Original parameters with nonunit right side).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces.actual_nonunit_rhs_parameter_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces.actual_nonunit_rhs_parameter_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For every positive epsilon there is a positive constant C, independent of the prime p, the positive widths X,Y, the unit g modulo p and the finite set s of original integer parameters (w,t). If XY<=p^4, every parameter is in the literal rectangle, and 1+g*w*t=0 modulo p, then |s|<=C*p^epsilon*(1+XY/p).

The integer product n=w*t is nonzero and has absolute value at most XY. All its allowed values lie in one residue class modulo p. Subtract one occurring value and divide by p; the resulting integer codes lie in an interval of radius 2XY/p, giving at most 1+4XY/p product values. For each value, the original ordered integer parameters are a subset of its signed divisor antidiagonal. The classical divisor subpower estimate and |n|<=p^4 bound each fiber by C*p^epsilon. No slope lift is chosen or multiplied into this count.

**Theorem 1.2 (The complete long nonunit-right-side contribution).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces.actual_long_nonunit_rhs_tuple_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces.actual_long_nonunit_rhs_tuple_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For every positive epsilon there is a positive constant C. Let p be prime, X,Y,H be positive real numbers with H^2=XY and p^3<=XY<=p^4, and assume 2X<p^2 and 2Y<p^3. Fix the two original alternating units modulo p cubed. Let T be any finite set of original integer six-letter rows within those widths whose actual return word is minus the identity. Require both middle letters to be units, require the right side 1+a1*a2*t*w to vanish modulo p, and require each original middle pair to admit a reduced basis of its actual index-p-cubed lattice with shortest-vector length sigma satisfying p^3<=H*sigma. Then |T|<=C*p^epsilon*(XY)^2/p^4.

Partition the actual rows by their literal middle coordinates (w,t). The preceding parameter theorem counts the image. In one parameter fiber, take the union F of the two actual endpoint images. The original return equations put both images in the same physical congruence lattice and literal box. The reduced-lattice section estimate and the long-range inequality give |F|<=48XY/p^3. The complete elementary fiber theorem gives at most 2|F|+1<=97XY/p^3 actual endpoint pairs, including nonunit right sides. Endpoints together with the fixed middle pair reconstruct all six original integers, so there is no uncounted multiplicity. Since XY>=p^3, the parameter factor 1+XY/p is at most 2XY/p, yielding the stated bound.

The geometric long-range hypothesis refers to a reduced basis of the actual original lattice; it is not an assumed endpoint-count estimate. Nonunit shortest-vector charts, the complementary short range, and nonunit endpoints in unit-right-side charts require their own counts. These results establish the nonunit-right-side contribution and do not assert the final full return-word bound.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces.actual_long_nonunit_rhs_tuple_count`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces.actual_nonunit_rhs_parameter_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiModularZeroPartners](PascadiModularZeroPartners.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalElementaryFibers](PascadiOriginalElementaryFibers.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage](PascadiOriginalWeightAverage.md)
