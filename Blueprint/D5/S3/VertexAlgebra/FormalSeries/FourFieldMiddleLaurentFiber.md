# FourFieldMiddleLaurentFiber

## Abstract

FourFieldMiddleLaurentFiber

**Definition 1.1 (Seven-index numerator input).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleInput`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural R,J,L,H,M,T,S, write B=b+k,Y=y+a3,Z=z+a1+a2+2k+R+J+L. The numerator input is [x+a0+3k+H+M+T+S,B-R-L-H,Z-M-T,Y-J-S]. Its total is x+b+z+y+sum(a)+6k.

**Definition 1.2 (Exact complex binomial scalar).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleWeight`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is binom(-k,R) binom(-a1,L) (-1)^J binom(-(2k+R),J) times (-1)^(H+M+T+S) binom(-k,H+M) choose(H+M,H) binom(-k,T) binom(-k,S), using the integerBinomial normalization in complex scalars.

**Definition 1.3 (Exact finite admissible fiber).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleFiber`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fiber contains exactly the seven natural indices for which all four signed numerator input coordinates are nonnegative. Its finite natural bounds are derived from those coordinates, including all negative target branches.

**Theorem 1.4 (Bounds forced by admissibility).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middle_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middle_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Admissibility forces R+L+H at most B, J+S at most Y and M+T at most Z, together with all cumulative native bounds and the total-degree bound.

**Theorem 1.5 (Exact membership).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.mem_middleFiber_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.mem_middleFiber_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership is equivalent to nonnegativity of all four original numerator inputs. No independent cutoff or finite-numerator premise is introduced.

**Definition 1.6 (Finite same-numerator readout).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is the finite sum over this exact fiber of the stated scalar times the signed numerator coefficient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.mem_middleFiber_iff`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleFiber`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleInput`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middleWeight`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber.middle_bounds`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber](ThreeFieldBalancedLaurentFiber.md)
