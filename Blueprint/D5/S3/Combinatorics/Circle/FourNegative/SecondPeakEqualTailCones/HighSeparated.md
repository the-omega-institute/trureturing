# Twelve exact shifted polynomial gates

## Abstract

High-a separated chart

For s>=2 and a>=3s and b>=a+2, choose u=2^(s-2), v=2^(a-3s), w=2^(b-a-2). Then z=4u, x=64u^3v, y=256u^3vw, with lambda=2w, epsilon=w and delta=1. The native X allocation is C=8u^2v-1. All natural gaps are nonnegative, and every chart variable is at least 1. Charts proves the complete eleven-slot coordinate identity and transports the native allocation to row 1 of Dyadic.

For each of the first three terminal seams, this module proves four inequalities: nonnegativity of the old doubled cumulative seam, its old successor-minus-one cap gap, the new doubled cumulative seam, and its new successor-minus-one cap gap. These are twelve exact inequalities for the actual head and mask polynomials, not numerical samples.

The proof shifts u=U+1,v=V+1,w=W+1 with U,V,W>=0. Each gate is identified by ring with its complete positive-coefficient Horner expression, whose nonnegativity follows by positivity. The expression literals do not introduce an external axiom. Charts consumes these bounds on this region; Physical and Schedule separately provide the occurrence inventory and all-prefix transport.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Dyadic](Dyadic.md)
