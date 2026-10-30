# Fixed drift and zero terminal gain

## Abstract

Exact guarded fixed-drift classification in ordinary polynomial worlds

An original world consists of the strict source P=[[r,b],[r(1-r)/b,1-r]], with 0<r<1 and b>0, one nonzero real polynomial g of degree at most three, and one fixed real drift d. The chronological word J,M,J,M,M,M has literal readings (0,24,147/5,24,18,p,v) at clocks zero through six. No observation is added or moved. The parameters p and v are arbitrary real numbers.

Write u=1+2b, C=24-d and K=4200u(u+1). The polynomial coordinates are A=-225du²+(33894-1310d)u+175d-3150, B=75du²+(46494-1710d)u+9450-525d, Z=-225du²-(14490+750d)u+47250-2625d, and Y=-600du²+(240d-72576)u+75600-4200d. Put L=12AB and N=CK(3A-2B).

The three equations are R=4N²-4NL+4(u-1)CKBL-(u-1)²L²=0, E=2100(p-d)(u+1)B-Z(B+1050C(u+1))=0, and F=4200(v-d)(u+1)B-Y(2B+1050C(u+1))=0. The set S(d,p,v) also requires u>1, AB≠0 and 0<N/L<1. All these guards are retained; a root without them need not be a world.

For d≠0 and d≠24, the map from a complete world to u=1+2b is a bijection with S(d,p,v). Its inverse is b=(u-1)/2, j=CK/(6A), n=CK/(4B) and r=N/L. Set e₀=-d/7, e₂=(294-10d)/(25(u+1)), e₄=(18-d)/(3u), h(t)=e₀(t-2)(t-4)/8-e₂t(t-4)/4+e₄t(t-2)/8 and g(t)=(7-t)h(t). The reconstruction stores the ordinary coefficients of this entire polynomial in OriginalWorld. Its source traces are exactly j=b+r(1-r)/b and n=j+r; its drift is the original fixed d.

The seven native traces are (1,j,(u+1)/2,n,u,u+n,2u+n), supplied by the literal chronological matrix products. At clocks zero, two, four and seven, the reconstructed gain has values -d, 5e₂, 3e₄ and zero. Mathlib's finite-node polynomial uniqueness theorem identifies every original gain with this cubic from these four distinct nodes, including all lower degrees and repeated roots. At clocks one, three, five and six its values are 6A/K, 4B/K, 2Z/K and Y/K. The first and third readings force A and B to be nonzero when d≠24. The rank-one source identity is equivalent to R=0, while the last two acquired rows are equivalent to E=F=0. These identities prove every acquired row and equality of the complete original worlds in both inverse laws.

For each fixed d outside {0,24}, the set of complete worlds constrained only by the first five acquired readings and g(7)=0 is finite and has at most ten elements. The coordinate map is injective on this larger set. The polynomial R has degree at most ten and coefficient -41006250000d⁴ at degree ten, which is nonzero. For each fixed p,v and such d, the full seven-reading child is finite and has at most four elements: its injective coordinate image lies in the roots of E, whose degree is at most four and whose coefficient at degree four is 16875d²≠0. Both conclusions count complete original worlds, using Mathlib's root-set finiteness and cardinality bounds.

The statement has no condition p≠24. It allows every original positive width, lower gain degree, sampled zero and repeated root consistent with its stated guards. The separate d=0 and d=24 layers are excluded here, without a claim about their classification. This fixed-drift zero-terminal-gain result does not settle the original independent-pair problem. The classification is a derivation in this matrix observation model and makes no physical realization or literature priority claim.

**Theorem 1.1 (Exact inverse and the ten and four world bounds).**

Lean statement: `D5/S3/Observer/CubicGain/FixedDriftQuartic.fixed_drift_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/FixedDriftQuartic.fixed_drift_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real d,p,v with d≠0 and d≠24, S(d,p,v) is equivalent to the complete seven-reading original worlds at drift d with g(7)=0. The equivalence reconstructs exactly the stated ordinary-coefficient world, and its inverse is the native width coordinate. The reconstructed polynomial and both odd source traces agree with the displayed formulas. The first-five set is finite of cardinality at most ten; the full child is finite of cardinality at most four.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/FixedDriftQuartic.fixed_drift_classification`
- Dependency: [D5/S3/Observer/CubicGain/OriginalWorld](OriginalWorld.md)
