# Source facts for the equal-outer marked joint lift

## Abstract

Consumed publication of three existing ThreeBitSource facts across the module boundary.

This module publicly re-exports three private ThreeBitSource facts consumed by ThreeNegativeEqualOuterJointLift. Each proof directly applies the corresponding existing fact; this publication adds no independent mathematical result or novelty claim.

**Lemma 1.1 (Integer total zero).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.source_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.source_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k,t with 3<=k, the sum over i<k of centered(modulus(k),2^i*t) is the integer zero. The bridge re-exports ThreeBitSource.source_zero for the full physical source cycle.

**Lemma 1.2 (The actual three source chains).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.actual_source_chains`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.actual_source_chains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural x,y,z with 0<x, 0<y and 2<=z, put P=2^x, Q=2^y, R=2^z, N=modulus(x+y+z), u=1+P+PQ, v=1+R+RP and w=1+Q+QR. The re-export retains the bounds 1<=u,v,w<N, the identities Ru=N+v, Qv=N+w and Pw=N+u, and all three indexed formulas for the actual centered source: each positive ladder ends at its specified negative half-difference. It directly applies ThreeBitSource.actual_source_chains without changing its hypotheses or ranges.

**Lemma 1.3 (The consumed physical schedule criterion).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.physical_schedule`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.physical_schedule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any label type and integer increment function f, the word F,av,Q,aw,G,au satisfies InStrip(f,C,0) when it permutes the given labels, its three marked increments are -Av,-Aw,-Au, Av and Aw are nonnegative, Au lies in [0,C], all increments in F,Q,G are nonnegative, the mass of F lies in [Av,C], the height after F,av,Q lies in [Aw,C], and the full label sum is zero. The bridge directly applies ThreeBitSource.physical_schedule; the joint lift supplies these physical inventory and seam hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.actual_source_chains`
- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.physical_schedule`
- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.source_zero`
- Dependency: [D5/S3/Combinatorics/Circle/DyadicPrefix](DyadicPrefix.md)
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeBitSource](ThreeBitSource.md)
