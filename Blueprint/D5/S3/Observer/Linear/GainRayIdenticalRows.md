# Identical-row worlds and complete suffix annihilation

## Abstract

Identical-row worlds and complete suffix annihilation

For a chronological Bool word w, false denotes M and true denotes J. rowCoordinates(w) is acquisition(w) applied to the column (1,1). At each initial-inclusive clock i, rowBase(w)(i) is its first coordinate for take i w; rowSlope(w)(i) is the second coordinate minus the first. Both coordinates are positive. They are both one until M occurs, and are unequal at every subsequent clock.

The matrix M sends (u,v) to (v,u+v), and J interchanges the coordinates. Positivity therefore prevents equality from returning after the first M. Every tail is allowed, including the empty tail. The suffix starts at the first M read, rather than at the following read.

rowMap(d,w,C,f) maps the ordinary coefficient vector beta to C applied to the vector f(i) times gain(d,beta)(i), at the consecutive original natural clocks. RowUniversallyCollinear(d,w,C) means that for every legal identical-row parameter 0<theta<1, every nonzero whole coefficient vector beta:Fin(d+1) to the reals, and every real drift delta, C applied to the actual readings of rowWorld is a real scalar multiple of beta. Zero scalar is allowed in this hypothesis.

**Theorem 1.1 (Native affine trace formula).**

Lean statement: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word w and real theta, trace(acquisition(w) identicalRow(theta)) equals rowCoordinates(w)(0) plus theta times (rowCoordinates(w)(1)-rowCoordinates(w)(0)). The equality holds algebraically for all theta; rowWorld uses its legal subdomain 0<theta<1.

**Theorem 1.2 (Exact support at every original clock).**

Lean statement: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_slope_support`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_slope_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word w and i:Fin(length(w)+1), rowSlope(w)(i) is nonzero if and only if false belongs to take i w. The initial slope is zero, and every pure-J read has zero slope.

**Theorem 1.3 (The entire suffix after the first M).**

Lean statement: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_entire_suffix`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_entire_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, every Bool tail and every initial-inclusive clock i of w=J repeated k followed by M followed by tail, rowSlope(w)(i) is nonzero exactly when k<i. Thus the first M is at clock n=k+1, and precisely the clocks n through N-1 have nonzero slope, where N=length(w)+1.

**Theorem 1.4 (Drift cancellation and both scalar coefficients).**

Lean statement: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_scalar_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_scalar_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d>=1, word w, fixed readout matrix C and RowUniversallyCollinear(d,w,C), C times the all-one read vector is zero. There are real lam0 and lam1 such that rowMap(d,w,C,rowBase(w)) is lam0 times the identity linear map and rowMap(d,w,C,rowSlope(w)) is lam1 times that identity. Consequently the full coefficient map at theta is (lam0+theta lam1) times the identity. The drift argument uses two different coefficient axes, and two parameters in the open interval separate the affine coefficients.

**Theorem 1.5 (Pure J and no-action annihilation).**

Lean statement: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_pureJ_annihilation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_pureJ_annihilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1, word w containing no false atom, fixed C and RowUniversallyCollinear(d,w,C), C annihilates the all-one read vector, and both rowMap(d,w,C,rowBase(w)) and rowMap(d,w,C,rowSlope(w)) are zero. There is no length restriction on this pure-J case, and the empty action word is included.

**Theorem 1.6 (Every short-suffix column vanishes).**

Lean statement: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_suffix_annihilation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_suffix_annihilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d>=1, k be any natural number, tail any Bool word, w=J repeated k followed by M followed by tail, and r=length(tail)+1<d+1. For every fixed C with RowUniversallyCollinear(d,w,C), C times the all-one read vector is zero; C(a,i)=0 for every output coordinate a and every clock i with k<i; and both its base and slope rowMaps are zero. The strict inequality r<m is used with m=d+1. A nonzero slope scalar would make evaluation at the r suffix clocks injective on m coefficients, contrary to dimension. Surjective evaluation at those same clocks then isolates and annihilates each suffix column. The constant coefficient vector and drift cancellation annihilate the remaining base scalar.

**Theorem 1.7 (Universal collinearity cannot succeed anywhere).**

Lean statement: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_annihilation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_annihilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1, word w, fixed matrix C with RowUniversallyCollinear(d,w,C), suppose either false is absent from w or there exist k and tail with w=J repeated k followed by M followed by tail and length(tail)+1<d+1. Then for every legal 0<theta<1, every nonzero beta:Coeff d and every real drift delta, C applied to the actual readings of rowWorld(d,theta,beta,delta) is zero and Succeeds(rowWorld,w,C) is false. This includes every legal continuation of every allowed short suffix. The gain may have any actual degree at most d, either coefficient signs and sampled roots; success requires a nonzero scalar of either sign.

**Theorem 1.8 (Exact original identical-row observation vector).**

Lean statement: `D5/S3/Observer/Linear/GainRayIdenticalRows.row_readings_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayIdenticalRows.row_readings_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual read at each original clock is its whole gain sample times rowBase plus theta times rowSlope, with the arbitrary constant drift added.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_annihilation`
- Truth anchor: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_entire_suffix`
- Truth anchor: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_pureJ_annihilation`
- Truth anchor: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_scalar_identity`
- Truth anchor: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_slope_support`
- Truth anchor: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_suffix_annihilation`
- Truth anchor: `D5/S3/Observer/Linear/GainRayIdenticalRows.identical_row_trace`
- Truth anchor: `D5/S3/Observer/Linear/GainRayIdenticalRows.row_readings_affine`
- Dependency: [D5/S3/Observer/Linear/GainRayHistory](GainRayHistory.md)
