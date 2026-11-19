# The opposite-gap Nesbitt bound

## Abstract

For 0<X≤Y≤Z with Z/Y ≥ s ≥ 1, the Nesbitt sum is at least s/2+2/(1+s), with equality exactly at X=Y, Z=sY when s>1.

**Theorem 1.1 (Nesbitt sum with a large top gap).**

Lean statement: `D5/S3/Arith/Divisors/DimitrovNesbittOppositeGap.opposite_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovNesbittOppositeGap.opposite_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N(X,Y,Z)=X/(Y+Z)+Y/(X+Z)+Z/(X+Y) and G(s)=s/2+2/(1+s). For 0<X≤Y≤Z and 1≤s≤Z/Y, N(X,Y,Z) ≥ G(s); if s>1, equality holds if and only if X=Y and Z=sY. This is the gap direction complementary to the ratio-constrained Nesbitt bound used for S. Dimitrov's Conjectures 2 and 7 (arXiv:2606.12484). Put x=X/Y ≤ 1 and t=Z/Y ≥ s. Then N=x/(1+t)+1/(x+t)+t/(x+1), and N−G(t)=(1−x)C/(2(x+1)(x+t)(1+t)) with C=t(x+t)(1+t)−2(x+1)(x+t−1). Writing t=1+u and x=1−v with u ≥ 0 and 0 ≤ v<1 gives C=u³+(5−v)u²+(4−v)u+v(4−2v) ≥ 0, and C>0 once u>0. Moreover G(t)−G(s)=(t−s)(st+s+t−3)/(2(1+s)(1+t)) ≥ 0, which vanishes for s>1 only at t=s. Hence N ≥ G(t) ≥ G(s), and when s>1 equality forces t=s>1 and then x=1.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovNesbittOppositeGap.opposite_gap`
