# Conjectural moments on polynomial bands

## Abstract

Conjectural prime moments on integer lengths imply uniform second moments and fourth bounds on polynomial bands.

Montgomery and Soundararajan, Primes in short intervals, Communications in Mathematical Physics 252 (2004), 589–617, Conjecture 1, is used as a hypothesis for orders two and four. The consequences for floored polynomial bands are derived here. No prime moment conjecture is asserted unconditionally.

**Definition 1.1 (The two conjectural moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.MSConjectureTwoFour`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.MSConjectureTwoFour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each k equal to two or four, every fixed positive epsilon and eta admit an integer cutoff beyond which every integer H with (log N)^(1+epsilon)<=H<=N^(1-epsilon) satisfies |M_k(N;H)-mu_k N (H log(N/H))^(k/2)|<=eta N (H log(N/H))^(k/2). Here mu_2=1 and mu_4=3, and M_k sums the kth powers of psi(n+H)-psi(n)-H for 1<=n<=N.

**Theorem 1.2 (The conjectural range after flooring).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_band_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_band_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<alpha<beta<1 there is epsilon>0 such that, for all sufficiently large real Y and every Y^alpha<=v<=Y^beta, the natural floors N and H satisfy N>=2, H>=1, (log N)^(1+epsilon)<=H<=N^(1-epsilon), and H<=N. Polynomial growth dominates the logarithmic lower endpoint, while floor_power_upper from the shared single-length band geometry applies the strict upper exponent margin to absorb rounding of Y.

**Theorem 1.3 (Uniform discrete variance).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_discrete_second_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_discrete_second_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the two conjectural moments and fix 0<alpha<beta<1. For every eta>0, eventually uniformly over Y^alpha<=v<=Y^beta, the second discrete moment at the natural floors of Y and v differs from Y v log(Y/v) by at most eta Y v log(Y/v). Rounding the leading term costs at most 4 Y log Y; dividing by the band normalizer makes this error vanish.

**Theorem 1.4 (Uniform discrete fourth bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_discrete_fourth_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_discrete_fourth_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same conjecture and exponent conditions, there exists A>=1 such that eventually M_4(floor Y;floor v)<=A Y v^2 (log Y)^2 uniformly over the band. The proof takes A=4: relative conjectural error one adds to the Gaussian coefficient three, and flooring only decreases each factor in this upper bound.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.MSConjectureTwoFour`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_band_geometry`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_discrete_fourth_upper`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand.conjecture_discrete_second_uniform`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry](SingleLengthBandGeometry.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms](SingleLengthMainTerms.md)
