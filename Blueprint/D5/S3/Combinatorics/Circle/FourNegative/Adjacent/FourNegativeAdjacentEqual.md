# Physical source and prefix support

## Abstract

The repeated diagonal source and its first ear

The private diagonal proof handles r=s=n>=2 using the existing ThreeRowSource.repeated_source theorem at base length n, four physical copies and seed one. Its geometric multiplier is D=1+2^n+2^(2n)+2^(3n), with N=(2^n-1)D. The formula retains each physical label i and reduces only its numerical readout to the residue i mod n. Neither minimal numerical period nor source injectivity is asserted.

Put q=2^(n-1) and H=(q-1)D. In the natural physical order, each of the four blocks has the complete positive ladder of mass H followed by its actual value -H. Positive-block monotonicity and concatenation give every old prefix in [0,H] and exact total zero. Since 2H+D=N, this is the narrower strip needed by the first-ear inference. A coarser universal source-width bound would not supply this equality.

The private first_ear inference uses the existing digit_data and charge_sum for the actual two source lengths. For k>=2 and a natural seed t<=2^(k-1)-1, any old permutation with nonnegative prefixes bounded by H, zero total and 2H+t<=N, the old-label new increment is 2f_i-q_i, every charge is nonnegative, all charges sum to t and the literal fresh label has value t. With the ear at cut zero, every nonempty new prefix is 2S+t-Q with 0<=Q<=t; the empty prefix is zero. It lies in [0,N], the new total is zero and the old strip embeds in [0,N/2]. This deduction uses the literal ear_prefix and ear_perm identities; it does not rotate the physical source.

The private branch endpoint is consumed by FourNegativeAdjacentNearJointLift. It is one branch of the full independent paired-gap target; far-ratio schedules are not consequences of the diagonal proof.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentDoublePhysical](FourNegativeAdjacentDoublePhysical.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeRowSource](../../ThreeRowSource.md)
