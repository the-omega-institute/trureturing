# A complete inventory with terminal order W, X, U, V

## Abstract

Actual physical banks and their paired source sums

For natural a,b,c,d>=2, the U,V,W,X chains start at 0,d,d+c,d+c+b and have lengths d,c,b,a. Given a native partition of the b-1 W-positive indices, the four banks are all U positives; W mask h; W mask m XOR h followed by all X positives; and all V positives followed by W mask low. Their successive terminals are W,X,U,V, with labels d+c+b-1,a+b+c+d-1,d-1,d+c-1.

The internal inventory proof uses the genuine native partition to show that the interleaved word is a permutation of every label in List.range(a+b+c+d). A separate membership proof places every bank occurrence inside the source and outside the four negative terminals. These statements preserve occurrence identity even when source values coincide.

For either the old or enlarged row, let F be its four native chain heads and let C_r=(2^(chainLength_r-1)-1)F_r. The four bank masses are C_0, h F_2, (m XOR h)F_2+C_3, and C_1+low F_2. Each of these eight paired sums is derived from the actual dyadic chain values and chamberLabels weighted sums, rather than from capacities alone. Schedule combines this inventory with the selector and terminal identities to obtain the complete physical orders.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/NativeMasks](NativeMasks.md)
