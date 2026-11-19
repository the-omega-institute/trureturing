# Physical construction

## Abstract

OR-completed nested W masks

Let E0=D+K-qL,F0=D+A-qL. Choose r1=max(0,ceil(-E0/L)), t=ceil(-F0/L), r2=t OR r1. Finite bitIndices union and its nonnegative intersection prove r2<=t+r1, while the real submask relations prove r1<=r2 and t<=r2. All selectors are strictly below dyadic q. The high block is q*(2^(a-1)-1); M1=high+r1 and M2=high+r2 are nested masks below the actual W capacity. testBit_two_pow_mul_add proves nesting without an assumed allocation.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/PalindromicArithmetic](PalindromicArithmetic.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits](../SecondPeakHighD/LowBits.md)
