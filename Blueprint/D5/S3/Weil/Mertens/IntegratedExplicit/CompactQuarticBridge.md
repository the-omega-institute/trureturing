# An exact finite arithmetic test

## Abstract

Quartic Riemann hypothesis criteria for tail LCMs and compact factorial gcds

**Theorem 1.1 (Exact logarithm of the tail LCM product).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.log_tailLCM_eq_sum_vonMangoldt`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.log_tailLCM_eq_sum_vonMangoldt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive M and natural N, put H=MN. Expand the logarithm of each prefix LCM as the Chebyshev psi sum. The incidence a*k<=H with M<k<=H and 1<=a<=N is equivalent to k<=floor(H/a), so exchanging the two finite sums gives the Mangoldt weight floor(H/a)-M.

**Definition 1.2 (Centered normalized tail logarithm).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.D`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Divide the log tail product at H=MN by M and subtract N log N minus (1+EulerMascheroniConstant)N.

**Theorem 1.3 (Explicit one-sided floor error).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.U_sub_D_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.U_sub_D_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract the centered tail logarithm from CompleteMertensPeak.U(N). The exact difference is the sum of the Mangoldt weights times MN/a-floor(MN/a), divided by M. Each floor error is in [0,1), yielding the nonnegative upper bound psi(N)/M.

**Theorem 1.4 (Cofinal quartic blocks for the tail LCM).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_tailLCM_quartic_integer_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_tailLCM_quartic_integer_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At N=n^4 and M=n^2 the floor error is at most (log 4+4)n^2. For each positive exponent loss and natural threshold, choose a smaller positive loss and a block sufficiently far out to absorb the error. The original quartic integer-block criterion then transfers in both directions.

**Theorem 1.5 (Eventual fixed-constant criterion).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_tailLCM_quartic_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_tailLCM_quartic_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH supplies the eventual quadratic bound with constant one. Conversely any eventual fixed real multiple of n^2 is absorbed into each positive quartic power loss on all sufficiently large blocks.

**Theorem 1.6 (A sufficient fixed constant above the first Li mass).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_tailLCM_quartic_of_mass_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_tailLCM_quartic_of_mass_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every constant C strictly above firstLiMass, the sharp actual envelope under RH bounds U(n^4)/n^2 eventually by C via y=4 log n. The nonnegative rounding error transfers this bound to the tail. The fixed-constant criterion gives the converse.

**Definition 1.7 (The compact gcd at the fourth-power scale).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.quarticFactorialGcd`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.quarticFactorialGcd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set M=n^2, N=n^4, r=M+1 and s=M(M-1). The gcd is the gcd of selbergFactorial(r,s,b) for 0<=b<=floor(s/r), where each term is the product over j=1,...,r of (jb)!/b! times (s-(r-j)b)!.

**Theorem 1.8 (Quadratic family size).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.quarticFactorialGcd_family_size`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.quarticFactorialGcd_family_size` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n, the number of admissible integer parameters is at most n^2 because M(M-1)<M(M+1).

**Definition 1.9 (Centered normalized compact gcd logarithm).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the same real normalization and centering at N=n^4 and M=n^2.

**Theorem 1.10 (Two-sided quantitative comparison with the integrated remainder).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD_U_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD_U_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact degree identity rs+r-1=M^3 gives the tail product at H=MN with no padding. The compact factorial theorem bounds the gcd between the tail and the tail times B!, where B=2(M+1)^2. The logarithmic gap after division by M is between zero and B log B/M. For n>=2, B<=8n^4 and log B<=7 log n. Combining with the floor bound places the compact centered remainder minus U(n^4) between -(log 4+4)n^2 and 56n^2 log n.

**Theorem 1.11 (RH equivalence for the explicit compact factorial family).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_compact_factorial_gcd_quartic_integer_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_compact_factorial_gcd_quartic_integer_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real kappa and natural A there must exist k>=max(A,2) such that every integer n in [k^3,k^4] satisfies the centered log gcd bound (n^4)^(1/2+kappa). The gcd ranges over the explicit factorial family with r=n^2+1 and s=n^2(n^2-1). The quantitative error in either direction is eventually absorbed by any positive quartic power loss. Choose the threshold for this absorption before selecting the block at half the requested loss. The canonical quartic criterion gives the equivalence.

**Theorem 1.12 (Explicit square-root scale comparison).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD_U_quadratic_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD_U_quadratic_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At n>=3 divide the logarithmic gcd excess by M=n^2. The bound 11(log 4+4)(M+1)^2/M is at most 18(log 4+4)M. The one-sided tail rounding bound gives the lower error -(log 4+4)M and preserves the upper bound.

**Theorem 1.13 (RH equivalence with a prescribed constant).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_compact_factorial_gcd`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_compact_factorial_gcd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH the eventual upper bound U(n^4)<n^2 yields compactD(n)<=(1+18(log 4+4))n^2. In the reverse direction tail divisibility transfers the same eventual bound to the centered tail logarithm. The tail LCM criterion gives RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.D`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.U_sub_D_bounds`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD_U_bounds`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.compactD_U_quadratic_bounds`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.log_tailLCM_eq_sum_vonMangoldt`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.quarticFactorialGcd`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.quarticFactorialGcd_family_size`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_compact_factorial_gcd_quartic_integer_blocks`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_compact_factorial_gcd`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_tailLCM_quartic_constant`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_eventually_tailLCM_quartic_of_mass_lt`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge.rh_iff_tailLCM_quartic_integer_blocks`
- Dependency: [D5/S3/Arith/FactorialRatio/CompactFactorialGcd](../../../Arith/FactorialRatio/CompactFactorialGcd.md)
- Dependency: [D5/S3/Arith/FactorialRatio/QuarticCompactLog](../../../Arith/FactorialRatio/QuarticCompactLog.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling](QuarticSampling.md)
