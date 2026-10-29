# Same-phase charges across the three moduli

## Abstract

Same-phase charges across the three moduli

**Theorem 1.1 (Native source digits and nonnegative charges).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.digit_data`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.digit_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native binary quotient gives nonnegative charge and the exact old and new source equations in their shared physical phase. Both periodic shortening and dyadic joint transport consume this owner declaration.

**Theorem 1.2 (The native charge total).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.charge_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.charge_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d>=2 and w<2^(d-1), the charge total over all d physical labels is w. The existing zero-sum source theorem and the geometric power sum give this identity. Periodic source equations and the unused-suffix comparison consume it.

**Theorem 1.3 (The exact dyadic seam charge).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.native_charge_alignment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.native_charge_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b=2^h*a<2^(d-1), a>=1, and tau=(finRotate d)^h, the old values agree after relabelling. At j=tau(i), the b charge equals the a charge plus 2^j*a when j<h, and equals it otherwise. The proof separates wrapped and unwrapped physical exponents and uses the owned digit equations and centered uniqueness. RunFirstEarTransport consumes both conclusions in its same-cut two-source construction; no charge domination is assumed.

**Theorem 1.4 (Geometric quotient as the shared finite sum).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric quotient is bound to the existing GeometricSourceRelocation.geometric_quotient. The subsequent multiplication and recurrence calculations consume this equality.

**Theorem 1.5 (The geometric multiplication identity).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared finite geometric sum gives (q-1)*G_r=q^r-1. The cross-modulus range proof and final strict-span calculation consume it.

**Theorem 1.6 (The geometric block recurrence).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending the last geometric summand gives G_(r+1)=G_r+q^r. Charged block joins and the final source equation consume this recurrence.

**Theorem 1.7 (Monotone geometric block heights).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d>=1, the geometric quotients increase with the block count. The physical candidate range and all early-block strips consume this order bound.

**Theorem 1.8 (Same-phase charges across the three moduli).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.periodic_source_equations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.periodic_source_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d>=2, w<=2^(d-1)-1 and m>=2, set q=2^d, G=G_m and f(r,i)=2^i*w*G_r+e(i). The original physical value at exponent r*d+i+1 is exactly 2*G*a(i)-f(r,i); at the last block it is R*y(i+1)+H*a(i). The phase i is shared by a, y, e and f. Every e is nonnegative and its total is w; each block correction has total w*q^r. The label zero retains value w*G. No unit, injectivity of values or least-period premise is used.

The charge is obtained from the binary prefix quotient of w. Centered uniqueness identifies the actual sources after both range and modular equality are proved. To certify every original block, the proof writes its candidate as q^r*y+K*a with K=2G-G_r-2q^r>=0, using both smaller centered ranges on the same phase. ZeroSumSubsets.source_cycle supplies the existing base total; the geometric quotient is reused at its original owner.

This is a repository derivation of the conditional periodic-shortening construction. The source problem is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, Conjecture 3.1. No literature novelty or solution of its general aperiodic case is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.charge_sum`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.digit_data`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_mono`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_mul`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_succ`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_sum`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.native_charge_alignment`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.periodic_source_equations`
- Dependency: [D5/S3/Combinatorics/Circle/GeometricSourceRelocation](GeometricSourceRelocation.md)
- Dependency: [D5/S3/Combinatorics/Circle/TwoRunSource](TwoRunSource.md)
- Dependency: [D5/S3/Combinatorics/Circle/ZeroSumSubsets](ZeroSumSubsets.md)
