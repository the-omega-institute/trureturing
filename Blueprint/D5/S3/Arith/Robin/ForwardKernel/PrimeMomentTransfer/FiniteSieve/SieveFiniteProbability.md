# Finite residue expectations and fourth norms use the uniform probability measure.

## Abstract

Finite residue expectations and fourth norms use the uniform probability measure.

**Theorem 1.1 (Uniform residue probability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_probability`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalized counting measure on the residues modulo a positive integer has total mass one.

**Theorem 1.2 (Uniform expectation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_expectation_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_expectation_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of a real residue function against normalized counting measure equals its finite sum divided by the modulus.

**Theorem 1.3 (Finite fourth moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_memLp_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_memLp_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real function on the finite residue space belongs to L4 for the uniform probability measure.

**Theorem 1.4 (Fourth norm identification).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_eq_lpNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_eq_lpNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fourth root of the expected fourth absolute power equals the real L4 norm under the uniform residue measure.

**Theorem 1.5 (Nonnegative fourth norm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite fourth norm of every real residue function is nonnegative.

**Theorem 1.6 (Recovering the fourth moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_fourth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fourth power of the finite fourth norm equals the expected fourth absolute power.

**Theorem 1.7 (Fourth norm triangle inequality).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_add_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_add_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fourth norm of the sum of two real residue functions is at most the sum of their fourth norms.

**Theorem 1.8 (Fourth norm homogeneity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by a real constant multiplies the finite fourth norm by the absolute value of that constant.

**Theorem 1.9 (Interval moment coordinates).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_interval_moment_eq_product_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_interval_moment_eq_product_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interval sieve moment equals the expectation of the product of the corresponding interval sums.

**Theorem 1.10 (Interval pairing coordinates).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_interval_defect_eq_wick_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_interval_defect_eq_wick_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interval Wick defect equals the fourth product moment minus its three covariance pairings in residue-function coordinates.

**Theorem 1.11 (Powers of the interval scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_scale_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_scale_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a length at least two, the square root of H log H is positive and its kth power equals (H log H) raised to k divided by two.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_expectation_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_interval_defect_eq_wick_defect`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_interval_moment_eq_product_moment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_memLp_four`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_add_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_eq_lpNorm`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_fourth`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_norm4_smul`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_probability`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.sieve_scale_power`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs](SieveAnalyticDefs.md)
