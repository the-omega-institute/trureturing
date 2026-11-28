# The three-adic transient of cubic Lucas blocks

## Abstract

The native cubic Lucas trajectory at three is an exact transient toward the fixed residue one.

**Theorem 1.1 (Exactly one digit of convergence at each step).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_depth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The valuation of the level-i block minus one is exactly i+1, including the initial level i=0. The shifted recurrence factors into the current deviation and a multiplier of valuation one.

**Theorem 1.2 (The earlier level controls the entire lag valuation).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_lag`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_lag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference between levels n and m, for n>m, has valuation m+1. This depends on where the two readings start, not on the lag.

**Theorem 1.3 (Exact pairwise collisions in the finite transient).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_clamped_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_clamped_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At precision a, two levels collide exactly when their indices agree after clamping at a-1. Every earlier residue is distinct, and every later residue is one.

**Theorem 1.4 (No positive period through the initial reading at nontrivial precision).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_no_initial_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_no_initial_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At precision greater than one, no positive shift preserves all readings starting at level zero. The eventual fixed tail is distinct from periodicity of the entire trajectory.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_clamped_phase`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_depth`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_lag`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic.cubicBlock_three_no_initial_period`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
