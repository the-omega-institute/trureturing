# Finite Ramanujan sums

## Abstract

Prime power values and multiplicativity of finite Ramanujan sums.

**Theorem 1.1 (Ramanujan sums at prime powers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_prime_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and natural j and k, c_(p^(k+1))(j) is p^(k+1) times the indicator that p^(k+1) divides j, minus p^k times the indicator that p^k divides j. The equality holds in the complex numbers.

**Theorem 1.2 (Multiplicativity of Ramanujan sums).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_multiplicative`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_multiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For coprime natural moduli m and n and every natural argument j, c_(mn)(j)=c_m(j)c_n(j) in the complex numbers. The divisor identity and Moebius inversion express this Ramanujan sum as a convolution of multiplicative arithmetic functions.

**Theorem 1.3 (Ramanujan sum at modulus one).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At modulus one the Ramanujan sum equals one for every natural argument.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_multiplicative`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_one`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums.ramanujan_prime_power`
- Dependency: [D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity](../../../../../Analytic/Certified/FiniteRamanujanDivisorIdentity.md)
