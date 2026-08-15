# Pure Shift and the Euler-Sieve Vacuum

## Abstract

Nontrivial arithmetic translations are pure isometries, while simultaneous Euler sieving by all prime addresses leaves exactly the vacuum line.

**Theorem 1.1 (Nontrivial arithmetic shifts have no unitary tail).**

$$\forall u\in \operatorname{PrimeAxisTable},\ u \neq \operatorname{vacuumAddress} \Rightarrow \operatorname{iInf}_{n\in \mathbb{N}} \operatorname{divisibleSubspace}(\operatorname{tablePow}(u, n)) = \operatorname{bot}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/PureShiftVacuum.iInf_divisibleSubspace_tablePow_eq_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The address tablePow u n encodes the n-th power of the positive integer encoding of u. For any fixed coefficient address b, a nontrivial base power eventually exceeds b and therefore cannot divide it. Membership in every divisible subspace consequently forces every coefficient to vanish, so the common tail is the zero subspace.

**Theorem 1.2 (The Euler sieve leaves exactly the vacuum line).**

$$\operatorname{iInf}_{p\in \operatorname{NatPrimes}} (\operatorname{divisibleSubspace}(\operatorname{primeAddress}(p)))^{\perp} = \mathbb{C} \cdot \operatorname{vacuumKet}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/PureShiftVacuum.iInf_orthogonal_divisibleSubspace_primeAddress_eq_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coefficient family in every prime wandering complement vanishes at each non-vacuum address: the positive integer encoded by that address has a prime divisor, and the corresponding orthogonal-complement condition kills the coefficient. The address one has no prime divisor, so its ket survives every sieve and spans the entire intersection.

## References

- Truth anchor: `D5/S3/Zeros/NicaCovariance/PureShiftVacuum.iInf_divisibleSubspace_tablePow_eq_bot`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/PureShiftVacuum.iInf_orthogonal_divisibleSubspace_primeAddress_eq_vacuum`
- Dependency: [D5/S3/Zeros/NicaCovariance/DoubleCommutation](DoubleCommutation.md)
- Dependency: [D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder](QuasiLatticeOrder.md)
- Dependency: [D5/S3/Zeros/NicaCovariance/SemigroupRelations](SemigroupRelations.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint](../ShiftOperators/BackwardShiftAdjoint.md)
