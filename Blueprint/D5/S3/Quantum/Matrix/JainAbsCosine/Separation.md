# Separation of Fourier representatives

## Abstract

Strict separation of nonzero absolute cosine Fourier modes.

**Theorem 1.1 (Strictly largest constant mode).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/Separation.modeValue_lt_top`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/Separation.modeValue_lt_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural m, every natural j between one and m, and every real exponent r, mode j is strictly smaller than mode zero. Each difference summand is nonnegative. The first is strictly positive because its cosine phase lies strictly between zero and pi and its power base is positive.

**Theorem 1.2 (Distinct representatives of nonzero modes).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/Separation.modeValue_injective_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/Separation.modeValue_injective_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real exponent r, representatives with indices between one and m that agree at a nonzero value have equal indices. The exact mode and gap signs reduce the comparison to the root products P(j)=product of r-2s for s less than j. Between two indices with equal nonzero sign, one can advance by one index when r exceeds twice the current index, and by two indices otherwise. Equality at that threshold would force the target root product to vanish. The signs of the corresponding gaps give strict ordering along the resulting finite chain. This argument applies to negative exponents as well as to the nonnegative range of the multiplicity claim.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/Separation.modeValue_injective_nonzero`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/Separation.modeValue_lt_top`
- Dependency: [D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns](GapSigns.md)
