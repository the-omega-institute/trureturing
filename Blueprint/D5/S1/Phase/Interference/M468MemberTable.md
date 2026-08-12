# M468 Member Table

## Abstract

The phase classifier `Psi mod 24` and the frozen Jacobi selector are independent. The side of a split-prime label is defined from the split-factor value `J(-384 | p)` in the frozen selector factorization, using the m468 datum `beta = -384`; the checked labels are `J(-384 | 7) = 1` and `J(-384 | 67) = -1`. The finite m468 phase-member table contains only the prime labels and residue classes, and does not assume those Jacobi values.

**Theorem 1.1 (Frozen selector side characterization).**

For every phase member `(p, Psi)` of the m468 relation,

$$
\operatorname{sameSide}(p,\Psi) \Longleftrightarrow \Psi \bmod 24=0,
\qquad
\operatorname{differentSide}(p,\Psi) \Longleftrightarrow \Psi \bmod 24=12.
$$

Here `sameSide` and `differentSide` are computed from the frozen Jacobi factor `J(-384 | p)`, not defined from the residue classifier or supplied by the member premise. The two selector values are kernel-checked at `p = 7` and `p = 67`.

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/M468MemberTable.m468_split_prime_characterization` (`std3`). ∎

**Theorem 1.2 (Zero-only selector column).**

Define `zeroOnly_468` by requiring `J(-384 | p) = 0` for every proper prime divisor `p` of `469`. Then

$$
\operatorname{zeroOnly}_{468}\Longleftrightarrow \operatorname{Prime}(469),
\qquad
469=7\cdot67,
\qquad
\neg\operatorname{zeroOnly}_{468}.
$$

The proper divisor `7` is prime, divides `469`, is neither `1` nor `469`, and has selector value `J(-384 | 7) = 1`; this is the explicit anti-vacuity witness.

*Proof.* Machine-checked in Lean as `m468_zero_only_iff_successor_prime`, `m468_successor_factorization`, `m468_zero_only_anti_vacuity_witness`, and `m468_zero_only_fails` (`std3`). ∎

## Scope

This companion does not claim a literal 24-row coordinate enumeration. It also omits the m-side bystander clause and the 1729 three-orbit claim: the frozen checkout has no selector semantics for the former and no orbit-to-choice bridge for the latter.

## References

- Truth anchor: `D5/S1/Phase/Interference/M468MemberTable.m468_split_prime_characterization`
- Truth anchor: `D5/S1/Phase/Interference/M468MemberTable.m468_zero_only_fails`
- Dependency: [D5/S1/Phase/SeatTowerArithmetic](../SeatTowerArithmetic.md)
- Dependency: [D5/S1/Phase/Interference/ZolotarevSelector](ZolotarevSelector.md)
