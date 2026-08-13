# M468 Member Table

## Abstract

The m468 side column is computed by the frozen Jacobi selector; unsupported m-side and 1729 orbit claims are omitted.

The phase classifier and the frozen selector column are separate definitions. The finite phase-member table records only prime labels and residue classes; it does not assume selector values.

**Theorem 1.1 (Frozen selector side characterization).**

$$\forall p \in \mathbb{N},\ \forall Psi \in \mathbb{Z},\ (phaseMember(p,Psi)\Rightarrow (sameSide(p,Psi) \Leftrightarrow Psi \operatorname{mod} 24=0 \land differentSide(p,Psi) \Leftrightarrow Psi \operatorname{mod} 24=12)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/M468MemberTable.m468_split_prime_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The side is defined from the split-factor Jacobi value J(-384 | p) in the frozen selector factorization. The checked selector column is J(-384 | 7) = 1 and J(-384 | 67) = -1; the independent phase-member table then connects those computed values to the two residue classes.

**Theorem 1.2 (Zero-only selector column fails at m468).**

$$\ \neg zeroOnly_{468}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/M468MemberTable.m468_zero_only_fails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero-only means that every proper prime divisor has frozen selector value zero. The equivalence to successor primality is proved separately; 469 = 7 * 67 and the prime divisor 7 with selector value J(-384 | 7) = 1 provides the non-vacuity witness.

Disclosure: the frozen repository surface provides no m-side selector semantics and no three-prime orbit bridge at 1729, so neither claim is asserted here.

## References

- Truth anchor: `D5/S1/Phase/Interference/M468MemberTable.m468_split_prime_characterization`
- Truth anchor: `D5/S1/Phase/Interference/M468MemberTable.m468_zero_only_fails`
- Dependency: [D5/S1/Phase/Interference/ZolotarevSelector](ZolotarevSelector.md)
- Dependency: [D5/S1/Phase/SeatTowerArithmetic](../SeatTowerArithmetic.md)
