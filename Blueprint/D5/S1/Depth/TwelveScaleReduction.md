# Twelve-Scale Reduction

## Abstract

Record partial arithmetic progress toward the unresolved source floor reduction.

This module records four partial arithmetic lemmas toward the unresolved source floor reduction. It does not identify the rational parameter with the largest partial quotient, does not supply the 2958-case or minimum-attainment certificates, does not identify the moat, envelope, or diffusion readings with the normalized finite-sample minimum, and does not reconstruct the historical sampling configuration or its leakage.

**Theorem 1.1 (Nonzero multiples of twelve obey the normalized floor).**

$$\forall \psi\in\mathbb{Z},\ \forall A\in\mathbb{Q}_{>0},\ (12\mid\psi \land \psi\neq0) \Rightarrow \frac{12}{A}\leq\frac{|\psi|}{A}$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero integer divisible by twelve has absolute value at least twelve. Dividing by a positive rational parameter preserves the inequality; no orbit or maximum-partial-quotient interpretation is inferred.

**Theorem 1.2 (The normalized floor equality detects absolute value twelve).**

$$\forall \psi\in\mathbb{Z},\ \forall A\in\mathbb{Q}_{>0},\ \frac{|\psi|}{A}=\frac{12}{A}\Leftrightarrow|\psi|=12$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive denominator, cancellation shows that the normalized magnitude equals twelve over that denominator exactly when the integer magnitude is twelve. The theorem does not produce such a sample member.

**Theorem 1.3 (A witnessed finite sample has exact twelve-scale minimum).**

$$\forall S\subset_{\mathrm{fin}}\mathbb{Z},\ \forall A\in\mathbb{Q}_{>0},\ ((\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)\land(\exists\psi_0\in S,\ |\psi_0|=12))\Rightarrow \min\left\{\frac{|\psi|}{A}:\psi\in S\right\}=\frac{12}{A}$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every member of a finite integer sample is a nonzero multiple of twelve and one supplied member has magnitude twelve, then twelve over the positive parameter is a member and lower bound of the normalized sample. The enumeration and witness remain explicit premises.

**Theorem 1.4 (A normalized finite-sample minimum is unique).**

$$\forall x,y\in N_A(S),\ ((\forall z\in N_A(S),\ x\leq z)\land(\forall z\in N_A(S),\ y\leq z))\Rightarrow x=y$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two normalized sample members that are each no greater than every member are equal by antisymmetry. This order-theoretic uniqueness does not identify any other statistical reading with the sample minimum.

## References

- Truth anchor: `D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff`
- Truth anchor: `D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique`
- Truth anchor: `D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum`
- Truth anchor: `D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude`
- Dependency: [D5/S1/Phase/SeatTowerArithmetic](../Phase/SeatTowerArithmetic.md)
- Dependency: [D5/S1/Phase/ZeroOrbitCongruence](../Phase/ZeroOrbitCongruence.md)
