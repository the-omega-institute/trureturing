# Twelve-Scale Reduction

## Abstract

Derive the exact twelve-scale floor from a rational sample's continued fraction.

This module extracts a rational sample's finite simple continued fraction with Mathlib's Euclidean algorithm, applies the Barkan-Hickerson-Knuth odd-length terminal convention, and derives the normalization denominator as the largest extracted partial quotient. It does not supply the 2958-case or minimum-attainment certificates, does not identify the moat, envelope, or diffusion readings with the normalized finite-sample minimum, and does not reconstruct the historical sampling configuration or its leakage.

**Theorem 1.1 (Canonical partial quotients are empty or odd in length).**

$$\forall q\in\mathbb{Q},\ C(q)=\varnothing\ \lor\ |C(q)|\equiv1\mod2$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.canonical_partial_quotients_empty_or_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integral rational has no fractional partial quotients. Every nonempty extracted sequence has odd length after the unique terminal rewrite used by the Barkan-Hickerson-Knuth convention.

**Theorem 1.2 (Canonical extraction reconstructs the rational sample).**

$$\forall q\in\mathbb{Q},\ [\lfloor q\rfloor;C(q)]=q$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.canonical_continued_fraction_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extracted finite continued fraction evaluates exactly to its input rational. The proof connects the finite coefficient list back to Mathlib's GenContFract.of computation and proves that the odd-length terminal rewrite preserves the value.

**Theorem 1.3 (Nonzero multiples of twelve obey the normalized floor).**

$$\forall q\in\mathbb{Q},\ \forall\psi\in\mathbb{Z},\ (A(q)>0\land12\mid\psi\land\psi\neq0)\Rightarrow\frac{12}{A(q)}\leq\frac{|\psi|}{A(q)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero integer divisible by twelve has absolute value at least twelve. Dividing by the positive maximum partial quotient extracted from the rational sample preserves the inequality.

**Theorem 1.4 (The normalized floor equality detects absolute value twelve).**

$$\forall q\in\mathbb{Q},\ \forall\psi\in\mathbb{Z},\ A(q)>0\Rightarrow\left(\frac{|\psi|}{A(q)}=\frac{12}{A(q)}\Leftrightarrow|\psi|=12\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive extracted maximum partial quotient, cancellation shows that the normalized magnitude equals twelve over that quotient exactly when the integer magnitude is twelve. The theorem does not produce such a sample member.

**Theorem 1.5 (A witnessed finite sample has exact twelve-scale minimum).**

$$\forall q\in\mathbb{Q},\ \forall S\subset_{\mathrm{fin}}\mathbb{Z},\ A(q)>0\land(\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)\land(\exists\psi_0\in S,\ |\psi_0|=12)\Rightarrow\min\left\{\frac{|\psi|}{A(q)}:\psi\in S\right\}=\frac{12}{A(q)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every member of a finite integer sample is a nonzero multiple of twelve and one supplied member has magnitude twelve, then twelve over the rational sample's positive maximum partial quotient is a member and lower bound of the normalized sample. The enumeration and witness remain explicit premises.

**Theorem 1.6 (A normalized finite-sample minimum is unique).**

$$\forall x,y\in N_q(S),\ ((\forall z\in N_q(S),\ x\leq z)\land(\forall z\in N_q(S),\ y\leq z))\Rightarrow x=y$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two normalized sample members that are each no greater than every member are equal by antisymmetry. This order-theoretic uniqueness does not identify any other statistical reading with the sample minimum.

**Theorem 1.7 (The normalized sample floor uses the extracted maximum partial quotient).**

$$\forall q\in\mathbb{Q},\ \forall S\subset_{\mathrm{fin}}\mathbb{Z},\ A(q)>0\land(\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)\land(\exists\psi_0\in S,\ |\psi_0|=12)\Rightarrow\min\left\{\frac{|\psi|}{A(q)}:\psi\in S\right\}=\frac{12}{A(q)},\qquad A(q)=\max C(q)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/TwelveScaleReduction.normalized_sample_floor_eq_twelve_over_maximum_partial_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the explicit divisibility, nonzero, attainment, and derived-maximum positivity premises, the actual Finset minimum of the normalized sample equals twelve divided by the largest partial quotient extracted from the rational sample. No independent scale parameter remains.
