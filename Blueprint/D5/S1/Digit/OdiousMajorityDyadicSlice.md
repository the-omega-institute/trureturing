# Odious Majority on the Six-Bit Dyadic Slice

## Abstract

An exact 21-state transfer certificate proves the Shevelev odious-majority inequality on every cutoff of the form 2^(6k).

**Theorem 1.1 (Signed residue counts obey the 21-state transfer).**

$$\begin{aligned}\forall n \in \mathbb{N},\\v_{n+1} = T v_{n} \land v_{n} = T^{n} e_{0}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OdiousMajorityDyadicSlice.state_eq_transfer_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state v_n records the signed popcount sum in each residue class modulo 21. Splitting the next binary range into even and odd integers transports the two residues to 2r and 2r+1 with opposite signs.

The proof uses Nat.bit0_bits and Nat.bit1_bits on the live path, then iterates the one-bit equality from the standard vector e_0.

**Theorem 1.2 (Eligibility and the six-bit block coefficient agree exactly).**

$$\begin{aligned}(\forall m \in \mathbb{N}, (7 \mid m \land \neg 3 \mid m) \iff (\operatorname{residue}(m) = 7 \lor \operatorname{residue}(m) = 14)) \land \\(\forall k \in \mathbb{N}, D_{k} = \ell \cdot (A^{k} e_{0})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OdiousMajorityDyadicSlice.eligibility_iff_residue_and_D_eq_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divisibility by 7 and nondivisibility by 3 select exactly residues 7 and 14 modulo 21. The selector row ell therefore turns the state at time 6k into the signed eligible difference D_k.

The block matrix is A=T^6. This theorem packages both universal clauses of PZG candidate theorem 6.218 in one addressable declaration.

**Theorem 1.3 (The exact annihilator yields a third-order recurrence).**

$$\begin{aligned}\ell \cdot A \cdot (A^{3} - 19 A^{2} - 209 A - 189 I) = 0 \land \\D_{1} = -6,\quad D_{2} = -42,\quad D_{3} = -2070 \land \\\forall k \in \mathbb{N}, k \geq 1 \implies D_{k+3} = 19 D_{k+2} + 209 D_{k+1} + 189 D_{k}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OdiousMajorityDyadicSlice.annihilating_identity_and_D_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordinary kernel decision checks all 21 coordinates of the row certificate. Matrix algebra then gives the displayed annihilator and propagates it to every row after the first.

The values D_1=-6 and D_2=-42 are decided directly over 64 and 4096 terms respectively; D_3=-2070 is decided through the matrix model.

**Theorem 1.4 (Odious integers dominate on every six-bit dyadic cutoff).**

$$\begin{aligned}\forall k \in \mathbb{N}, k \geq 1,\\D_{k} < 0 \land \operatorname{evilCount}(k) < \operatorname{odiousCount}(k).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OdiousMajorityDyadicSlice.D_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction uses the three negative initial values and the positive recurrence coefficients 19, 209, and 189 to keep D_k strictly negative.

A separate finite-sum induction identifies D_k with evilCount(k) minus odiousCount(k), so negativity gives the strict counting inequality.

This proves only the infinite slice n=2^(6k). It does not claim the all-prefix Shevelev conjecture.

## References

- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.D_negative`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.annihilating_identity_and_D_recurrence`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.eligibility_iff_residue_and_D_eq_transfer`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.state_eq_transfer_pow`
