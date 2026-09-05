# Odious Majority on the Six-Bit Dyadic Slice

## Abstract

An exact 21-state transfer certificate proves the Shevelev odious-majority inequality on every cutoff 2^(6k) with k >= 1

**Definition 1.1 (The residue index type).**

$$Ix = \operatorname{Fin}(21)$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.Ix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ix consists of the natural numbers from 0 through 20. Arithmetic in Ix is reduced modulo 21.

**Definition 1.2 (The standard residue columns).**

$$\forall i, j \in Ix, e_{j}(i) = \text{if} (i = j) \text{then} 1 \text{else} 0$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.basis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column e_j denotes basis(j); its coordinates are integers.

**Definition 1.3 (The signed binary transfer matrix).**

$$\begin{aligned}\forall i, j \in Ix,\\T_{ij} = (\text{if} (i = 2 j) \text{then} 1 \text{else} 0) - (\text{if} (i = 2 j + 1) \text{then} 1 \text{else} 0)\end{aligned}$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T is an integer matrix indexed by Ix in both coordinates. The conditions use arithmetic in Fin 21, including reduction of 2j and 2j+1.

**Definition 1.4 (The least natural remainder).**

$$\forall m \in \mathbb{N}, \operatorname{residue}(m) = m \bmod 21$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

residue(m) is the least natural remainder modulo 21, represented in Ix with the proof that it is less than 21.

**Definition 1.5 (The signed residue state).**

$$\forall n \in \mathbb{N}, v_{n} = \sum_{m \in \operatorname{range}(2^{n})} (-1)^{\operatorname{count}(\operatorname{bits}(m), \mathrm{true})} \cdot e_{\operatorname{residue}(m)}$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.state` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector v_n denotes state(n). Here bits(m) is Nat.bits(m), and count(bits(m),true) is the number of true entries in that list. The integer sign multiplies the standard column at residue(m).

**Definition 1.6 (The eligible selector row).**

$$\forall i \in Ix, \ell_{i} = \text{if} (i = 7 \lor i = 14) \text{then} 1 \text{else} 0$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.ell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer row ell selects coordinates 7 and 14.

**Definition 1.7 (The six-bit block matrix).**

$$A = T^{6}$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A is the sixth matrix power of T over the integers.

**Definition 1.8 (The signed eligible difference).**

$$\forall k \in \mathbb{N}, D_{k} = \sum_{m \in \operatorname{range}(2^{6 k})} (\text{if} ((7 \mid m \land \neg (3 \mid m))) \text{then} (-1)^{\operatorname{count}(\operatorname{bits}(m), \mathrm{true})} \text{else} 0)$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D_k denotes D(k). The finite integer sum includes exactly natural numbers below 2^(6k) divisible by 7 and not by 3, with sign given by the count of true entries in Nat.bits(m).

**Definition 1.9 (The eligible odious count).**

$$\begin{aligned}\forall k \in \mathbb{N},\\\operatorname{odiousCount}(k) = \operatorname{card}(\operatorname{filter}(\operatorname{range}(2^{6 k}), m \mapsto ((7 \mid m \land \neg (3 \mid m)) \land \operatorname{Odd}(\operatorname{count}(\operatorname{bits}(m), \mathrm{true})))))\end{aligned}$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.odiousCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural cardinality counts the filtered Finset.range. Odd tests the number of true entries in Nat.bits(m).

**Definition 1.10 (The eligible evil count).**

$$\begin{aligned}\forall k \in \mathbb{N},\\\operatorname{evilCount}(k) = \operatorname{card}(\operatorname{filter}(\operatorname{range}(2^{6 k}), m \mapsto ((7 \mid m \land \neg (3 \mid m)) \land \operatorname{Even}(\operatorname{count}(\operatorname{bits}(m), \mathrm{true})))))\end{aligned}$$

*Formalization.* `D5/S1/Digit/OdiousMajorityDyadicSlice.evilCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural cardinality counts the filtered Finset.range. Even tests the number of true entries in Nat.bits(m).

**Theorem 1.11 (Signed residue counts obey the 21-state transfer).**

$$\begin{aligned}\forall n \in \mathbb{N},\\v_{n+1} = T v_{n} \land v_{n} = T^{n} e_{0}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OdiousMajorityDyadicSlice.state_eq_transfer_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state v_n records the signed popcount sum in each residue class modulo 21. Splitting the next binary range into even and odd integers transports the two residues to 2r and 2r+1 with opposite signs.

The proof uses Nat.bit0_bits and Nat.bit1_bits on the live path, then iterates the one-bit equality from the standard vector e_0.

**Theorem 1.12 (Eligibility and the six-bit block coefficient agree exactly).**

$$\begin{aligned}(\forall m \in \mathbb{N}, (7 \mid m \land \neg 3 \mid m) \iff (\operatorname{residue}(m) = 7 \lor \operatorname{residue}(m) = 14))\\\land (\forall k \in \mathbb{N}, D_{k} = \ell \cdot (A^{k} e_{0})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OdiousMajorityDyadicSlice.eligibility_iff_residue_and_D_eq_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divisibility by 7 and nondivisibility by 3 select exactly residues 7 and 14 modulo 21. The selector row ell therefore turns the state at time 6k into the signed eligible difference D_k.

The block matrix is A=T^6. This theorem packages both universal clauses of PZG candidate theorem 6.218 in one addressable declaration.

**Theorem 1.13 (The exact annihilator yields a third-order recurrence).**

$$\begin{aligned}\ell \cdot A \cdot (A^{3} - 19 A^{2} - 209 A - 189 I) = 0\\\land D_{1} = -6 \land D_{2} = -42 \land D_{3} = -2070\\\land (\forall k \in \mathbb{N}, k \geq 1 \implies D_{k+3} = 19 D_{k+2} + 209 D_{k+1} + 189 D_{k}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OdiousMajorityDyadicSlice.annihilating_identity_and_D_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordinary kernel decision checks all 21 coordinates of the row certificate. Matrix algebra then gives the displayed annihilator and propagates it to every row after the first.

The values D_1=-6 and D_2=-42 are decided directly over 64 and 4096 terms respectively; D_3=-2070 is decided through the matrix model.

**Theorem 1.14 (Odious integers dominate for every k >= 1).**

$$\begin{aligned}\forall k \in \mathbb{N},\\k \geq 1 \implies (D_{k} < 0 \land \operatorname{evilCount}(k) < \operatorname{odiousCount}(k)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OdiousMajorityDyadicSlice.D_negative` (`✓ std3`). ∎

*Citation.* Vladimir Shevelev (2008). *Generalized Newman Phenomena and Digit Conjectures on Primes*. DOI: [10.1155/2008/908045](https://doi.org/10.1155/2008/908045).

*Commentary.*

Strong induction uses the three negative initial values and the positive recurrence coefficients 19, 209, and 189 to keep D_k strictly negative.

A separate finite-sum induction identifies D_k with evilCount(k) minus odiousCount(k), so negativity gives the strict counting inequality.

This proves only the infinite slice n=2^(6k) with k >= 1. It does not claim the all-prefix Shevelev conjecture.

## References

- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.A`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.D`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.D_negative`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.Ix`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.T`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.annihilating_identity_and_D_recurrence`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.basis`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.eligibility_iff_residue_and_D_eq_transfer`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.ell`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.evilCount`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.odiousCount`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.residue`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.state`
- Truth anchor: `D5/S1/Digit/OdiousMajorityDyadicSlice.state_eq_transfer_pow`
