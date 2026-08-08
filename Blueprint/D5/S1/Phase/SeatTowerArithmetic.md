# Seat-Tower Arithmetic

## Abstract

Isolate the arithmetic reductions used by the seat-tower selector, walk formula, input gate, and divisibility floor.

This module records five arithmetic reductions with all structural premises explicit. It does not prove the Jacobi selector, identify canonical W3 data, validate orbit inputs, or extend finite observations to measurable claims.

**Theorem 1.1 (Multiples of twelve have two residues modulo twenty-four).**

$\forall \psi,q\in\mathbb{Z},\ \psi=12q \Rightarrow (\psi\operatorname{mod}24=0 \lor \psi\operatorname{mod}24=12)$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerArithmetic.mod_twenty_four_eq_zero_or_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an integer is explicitly written as twelve times a quotient, its residue modulo twenty-four is zero or twelve. No orbit divisibility premise is inferred.

**Theorem 1.2 (Divisibility by twenty-four is quotient parity).**

$\forall \psi,q\in\mathbb{Z},\ \psi=12q \Rightarrow (24\mid\psi \Leftrightarrow 2\mid q)$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerArithmetic.twenty_four_dvd_iff_even_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same explicit factorization by twelve, divisibility by twenty-four is equivalent to evenness of the quotient. The theorem does not identify that parity with a Jacobi symbol.

**Theorem 1.3 (The BHK and Rademacher hypotheses rearrange to the walk expression).**

$$\forall s,a,l,r,l',r',c,\phi\in\mathbb{Q},\ c\neq 0 \land 12s=-3+\frac{l'+r'}{c}-a \land \phi=\frac{l+r}{c}-12s \Rightarrow \phi=3+a+\frac{(l+r)-(l'+r')}{c}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerArithmetic.bhk_implies_w3_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rational variables and a nonzero denominator, the displayed conclusion follows algebraically from explicit BHK and Rademacher equations. This is not a typed identification theorem for canonical W3 data.

**Theorem 1.4 (The Pythagorean equation normalizes to an Eisenstein norm).**

$$\forall \beta,\gamma_{0},m\in\mathbb{Z},\ (\gamma_{0}-2\beta)^{2}+3\gamma_{0}^{2}=4m(m+1) \Leftrightarrow \beta^{2}-\beta\gamma_{0}+\gamma_{0}^{2}=m(m+1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerArithmetic.pythagorean_gate_iff_eisenstein_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two integer polynomial equations are equivalent by normalization. The theorem does not prove that actual orbit parameters satisfy either equation and does not validate narrative input data.

**Theorem 1.5 (A nonzero multiple of twelve has absolute value at least twelve).**

$\forall \psi\in\mathbb{Z},\ 12\mid\psi \land \psi\neq 0 \Rightarrow 12\leq |\psi|$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerArithmetic.twelve_le_abs_of_dvd_of_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Explicit divisibility by twelve and nonzeroness imply the absolute-value floor. No sampled congruence, asymptotic law, or measurable statement is closed.

## References

- Truth anchor: `D5/S1/Phase/SeatTowerArithmetic.bhk_implies_w3_walk`
- Truth anchor: `D5/S1/Phase/SeatTowerArithmetic.mod_twenty_four_eq_zero_or_twelve`
- Truth anchor: `D5/S1/Phase/SeatTowerArithmetic.pythagorean_gate_iff_eisenstein_norm`
- Truth anchor: `D5/S1/Phase/SeatTowerArithmetic.twelve_le_abs_of_dvd_of_ne_zero`
- Truth anchor: `D5/S1/Phase/SeatTowerArithmetic.twenty_four_dvd_iff_even_quotient`
