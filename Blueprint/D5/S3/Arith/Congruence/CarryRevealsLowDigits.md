# A Carry Reveals the Missing Low Digits

## Abstract

Reading the digit of order k of a p-adic integer along the translations x, x + 1, ..., x + p^k - 1 recovers its residue modulo p^{k+1}: the first carry into that digit reveals the lower digits, and no shorter run of readings suffices.

**Definition 1.1 (The digit sensor).**

$$d_{k}(x) = \lfloor\frac{(q_{k+1}(x))}{p^{k}}\rfloor$$

*Formalization.* `D5/S3/Arith/Congruence/CarryRevealsLowDigits.highDigit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here q_{k+1} is the reduction of a p-adic integer modulo p^{k+1}, read as a natural number below p^{k+1}; the sensor d_k returns its digit of order k.

**Definition 1.2 (The fixed continuous protocol).**

$$W_{k,N}(x) = (d_{k}(x+n))_{n \leq N}$$

*Formalization.* `D5/S3/Arith/Congruence/CarryRevealsLowDigits.digitProtocol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The protocol reads the sensor after 0, 1, ..., N unit translations.

**Theorem 1.3 (Carry revelation and the sharp horizon).**

$$p \text{ prime }, k \in \mathbb{N}, x, y \in \mathbb{Z}_{p}, b = \lfloor\frac{q_{k+1}(x)}{p^{k}}\rfloor, r = q_{k+1}(x) \operatorname{mod} p^{k} \Rightarrow\\{}\forall n \leq p^{k}-1, d_{k}(x+n) = (b+\lfloor\frac{r+n}{p^{k}}\rfloor) \operatorname{mod} p \land\\{}(r = 0 \Rightarrow \forall n, 1 \leq n \leq p^{k}-1 \Rightarrow d_{k}(x+n) = d_{k}(x)) \land\\{}(r > 0 \Rightarrow d_{k}(x+(p^{k}-r)) \neq d_{k}(x) \land \forall n, 1 \leq n < p^{k}-r \Rightarrow d_{k}(x+n) = d_{k}(x)) \land\\{}(W_{k,p^{k}-1}(x) = W_{k,p^{k}-1}(y) \iff q_{k+1}(x) = q_{k+1}(y)) \land\\{}\forall N, k \geq 1 \Rightarrow N < p^{k}-1 \Rightarrow W_{k,N}(0) = W_{k,N}(1) \land q_{k+1}(0) \neq q_{k+1}(1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/CarryRevealsLowDigits.carry_reveals_low_digits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here q_{k+1}(x) is read as a natural number below p^{k+1}, so q_{k+1}(x) = b p^k + r with b < p and r < p^k. Then q_{k+1}(x + n) is the residue of b p^k + r + n modulo p^{k+1}, and its digit of order k is the digit of the quotient of b p^k + r + n by p^k, that is (b + floor((r + n)/p^k)) mod p. For n <= p^k - 1 the sum r + n is below 2 p^k, so at most one carry reaches the digit: none when r = 0, and exactly at n = p^k - r when r > 0, where the digit changes because p >= 2, including the wrap from p - 1 to 0. Two points with the same readings therefore share b and the first change time, hence r, so they have the same residue; the converse holds because every reading factors through q_{k+1}. For k >= 1 and n <= p^k - 2 the points 0 and 1 both read digit 0, while their residues differ.

## References

- Truth anchor: `D5/S3/Arith/Congruence/CarryRevealsLowDigits.carry_reveals_low_digits`
- Truth anchor: `D5/S3/Arith/Congruence/CarryRevealsLowDigits.digitProtocol`
- Truth anchor: `D5/S3/Arith/Congruence/CarryRevealsLowDigits.highDigit`
