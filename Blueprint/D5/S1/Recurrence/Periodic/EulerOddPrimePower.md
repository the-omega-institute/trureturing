# Odd-prime-power zero transfer

## Abstract

Corrected Euler coefficients propagate zeros at every positive odd-prime-power index.

Write q=p raised to r+1, and epsilon=(-1) raised to b times floor(p/2). All parameters are natural; b is zero or one. Residue arithmetic is in ZMod q. The deleted frequencies form an exact finite bijection. The correction factor is a unit at every positive index, including indices smaller than r+1. This reconstructs a consequence of Young's prior Kummer congruence, without a p-adic premise.

**Theorem 1.1 (The prime-deleted frequency identity).**

$$\forall p: \mathbb{N}, (\forall r: \mathbb{N}, (\forall b: \mathbb{N}, (\forall j: \mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies ((\operatorname{Odd}\left(p\right)) \implies ((b \le 1) \implies (\left(1 - \operatorname{residue}\left(p^{r + 1}, (-1)\right)^{b \cdot \operatorname{div}\left(p, 2\right)} \cdot \operatorname{residue}\left(p^{r + 1}, p\right)^{j}\right) \cdot \operatorname{residue}\left(p^{r + 1}, \operatorname{A}\left(b, j\right)\right) = \sum_{h \in \operatorname{filter}\left(\operatorname{range}\left(p^{r + 1}\right), h \mapsto \neg (p \mid 2 \cdot h + b)\right)} (\operatorname{residue}\left(p^{r + 1}, (-1)\right)^{h} \cdot \operatorname{residue}\left(p^{r + 1}, 2 \cdot h + b\right)^{j}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerOddPrimePower.corrected_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract the p-scaled shorter odd-length sum from the full sum. The divisible frequencies have h=p*v+b*floor(p/2).

**Theorem 1.2 (Every positive signed zero transfers).**

$$\forall p: \mathbb{N}, (\forall r: \mathbb{N}, (\forall b: \mathbb{N}, (\forall k: \mathbb{N}, (\forall m: \mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies ((\operatorname{Odd}\left(p\right)) \implies ((b \le 1) \implies ((0 < k) \implies ((\operatorname{residue}\left(p^{r + 1}, \operatorname{A}\left(b, k\right)\right) = 0) \implies (\operatorname{residue}\left(p^{r + 1}, \operatorname{A}\left(b, k + m \cdot \operatorname{totient}\left(p^{r + 1}\right)\right)\right) = 0))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerOddPrimePower.signed_zero_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every retained frequency is a unit. Euler periodicity equates their powers, and nilpotence of p proves the correction factor invertible.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/EulerOddPrimePower.corrected_sum`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerOddPrimePower.signed_zero_transfer`
- Dependency: [D5/S1/Recurrence/Periodic/EulerSignedFrequency](EulerSignedFrequency.md)
