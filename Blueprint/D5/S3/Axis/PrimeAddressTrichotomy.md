# Prime Residues Modulo Four

## Abstract

Every prime is either two or has residue one or three modulo four.

**Theorem 1.1 (A prime is two or has residue one or three modulo four).**

$$\forall p : \mathbb{N}, Prime(p) \Rightarrow p = 2 \lor p \bmod 4 = 1 \lor p \bmod 4 = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/PrimeAddressTrichotomy.prime_address_mod_four_trichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p, either p is the even prime 2, or its remainder after division by 4 is 1 or 3. These alternatives are exhaustive; the last two alternatives are the odd residue classes modulo 4.

This records only the prime-residue trichotomy clause. The separate equivalence between residue 1 modulo 4 and representation as a sum of two squares, and the dynamical classifier interpretation, remain unresolved and are not claimed here.

Pinned Mathlib was searched before proving. The Lean theorem directly combines Nat.Prime.eq_two_or_odd with Nat.odd_mod_four_iff; no complete trichotomy wrapper was found under the queried names.

## References

- Truth anchor: `D5/S3/Axis/PrimeAddressTrichotomy.prime_address_mod_four_trichotomy`
