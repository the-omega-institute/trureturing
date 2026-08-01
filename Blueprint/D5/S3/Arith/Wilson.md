# Wilson's Theorem

## Abstract

The factorial of one less than a prime is congruent to minus one modulo that prime.

**Theorem 1.1 (The factorial before a prime is minus one modulo the prime).**

$$p\ \text{prime}\quad\Rightarrow\quad (p-1)!\equiv -1\ (\operatorname{mod}\ p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Wilson.wilson_theorem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p, the natural number factorial (p - 1)! casts to -1 in the residue ring ZMod p. Equality after the canonical natural-number cast into ZMod p is the standard formal expression of the congruence (p - 1)! congruent to -1 modulo p, so the statement retains the source atom's modulus, factorial, and sign without weakening.

The atomic proof skeleton pairs each nonzero residue modulo p with its multiplicative inverse. Every pair with distinct entries contributes one to the product, while a self-inverse residue solves x squared = 1 and is therefore 1 or -1; their product leaves -1. The Lean proof constructs the required primality Fact from the explicit hypothesis and assembles this skeleton through Mathlib's ZMod.wilsons_lemma. No numerical certificate is asserted.
