# The Inert Bad-Prime Congruence

## Abstract

An inert prime factor of (6j)^2+1 is congruent to 5 modulo 12.

**Theorem 1.1 (An inert prime dividing (6j)^2+1 is 5 modulo 12).**

$$\forall j p : \mathbb{N}, p \mathrm{prime}, p \mid (6j)^{2}+1, p \operatorname{mod} 3 = 2 \Rightarrow p \operatorname{mod} 12 = 5$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/InertPrimeMod12.inert_prime_dvd_mod_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any prime p that is inert in the Eisenstein integers (p mod 3 = 2) and divides (6j)^2 + 1, the residue p mod 12 equals 5. A rational prime is inert in the Eisenstein integers exactly when p mod 3 = 2 (it splits when p mod 3 = 1 and ramifies at 3), so the hypothesis selects the inert factors; the split factors of (6j)^2 + 1 are instead congruent to 1 modulo 12, and are not constrained by this lemma.

The proof is four steps. First p is not 2, since (6j)^2 + 1 is odd. Casting the divisibility p | (6j)^2 + 1 into ZMod p makes (6j)^2 = -1, so -1 is a square modulo p; the standard characterization of when -1 is a quadratic residue then forces p mod 4 to differ from 3, and with p odd this is p mod 4 = 1. Finally the two residues p mod 4 = 1 and p mod 3 = 2 combine, by the Chinese remainder theorem, to p mod 12 = 5.

This records only the bad-prime lemma. Mathlib supplies the quadratic-residue characterization of -1 but no assembled inert bad-prime congruence. The statement does not cover the odd-core density theorem in which the lemma is used — the half-dimensional sieve estimate for the count of j whose value (6j)^2 + 1 is realized — which is far beyond this arithmetic congruence.

## References

- Truth anchor: `D5/S3/Arith/Congruence/InertPrimeMod12.inert_prime_dvd_mod_twelve`
