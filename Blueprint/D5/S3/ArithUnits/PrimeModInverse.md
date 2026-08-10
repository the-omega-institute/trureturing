# Invertibility Modulo a Prime

## Abstract

A natural number not divisible by a prime is a unit modulo that prime.

**Theorem 1.1 (Nondivisibility by a prime gives a unit modulo that prime).**

$$\forall p,a\in\mathbb{N},\ p\ \text{prime} \land \neg(p \mid a) \Rightarrow \operatorname{IsUnit}([a]_{p})$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/PrimeModInverse.prime_not_dvd_is_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p and natural number a, if p does not divide a, then the residue class of a in ZMod p is multiplicatively invertible. This is the complete source clause: no converse, explicit inverse construction, or unresolved subclaim is asserted.

Repository searches found no declaration or Blueprint with this exact adapter signature. The existing PrimeModUnit theorem characterizes units modulo a prime as nonzero residues, while FermatLittle consumes the same premise to prove a different modular-congruence conclusion.

Pinned Mathlib supplies both bridge results needed here. ZMod.isUnit_iff_coprime turns the goal into coprimality of a and p, and Nat.Prime.coprime_iff_not_dvd converts the stated premise to coprimality in the opposite order. Symmetry closes the adapter. The nearby isUnit_prime_of_not_dvd reverses the mathematical roles by making the prime the residue modulo an arbitrary modulus, so it is not the target theorem. No inverse or coprimality argument is re-proved.

## References

- Truth anchor: `D5/S3/ArithUnits/PrimeModInverse.prime_not_dvd_is_unit`
