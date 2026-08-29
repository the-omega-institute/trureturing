# Exact Blind-Prime Classification for Integer Pairs

## Abstract

Integer residues agree exactly at prime divisors of the difference; for distinct integers the blind prime set is finite and the separating set is cofinite.

**Theorem 1.1 (Residue equality is divisibility of the difference).**

$$\forall p \in \mathbb{N}, x, y \in \mathbb{Z}, \operatorname{primeResidue}\left(p, x\right) = \operatorname{primeResidue}\left(p, y\right) \iff p \mid x - y.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/BlindPrimes/IntegerPairClassification.prime_residue_eq_iff_dvd_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integer modular equality is Mathlib's integer congruence relation. Its divisibility characterization gives the ordered difference after negating the opposite subtraction.

**Theorem 1.2 (Blind primes are exactly prime divisors).**

$$\forall x, y \in \mathbb{Z}, \operatorname{blindPrimes}\left(x, y\right) = \operatorname{primeDivisors}\left(x - y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/BlindPrimes/IntegerPairClassification.blind_primes_eq_primeDivisors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extensionality applies the residue-divisibility equivalence at each prime index. No distinctness hypothesis is needed for this exact set identity.

**Theorem 1.3 (Distinct integers have finitely many blind primes).**

$$\forall x, y \in \mathbb{Z}, x \neq y \Rightarrow \operatorname{Finite}\left(\operatorname{blindPrimes}\left(x, y\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/BlindPrimes/IntegerPairClassification.blind_primes_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero difference has nonzero absolute value. Every blind prime therefore lies over the finite divisor finset of that absolute value.

**Theorem 1.4 (The separating prime set is cofinite).**

$$\forall x, y \in \mathbb{Z}, x \neq y \Rightarrow \operatorname{Finite}\left(\operatorname{compl}\left(\operatorname{separatingPrimes}\left(x, y\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/BlindPrimes/IntegerPairClassification.separating_primes_compl_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Within the prime-index subtype, the complement of the separating set is the blind set. Its finiteness proves cofiniteness. Natural and Dirichlet density are not claimed because pinned Mathlib has no usable definitions for them.

**Theorem 1.5 (Distinctness is required for blind-set finiteness).**

$$\neg\operatorname{Finite}\left(\operatorname{blindPrimes}\left(0, 0\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/BlindPrimes/IntegerPairClassification.distinctness_is_necessary_for_blind_primes_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the concrete equal pair zero and zero, every prime is blind. The prime subtype is infinite, so this blind set is not finite.

## References

- Truth anchor: `D5/S3/Arith/BlindPrimes/IntegerPairClassification.blind_primes_eq_primeDivisors`
- Truth anchor: `D5/S3/Arith/BlindPrimes/IntegerPairClassification.blind_primes_finite`
- Truth anchor: `D5/S3/Arith/BlindPrimes/IntegerPairClassification.distinctness_is_necessary_for_blind_primes_finite`
- Truth anchor: `D5/S3/Arith/BlindPrimes/IntegerPairClassification.prime_residue_eq_iff_dvd_difference`
- Truth anchor: `D5/S3/Arith/BlindPrimes/IntegerPairClassification.separating_primes_compl_finite`
