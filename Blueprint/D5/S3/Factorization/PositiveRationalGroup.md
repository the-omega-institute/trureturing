# Positive Rationals from Signed Prime Exponents

## Abstract

Signed prime exponents give the additive presentation of positive rationals.

**Definition 1.1 (Signed prime ledgers map to positive rationals).**

$$primeExponentEquivPositiveRational:(Prime \Rightarrow Int) \sim PositiveRational$$

*Formalization.* `D5/S3/Factorization/PositiveRationalGroup.primeExponentEquivPositiveRational` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence sends a finitely supported integer-valued function on the natural primes to a positive rational. Addition of exponent ledgers corresponds to multiplication of positive rationals.

**Theorem 1.2 (The prime-exponent equivalence is bijective).**

$$\operatorname{Bijective}(primeExponentEquivPositiveRational)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PositiveRationalGroup.signed_prime_ledger_equiv_positive_rationals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite signed prime ledger determines exactly one positive rational, and every positive rational has exactly one such ledger. The codomain is represented as the units of the nonnegative rationals, so zero is excluded by construction.

The library was searched before proving. No direct equivalence between positive rationals and integer prime exponents was found. The proof instead constructs both groups as localizations of the natural prime ledger and applies AddSubmonoid.LocalizationMap.addEquivOfLocalizations. The localization laws use AddSubmonoid.isLocalizationMap_of_addGroup; natural-number factorization enters through PNat.factorMultisetEquiv, PNat.factorMultiset_mul, and Multiset.toFinsupp. This is a new localization wrapper assembled from pinned library components, not a wrapper around the complete statement. The source atom contains no numerical certificate.

**Theorem 1.3 (Rational logarithmic length is additive).**

$$rationalLogLength(a+b)=rationalLogLength(a)+rationalLogLength(b)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PositiveRationalGroup.rational_log_length_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transporting the natural logarithm through the equivalence extends prime-exponent length to signed ledgers. The homomorphism law turns ledger addition into rational multiplication, and Real.log_mul turns that product into addition. A separate checked witness shows that this extension takes negative values, as required for ratios below one.

## References

- Truth anchor: `D5/S3/Factorization/PositiveRationalGroup.primeExponentEquivPositiveRational`
- Truth anchor: `D5/S3/Factorization/PositiveRationalGroup.rational_log_length_add`
- Truth anchor: `D5/S3/Factorization/PositiveRationalGroup.signed_prime_ledger_equiv_positive_rationals`
