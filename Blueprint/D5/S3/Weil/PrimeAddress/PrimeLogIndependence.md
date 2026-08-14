# Rational Independence of Prime Logarithms

## Abstract

Unique factorization makes the logarithms of the primes linearly independent over the rationals.

**Theorem 1.1 (Prime logarithms are integer-linearly independent).**

$$\operatorname{LinearIndependent}_{\mathbb{Z}}(p \mapsto \log p : \operatorname{Primes} \to \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeLogIndependence.prime_log_integer_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The family p maps to log p, indexed by the natural primes and valued in the reals, is linearly independent over the integers. This declaration adapts the repository's existing finite-relation theorem prime_log_indep to Mathlib's LinearIndependent interface; the existing theorem supplies the unique-factorization argument.

**Theorem 1.2 (Prime logarithms are rationally linearly independent).**

$$\operatorname{LinearIndependent}_{\mathbb{Q}}(p \mapsto \log p : \operatorname{Primes} \to \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeLogIndependence.prime_log_rational_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same prime-indexed real family is linearly independent over the rationals. Mathlib's fraction-ring equivalence reduces this assertion to the preceding integer theorem, thereby proving the denominator-clearing step rather than assuming it.

**Theorem 1.3 (Every rational relation between log two and log three is trivial).**

$$\forall a, b \in \mathbb{Q},\ a \cdot \log 2 + b \cdot \log 3 = 0 \Rightarrow a = 0 \land b = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeLogIndependence.log_two_log_three_relation_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rational coefficients a and b, a log 2 plus b log 3 can vanish only when both coefficients vanish. This is the two-coordinate specialization of the prime-family theorem.

**Theorem 1.4 (The coefficient pair one and minus one gives no vanishing relation).**

$$(1 : \mathbb{Q}) \cdot \log 2 + (-1 : \mathbb{Q}) \cdot \log 3 \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeAddress/PrimeLogIndependence.log_two_sub_log_three_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit nontrivial rational coefficient pair (1, -1) does not annihilate log 2 and log 3. This checked instance prevents the general independence statement from being vacuous.

## References

- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeLogIndependence.log_two_log_three_relation_eq_zero`
- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeLogIndependence.log_two_sub_log_three_ne_zero`
- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeLogIndependence.prime_log_integer_independence`
- Truth anchor: `D5/S3/Weil/PrimeAddress/PrimeLogIndependence.prime_log_rational_independence`
- Dependency: [D5/S3/Factorization/PrimeLogIndependence](../../Factorization/PrimeLogIndependence.md)
