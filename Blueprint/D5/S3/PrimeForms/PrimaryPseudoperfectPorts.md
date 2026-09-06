# Primary Pseudoperfect Reciprocal and Extension Laws

## Abstract

Primary pseudoperfect numbers admit exact reciprocal and prime-extension laws.

Write d(n) for the sum of n divided by p over the distinct prime divisors p of n, and R(n) for the corresponding sum of rational reciprocals 1/p.

**Theorem 1.1 (The quotient sum casts to the reciprocal-prime sum).**

$$\operatorname{d}\left(n\right) = n \operatorname{R}\left(n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prime in primeFactors n divides n and is nonzero. Mathlib's Nat.cast_div therefore converts each natural quotient n / p to the rational quotient, and distributivity factors out n.

**Theorem 1.2 (The reciprocal and integral identities are equivalent).**

$$n \neq 0 \Rightarrow \frac{1}{n} + \operatorname{R}\left(n\right) = 1 \Leftrightarrow n = 1 + \operatorname{d}\left(n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.reciprocal_sum_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by the nonzero rational n and the cast identity turn one equation into the other. The explicit nonzero premise excludes the totalized division value at n = 0.

**Theorem 1.3 (Primary pseudoperfectness is the reciprocal identity).**

$$\operatorname{IsPPN}\left(n\right) \Leftrightarrow \operatorname{Squarefree}\left(n\right) \land 1 < n \land \frac{1}{n} + \operatorname{R}\left(n\right) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_iff_reciprocal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict lower bound n > 1 supplies n != 0 in both directions, so the reciprocal theorem applies without a hidden degenerate case.

**Theorem 1.4 (A new prime gives a one-step quotient expansion).**

$$K \neq 0 \land \operatorname{Prime}\left(p\right) \land \neg\operatorname{Divides}\left(p, K\right) \Rightarrow \operatorname{d}\left(Kp\right) = p\operatorname{d}\left(K\right) + K.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv_mul_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime-factor set of Kp is the disjoint union of the factors of K and the new prime p. Old quotients scale by p, while the new quotient is K.

**Theorem 1.5 (Two new primes give the iterated quotient expansion).**

$$\operatorname{FreshDistinctPrimes}\left(K, p, q\right) \Rightarrow \operatorname{d}\left(Kpq\right) = q{p\operatorname{d}\left(K\right) + K} + Kp.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv_mul_two_primes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the one-prime expansion first to p and then to q gives the formula; distinctness ensures q is still new after adjoining p.

**Theorem 1.6 (A prime successor preserves primary pseudoperfectness).**

$$\operatorname{IsPPN}\left(K\right) \land \operatorname{Prime}\left({K + 1}\right) \Rightarrow \operatorname{IsPPN}\left(K{K + 1}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_mul_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A number and its successor are coprime. The prime-extension formula and the identity K = 1 + d(K) then close the new quotient identity.

**Theorem 1.7 (The two-prime extension is an integer factor equation).**

$$\operatorname{IsPPN}\left(K\right) \land \operatorname{FreshDistinctPrimes}\left(K, p, q\right) \Rightarrow (\operatorname{IsPPN}\left(Kpq\right) \Leftrightarrow {p - K}{q - K} = \operatorname{sq}\left(K\right) + 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_mul_two_primes_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equation is stated over the integers, so neither subtraction is silently truncated. Expanding both sides is equivalent to the new primary-pseudoperfect quotient identity.

**Theorem 1.8 (The first five numerical witnesses).**

$$\operatorname{IsPPN}\left(2\right) \land \operatorname{IsPPN}\left(6\right) \land \operatorname{IsPPN}\left(42\right) \land \operatorname{IsPPN}\left(1806\right) \land \operatorname{IsPPN}\left(47058\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.primary_pseudoperfect_numerical_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first four terms follow by repeated prime-successor extension. The last uses the squarefree factorization 2 * 3 * 11 * 23 * 31 and computes its quotient sum as 47057.

## References

- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_iff_reciprocal_sum`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_mul_succ`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.isPPN_mul_two_primes_iff`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.primary_pseudoperfect_numerical_chain`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.reciprocal_sum_eq_one_iff`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv_cast`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv_mul_prime`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv_mul_two_primes`
