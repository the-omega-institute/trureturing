# Murthy's decimal bounded exponent conjecture is false

## Abstract

The least positive prime-producing exponents in OEIS A087371 are unbounded.

**Definition 1.1 (The least positive exponent).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \begin{cases}\operatorname{min}\left(\{k : \mathbb{N} \mid 1 \le k \land \left(\operatorname{Prime}\left(10^{k} + 2 \cdot n - 1\right) \land 10 < 10^{k} + 2 \cdot n - 1\right)\}\right)&\exists k \in \mathbb{N},\; 1 \le k \land \left(\operatorname{Prime}\left(10^{k} + 2 \cdot n - 1\right) \land 10 < 10^{k} + 2 \cdot n - 1\right)\\0&\neg (\exists k \in \mathbb{N},\; 1 \le k \land \left(\operatorname{Prime}\left(10^{k} + 2 \cdot n - 1\right) \land 10 < 10^{k} + 2 \cdot n - 1\right))\end{cases}$$

*Formalization.* `D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.a` (`✓ std3`).

*Citation.* Amarnath Murthy (2003). *OEIS A087371, Smallest k such that 10^k + 2n-1 is a prime >10, or 0 if no such k exists*. URL: <https://oeis.org/A087371>.

*Commentary.*

OEIS A087371, NAME (unpaginated), defines the least exponent for which 10^k+2n-1 is a prime strictly greater than ten, or zero if none exists. The displayed set retains all three conditions: k is positive, the candidate is prime, and its value exceeds ten. Exponent zero cannot qualify: for n at least one its candidate is 2n, and an even prime is two, which fails the strict threshold. Thus the positive-exponent convention agrees with the source even if its smallest-power wording is read as allowing exponent zero. Nat.find takes the least member of the nonempty set, testing every earlier positive exponent; the empty-set branch is exactly zero. The definition is total on natural n, and the conjecture uses the source's offset-one domain.

**Definition 1.2 (The full boundedness assertion).**

$$claim = (\exists M \in \mathbb{N},\; \forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{a}\left(n\right) < M)$$

*Formalization.* `D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.claim` (`✓ std3`).

*Citation.* Amarnath Murthy (2003). *OEIS A087371, Smallest k such that 10^k + 2n-1 is a prime >10, or 0 if no such k exists*. URL: <https://oeis.org/A087371>.

*Commentary.*

OEIS A087371, COMMENTS (unpaginated): "Conjecture: There exists a finite M such that a(n) < M for all n." Both M and n range over natural numbers, with n at least one. The same M must work for every such n, and the inequality is strict.

**Theorem 1.3 (No finite bound exists).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/murthy-a087371-bounded-exponent` (refuted) by `D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"murthy-a087371-bounded-exponent","declaration_gid":"D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amarnath Murthy (2003). *OEIS A087371, Smallest k such that 10^k + 2n-1 is a prime >10, or 0 if no such k exists*. URL: <https://oeis.org/A087371>.

*Commentary.*

Fix any positive K. Apply PrimeGap.exists_primeGap_ge to 10^K, obtaining consecutive primes q<p with p-q at least 10^K. Since q is at least two, p is strictly greater than ten. The upper prime p is odd, whereas 10^K is even. Hence p-10^K is a positive odd integer. Write p-10^K=2m+1 and set n=m+1, so n is at least one and 10^K+2n-1=p. This is a qualifying prime strictly greater than ten at exponent K. For every natural j<K, including zero, the candidate 10^j+2n-1 lies strictly between q and p, hence is composite by Nat.nth_add_one_le_iff. In particular every earlier positive exponent fails. Thus the qualifying set is nonempty and its least member is exactly K: a(n)=K. Given a proposed bound M, take K=M+1 to contradict a(n)<M. This supplies genuine first successes of every positive size without a cutoff, while retaining the zero value whenever no exponent qualifies. The consecutive-prime-gap theorem is reused directly; the offset, threshold and leastness are checked for this decimal sequence. No theorem about the separate base-three sequence is assumed.

## References

- Truth anchor: `D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.a`
- Truth anchor: `D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.claim`
- Truth anchor: `D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.result`
- Dependency: [D5/S3/Arith/Primes/PrimeGap](PrimeGap.md)
