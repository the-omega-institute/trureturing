# Murthy's bounded exponent conjecture is false

## Abstract

The least positive prime-producing exponents in OEIS A087372 are unbounded.

**Definition 1.1 (The least positive exponent).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \begin{cases}\operatorname{min}\left(\{k : \mathbb{N} \mid 1 \le k \land \operatorname{Prime}\left(3^{k} + 2 \cdot n\right)\}\right)&\exists k \in \mathbb{N},\; 1 \le k \land \operatorname{Prime}\left(3^{k} + 2 \cdot n\right)\\0&\neg (\exists k \in \mathbb{N},\; 1 \le k \land \operatorname{Prime}\left(3^{k} + 2 \cdot n\right))\end{cases}$$

*Formalization.* `D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.a` (`✓ std3`).

*Citation.* Amarnath Murthy (2003). *OEIS A087372, Smallest k such that 3^k + 2n is a prime, or 0 if no such k exists*. URL: <https://oeis.org/A087372>.

*Commentary.*

OEIS A087372, NAME (unpaginated), defines the least exponent producing a prime, or zero if none exists. Exponents are positive natural numbers: EXAMPLE gives a(23)=3, since 49 and 55 are composite and 73 is prime. Allowing exponent zero would give 47 and contradict that example. Nat.find chooses the least member of the displayed nonempty set, testing every earlier positive exponent; the empty-set branch is exactly zero. The definition is total on natural n, and the conjecture uses the source's offset-one domain.

**Definition 1.2 (The full boundedness assertion).**

$$claim = (\exists M \in \mathbb{N},\; \forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{a}\left(n\right) < M)$$

*Formalization.* `D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.claim` (`✓ std3`).

*Citation.* Amarnath Murthy (2003). *OEIS A087372, Smallest k such that 3^k + 2n is a prime, or 0 if no such k exists*. URL: <https://oeis.org/A087372>.

*Commentary.*

OEIS A087372, COMMENTS (unpaginated): "Conjecture: There exists a finite M such that a(n) < M for all n." Both M and n range over natural numbers, with n at least one. The same M must work for every such n, and the inequality is strict.

**Theorem 1.3 (No finite bound exists).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/murthy-a087372-bounded-exponent` (refuted) by `D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"murthy-a087372-bounded-exponent","declaration_gid":"D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amarnath Murthy (2003). *OEIS A087372, Smallest k such that 3^k + 2n is a prime, or 0 if no such k exists*. URL: <https://oeis.org/A087372>.

*Commentary.*

Fix any positive K. Apply PrimeGap.exists_primeGap_ge to 3^K, obtaining consecutive primes q<p with p-q at least 3^K. The upper prime p is odd and p-3^K is even and at least two. Write p-3^K=2n, so n is at least one. At exponent K the candidate is p. For every positive j<K, the candidate 3^j+2n lies strictly between q and p, hence is composite. The absence of a prime in this interval follows from Nat.nth_add_one_le_iff. Thus the qualifying set is nonempty and its least member is exactly K: a(n)=K. Given a proposed bound M, take K=M+1 to contradict a(n)<M. This constructs actual first successes of every positive size; it imposes no cutoff and does not infer a bound from only the successful inputs. The consecutive-prime gap theorem is reused; the exponent construction is derived here.

## References

- Truth anchor: `D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.a`
- Truth anchor: `D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.claim`
- Truth anchor: `D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.result`
- Dependency: [D5/S3/Arith/Primes/PrimeGap](PrimeGap.md)
