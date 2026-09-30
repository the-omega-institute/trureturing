# Erdős #375: a three-term prime-divisor slice

**Status (30 September 2026):** the source problem remains open. The live
entry [#375](https://www.erdosproblems.com/375) is marked FALSIFIABLE/open and
reports zero proof claims. The full statement asks for distinct prime
representatives for every finite interval of composite integers.

## Formal target

For `n >= 1`, assume `n + 1`, `n + 2`, and `n + 3` are composite. Then there
exist pairwise distinct primes `p_1`, `p_2`, and `p_3` such that

\[
p_i \mid n+i \qquad (i=1,2,3).
\]

This is the first case beyond the page's stated trivial range `k <= 2`. The
Lean declaration is

```text
D5.S3.Arith.Congruence.Erdos375ThreeComposites
  .exists_distinct_prime_divisors_of_three_composites
```

## Proof ledger

Every positive term has a prime divisor (`Nat.exists_prime_and_dvd`). For each
endpoint, `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt` gives either a
multiple of four or an odd prime divisor. If both endpoints were multiples of
four, `Nat.dvd_sub` would give `4 | 2`, a contradiction. Thus one endpoint
has an odd prime divisor. If it were also a divisor of the other endpoint,
the same subtraction gives a prime divisor of `2`; primality and oddness rule
out both `1` and `2`. Finally, consecutive coprimality from
`Nat.coprime_add_self_right` and `Nat.eq_one_of_dvd_coprimes` separates the
middle divisor from each endpoint divisor.

The hypotheses that all three terms are composite are retained to match the
named Erdős slice. The proof only needs the first one to exclude `n = 1`; the
prime-divisor and coprimality facts handle the other two terms directly.

## Residual open boundary

This theorem leaves every interval length `k >= 4`, the Hall-type global
matching problem for arbitrary composite runs, and the unrestricted Grimm
conjecture open. Finite verification through large bounds does not alter that
boundary.

## References

1. [Erdős Problems #375](https://www.erdosproblems.com/375), accessed 30
   September 2026.
2. S. Laishram and T. N. Shorey, *Grimm's conjecture on consecutive
   integers* (2006), linked from the source page.
3. P. Erdős and J. L. Selfridge, historical work cited by the source page.
