---
bibkey: luca2009eulerfibonacci
authors: Florian Luca; V. Janitzio Mejía Huguet; Florin Nicolae
year: 2009
title: On the Euler Function of Fibonacci Numbers
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL12/Mejia/luca31.pdf
claim: Lemma 3 bounds the sum of reciprocal primes with Fibonacci rank m by O(log(m)/m); it does not state a Robin bound for arbitrary two-term sums.
strata_touched: []
license: citation-only
triage: anchor
---

# Fibonacci rank buckets and Euler-function distributions

The primary article is in *Journal of Integer Sequences* 12 (2009), Article
09.6.6. Lemma 3, equation (5), page 4, with proof continuing on page 5, states
that the sum of `1/p` over primes whose first Fibonacci zero index is `m` is
`O(log(m)/m)`. It uses `p = ±1 mod m`, a cardinality bound from the product of
these primes dividing `F_m`, and a split at `m^2`. No explicit constant six
is stated there. Lemma 4 on page 5 bounds the divisor sum of `log(d)/d` by
`O((log log m)^2)`, citing Luca's earlier work.

Theorem 1 and the discussion immediately after it on page 2 concern density
of vectors of ratios of Euler functions at consecutive Fibonacci numbers.
Page 13, Section 6 states the corresponding extension to the divisor-sum
function. Neither statement gives an upper bound for the divisor sum of an
arbitrary additive combination of Fibonacci terms.

FIB theory §171 compares this established rank-bucket method with the explicit
logarithmic Euler estimate in §163 and the common-source carrier bounds in
§§167–169. Those combinations are project deductions, not claims attributed
to this paper. This note records the verified primary statements, not an
exhaustive priority search or a new proof of RH.
