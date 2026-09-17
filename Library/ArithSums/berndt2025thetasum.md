---
bibkey: berndt2025thetasum
authors: Bruce C. Berndt, Raghavendra N. Bhat, Jeffrey L. Meyer, Likun Xie, Alexandru Zaharescu
year: 2025
title: "An Arithmetic Sum Associated with the Classical Theta Function"
doi: null
url: https://arxiv.org/abs/2501.03234
claim: "S'(h,k) = sum_{j=1}^{k-1} (-1)^(j+1+floor(h*j/k)), S(k) = sum_{h=1}^{k-1} S'(h,k). Conjecture 1.1: S(k) > 0 for every odd prime k. Conjecture 4.1: S(k) > k for every prime k > 5. Conjecture 4.2: S(k) > 2k for k > 233. Conjecture 4.3: S(k) > 3k for k > 3119. Conjecture 4.4: for every n, eventually n*k < S(k) along odd primes."
strata_touched: []
license: citation-only
triage: anchor
---

# Berndt, Bhat, Meyer, Xie and Zaharescu, arithmetic sum of the theta function

The five conjectures quoted above are open. None is proved in this repository, and no
declaration about `S` or `S'` exists here. This note records what was measured while
attempting Conjecture 1.1, so that a later attempt does not repeat eliminated routes.

## Structure that is established by computation

Two facts reduce the conjecture. Both were verified across the first 45 odd primes with no
violations, and both are bind-only in the sense of the repository's admission rule — they
follow from the pinned library by instantiation and normalisation, so they belong inside a
proof and not as declarations.

`S'(h,k) = 0` for every odd `h`, when `k` is an odd prime. Pair `j` with `k - j`: since `k` is
prime and `1 <= j <= k-1`, the quotient `h*j/k` is never an integer, so
`floor(h*(k-j)/k) = h - 1 - floor(h*j/k)`. The two exponents sum to `k + h + 1`, odd exactly
when `h` is odd, so the paired terms cancel; `k` odd means `j` is never its own partner.
Primality is needed: `S'(3,9) = -2`, so the unrestricted odd-composite form is false.

`S'(k-1,k) = k-1`, since `floor((k-1)*j/k) = j - 1` makes every exponent even.

Hence `S(k) = (k-1) + rest(k)`, where `rest(k)` sums `S'(h,k)` over the even `h` in
`[2, k-3]`, and Conjecture 1.1 is equivalent to `rest(k) >= 0`. Measured values of `rest` for
the first eighteen odd primes: 0, 0, 4, 4, 8, 8, 20, 8, 16, 56, 56, 40, 52, 60, 32, 48, 104,
132 — always nonnegative, zero only at `k = 3` and `k = 5`, and always divisible by four.

Inversion invariance: for even `h` whose inverse modulo `k` is also even,
`S'(h,k) = S'(h^{-1} mod k, k)`. Verified on 2381 such pairs across the 63 odd primes from 7
through 317, and on 2383 pairs across 65 primes when 3 and 5 are included. `h = k-1` is a fixed
point, consistent with the value above. This is most likely the standard Dedekind-sum property
`s(h,k) = s(h^{-1},k)` seen through a Dedekind-type expression for `S'`.

`S'(2,k) = 2` when `k = 3 (mod 4)` and `0` when `k = 1 (mod 4)`, over the first twelve odd
primes.

## Routes eliminated, with the counterexample that kills each

Termwise nonnegativity of the even-`h` terms: false. `S'(6,17) = -4` and `S'(4,11) = -2`.

Nonnegativity of inversion-orbit sums: false. The first negative orbit is `{14, 24}` at
`k = 67`, contributing `-4` against `rest(67) = 132`. Enlarging the orbits by adjoining
`x -> 1 - x` does not repair it: at `k = 23` the orbit `{3, 8, 11, 13, 16, 21}` contributes
`-4` through its even elements.

Endpoint-only compensation after signed inversion cancellation: false. Writing `R(k)` for the
even `h` in `[2, k-3]` with even inverse and `Bminus(k)` for the sum of the negative parts of
`S'(h,k)` over `R(k)`, the bound `S(k) >= k - 1 + Bminus(k)` first becomes nonpositive at
`k = 15727`, where `Bminus = -16056` and the bound gives `-330` against the actual
`S = 94450`. All 1831 odd primes through 15727 were scanned, two independent integer algorithms
agreed on 3372322 values, and direct evaluation of 123653538 original summands at 15727
confirmed the obstruction.

The two-step Euclidean remainder bound from Dedekind reciprocity: insufficient. It first gives
a negative bound for `rest` at `k = 19`, namely `-4` against the actual `20`, and first fails
to establish `S > 0` at `k = 31`, where the bound gives `rest >= -32` against the actual `56`.
Independent absolute-value estimates for the Dedekind terms are also insufficient. The general
reciprocity route is not eliminated; only these estimates are.

## The reformulation that survives

`S(k) = (k-1)^2/2 - 4*N(k)`, where `N(k)` counts the pairs of even residues whose product
modulo `k` is even. Conjecture 1.1 is then exactly `N(k) < (k-1)^2/8`: strictly fewer than half
of the even-even pairs have even product. That inequality is not proved here, and it is the
form in which a further attempt should start.

## Verified locator

- URL: https://arxiv.org/abs/2501.03234
