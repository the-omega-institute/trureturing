---
slug: erdos-1985-consecutive-product-squarefree-factor-refutation
bibkey: erdos1985consecutive
doi: 10.1216/RMJ-1985-15-2-353
triage: theorem
motivation_gids:
  - D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation
---

# Starting value 47 refutes Erdős's proposed unique counterexample

## Problem

Erdős, Rocky Mountain Journal of Mathematics 15(2) (1985), page 361
(verbatim from the rendered scan at
https://users.renyi.hu/~p_erdos/1985-27.pdf):

> Put (21) ∏_{i=1}^{k} (x + i) = u_k(x) v_k(x), (u_k(x), v_k(x)) = 1 where v_k(x) is squarefree and all prime factors of u_k(x) occur with an exponent greater than 1. The representation in (21) is clearly unique. Clearly for k > k_0(x), u_k(x) > v_k(x). Perhaps one can estimate the smallest k_0(x) so that u_k(x) > v_k(x) for all k > k_0(x) quite well. I have not done this. For small values of k usually v_k(x) > u_k(x). I thought that for every x there is a k for which v_k(x) > u_k(x). x = 7 seemed a likely counterexample but if k = 7, u_7(7) = 2^7 3^3 < v_7(7) = 5·7·11·13. On the other hand a simple computation shows that n = 23 is a counterexample, i.e., for every k, v_k(23) < u_k(23). The reason for this is the existence of 24, 25, 27 and 32. I would not be surprised if 23 is the only counterexample. Perhaps in fact there is a k_0 so that for every k > k_0 and all n > n_0(k) (22) v_k(n) > u_k(n). (22) is perhaps too optimistic.

The literal refuted statement is

```text
∀ x ≥ 1, x ≠ 23 → ∃ k ≥ 1, u(x,k) < v(x,k).
```

For `P(x,k) = ∏_{i=1}^k (x+i)`, `v(x,k)` is the product of the
primes whose exponent in `P(x,k)` is exactly one. It is not the squarefree
part: a prime occurring to exponent at least two is absent from `v`.
The factor `u(x,k)` is the product of every prime power whose exponent in
`P(x,k)` is at least two, with its full exponent. Thus `u(x,k)·v(x,k)=P(x,k)`.

The result refutes only the sentence proposing 23 as the unique
counterexample. It makes no claim about conjecture (22), an estimate of
`k_0(x)`, the assertion that 23 and 47 are the only counterexamples, or the
statement that 23 itself is a counterexample.

## Motivation

The paper identifies 23 as a counterexample and proposes that it could be the
only one. The starting value 47 is a second symbolic counterexample: every
positive length has `u(47,k) > v(47,k)`, so the displayed universal statement
is false.

## Gap

The literature surfaces recorded on September 14, 2026 in issue #7679 were
bounded. OEIS phrase search returned 0 relevant results. An exact arXiv web
search returned 0; its API timed out and is `ASSUMED-UNVERIFIED`.
MathOverflow returned 0. Crossref located the Erdős 1985 article; Semantic
Scholar listed three citing works, none addressing this remark, while its
rate-limited response is `ASSUMED-UNVERIFIED`. zbMATH reverse search
`rf:3929095` returned no result. Searches of erdosproblems.com for
`consecutive` (76 entries), `squarefree` (38 entries), and `Er85` (35 entries)
contained no hit for this question. The full text of Tao's arXiv:2603.27990
contained 0 hits for the quoted uniqueness sentence or its `u_k`/`v_k`
notation. Two Bing queries returned 0 relevant results. Google Scholar and
MathSciNet were not checked and are `ASSUMED-UNVERIFIED`. These readings make
no historical-priority claim.

## Route

Fix `x=47`. For `1 ≤ k ≤ 78`, split the interval into `1..30`, `31..60`,
and `61..78`. In each interval, factorization of the consecutive product is
the sum of the factorizations of its factors; finite factor-exponent
bookkeeping then verifies `v(47,k) < u(47,k)` in the kernel.

For `k ≥ 79`, induction on `k` proves
`16^(47+k) < P(47,k)`, beginning with the exact base inequality at `k=79`
and using the next factor `47+(k+1)`. Every prime counted by `v(47,k)` is at
most `47+k`, so
`v(47,k) ≤ primorial(47+k) ≤ 4^(47+k)`. Hence
`v(47,k)^2 ≤ 16^(47+k) < P(47,k) = u(47,k)·v(47,k)`, and positivity of `v`
gives `v(47,k) < u(47,k)`.

## Falsifier

A positive `k` with `u(47,k) ≤ v(47,k)` would falsify the counterexample.
The proof would also fail if the factorization sum did not match the
consecutive product, if a prime in `v` exceeded `47+k`, if the primorial bound
had the wrong direction, if the inductive exponential inequality failed, or
if `u(47,k)·v(47,k)` did not reconstruct `P(47,k)`.

## Evidence

- Lean module:
  `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axiom closure
  `propext`, `Classical.choice`, and `Quot.sound`.
- A profiled kernel check at source SHA-256
  `563b78f4eb1a8a183a2ef97e8f5d77c760735d073462b758f063605d04effe9c`
  took 23.22 seconds wall time, 19.3 seconds cumulative type checking, and
  2,149,892,096 bytes maximum resident set size.
- An independent bounded scan found no `k` with `u(47,k) ≤ v(47,k)` for
  `1 ≤ k ≤ 3000`.
- At the closest scanned point, `k=15`,
  `u(47,15)=15362887680000` and `v(47,15)=7920561451517`, with
  `v(47,15)=11·13·17·19·29·31·53·59·61` and
  `u(47,15)·v(47,15)=P(47,15)`.
- In the bounded rectangle `1 ≤ x ≤ 3000`, `1 ≤ k ≤ 800`, the starting
  values surviving every tested length were exactly `{23,47}`.
- For `x=7`, the bounded scan found `v(7,k)>u(7,k)` only at `k=7`.

The bounded scans corroborate the symbolic argument but do not carry the
theorem or classify all counterexamples.

## Triage

`theorem`. The kernel theorem refutes the literal universal statement using
the starting value 47. The module is `utility: none`: `P`, `v`, `u`, and
`claim` are definitions, while `result` is a symbolic refutation by finite
factor-exponent lemmas followed by an inductive exponential estimate and a
primorial bound. None of `bounded-enumeration`, `checker`,
`numeric-reduction`, or `certified-instance` describes its main new content.

## ASSUMED-UNVERIFIED

The arXiv API timeout, the Semantic Scholar HTTP 429 response, the unchecked
Google Scholar and MathSciNet surfaces, all bounded numerical scans, and the
historical openness of the remark after the listed search surfaces are
`ASSUMED-UNVERIFIED`. No exhaustive literature or priority claim is made.
