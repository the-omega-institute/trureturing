---
slug: oeis-a046528-sigma-tau-rational-power-mersenne-characterization
bibkey: laboselemer2013a046528
doi: null
url: https://oeis.org/A046528
triage: theorem
motivation_gids:
  - D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne
---

# Products of distinct Mersenne primes satisfy exactly the sigma-tau rational-power relation

## Problem

OEIS A046528, NAME (`%N`, verbatim):

> Numbers that are a product of distinct Mersenne primes (elements of A000668).

The known COMMENT (`%C`, verbatim) states:

> n is a product of distinct Mersenne primes iff sigma(n) is a power of 2: see exercise in Sivaramakrishnan, or Shallit.

Jaroslav Krizek's COMMENT (`%C`, verbatim) states:

> Supersequence of A051281 (numbers n such that sigma(n) is a power of tau(n)). Conjecture: numbers n such that sigma(n) = tau(n)^(a/b), where a, b are integers >= 1. Example: sigma(93) = 128 = tau(93)^(7/2) = 4^(7/2). - _Jaroslav Krizek_, May 04 2013

The literal proved statement is
`∀ n : ℕ, 0 < n → (isMersenneProduct n ↔ ratPow n)`, where
`isMersenneProduct n` means
`∃ S : Finset ℕ, n = ∏ p ∈ S, p ∧ ∀ p ∈ S, p.Prime ∧ ∃ k : ℕ, 0 < k ∧ p + 1 = 2 ^ k`,
and `ratPow n` means
`∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (σ 1 n) ^ b = (σ 0 n) ^ a`.
Here `σ 1` is the divisor-sum function and `σ 0` is the divisor-count
function tau. Since both bases are positive integers for positive `n`, this
integer-power equality is equivalent to Krizek's rational-exponent form.

No statement about A051281 beyond the displayed equivalence is claimed. The
infinitude or distribution of Mersenne primes and novelty of the known
sigma-equals-a-power-of-two classification are also NOT claimed.

## Motivation

The conjecture gives a structural characterization of every positive integer
whose divisor sum and divisor count are related by positive rational powers.
It strengthens the practical description of A046528 from a factorization
condition to an equivalent relation between two standard arithmetic functions.

## Gap

The OEIS `%C` line still labels Krizek's assertion as a conjecture dating from
2013. The checked A046528 history through revision 85 contains no settlement,
and the A051281 discussion includes Marcus's 2020 remark without a proof of
this equivalence. Exact searches performed on 2026-09-14 returned zero arXiv
matches, zero OpenAlex matches, and zero GitHub exact-phrase matches.
MathOverflow question 62721 concerns only the known equation
`sigma(x) = 2^n`, not Krizek's sigma-tau equivalence. These checked surfaces do
not support a publication-priority claim.

## Route

1. Equality of positive powers gives equality of the prime supports of
   `sigma(n)` and `tau(n)`.
2. For the largest odd prime `q` dividing `tau(n)`, choose a prime-power
   factor `p^e` of `n` with `q ∣ e+1`; then the geometric sum
   `G = ∑ i < q, p^i` divides `sigma(n)`.
3. Every prime factor `r` of `G` equals `q`: support equality gives `r ≤ q`,
   while the multiplicative order of `p` modulo `r` gives either `r=q` or
   the contradiction `q < r`.
4. The theorem `emultiplicity_geom_sum₂_eq_one` gives `q^2 ∤ G`, whereas the
   preceding unique-prime-factor classification forces the contrary. Thus
   `tau(n)` is a power of two. Steps 1 through 4 are the new argument.
5. The known Sivaramakrishnan-Shallit prerequisite, proved inline and
   attributed, shows that simultaneous power-of-two values of `tau(n)` and
   `sigma(n)` force `n` to be a product of distinct Mersenne primes.
6. Conversely, multiplicativity gives `sigma(n)=2^(sum k_p)` and
   `tau(n)=2^|S|`; the empty product `n=1` uses exponents `a=b=1`.

## Falsifier

A positive natural number `n` for which exactly one of
`isMersenneProduct n` and `ratPow n` holds would contradict the theorem. The
kernel-checked result quantifies over every positive natural number.

## Evidence

- Lean module:
  `D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 6.04 seconds, type checking
  160 milliseconds, and maximum resident set size 2,208,792,576 bytes.
- The orchestrator independently found zero counterexamples to the equivalence
  for `n ≤ 10^5`, zero counterexamples to the key odd-prime-support lemma for
  `n ≤ 2 * 10^5`, and zero counterexamples to the known step 5 over the same
  latter range.
- The probe found 19 `ratPow` hits for `n ≤ 10^5`; every hit was a product of
  distinct Mersenne primes.
- The bounded checks support fault detection only; the Lean proof carries the
  universal result.

## Triage

`theorem`. Krizek's rational-power characterization is proved for every
positive natural number, so the resolution is `proved`.

## ASSUMED-UNVERIFIED

The bounded scans do not establish the universal statement. The source texts
of Sivaramakrishnan and Shallit were not opened; their attribution is taken
from the OEIS `%C` line. Historical openness outside the checked OEIS history,
arXiv, OpenAlex, MathOverflow, GitHub, and cited-source surfaces is unverified;
no exhaustive literature or priority claim is made.
