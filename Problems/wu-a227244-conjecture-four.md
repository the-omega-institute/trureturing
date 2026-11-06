---
slug: wu-a227244-conjecture-four
bibkey: wu2026a227244c4
doi: null
url: https://oeis.org/A227244/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/WuA227244ConjectureFour.result
---

## Problem

Chai Wah Wu's fourth conjecture in OEIS A227244 states:
"Conjecture 4: a(168*n+43) = 59 if n>=0 and n mod 55 <> 26."
The NAME defines a(m) as the smallest prime factor of
(2^(2^m)+1)*2^(2^(2^m))-1. The primary locator and version are in
[wu2026a227244c4](../Library/Factorization/wu2026a227244c4.md).
The external assertion is identified by [#27391](https://github.com/the-omega-institute/trureturing/issues/27391).

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every n>=0, including zero, without an upper bound | `∀ n : ℕ` |
| n mod 55 differs from 26 | `n % 55 ≠ 26` |
| Index 168*n+43 | The same literal index in both divisibility clauses |
| Nested powers in NAME | `G m = ((2 : ℤ)^(2^m)+1)*2^(2^(2^m))-1` |
| Smallest prime factor equals 59 | `Nat.Prime 59`, integer divisibility by 59, and `59 ≤ q` for every natural prime q dividing the same integer |

All exponents are natural. The multiplication and final subtraction are in
Z. There is no claim at residue 26 and no claim that excluding it is necessary.

## Motivation

The assertion determines the least prime divisor for an unbounded family of
nested exponential integers, rather than for a finite prefix or only in the
sense of divisibility by 59.

## Gap

No exact prior resolved C4 supplier was found in the limited surfaces described
in the Library note. Literature completeness and priority remain
ASSUMED-UNVERIFIED. The mathematical target is the full stated family.

## Route

Periodicity transfers powers along the progression 168*n+43 to finite residues.
A separate tail-period identity handles the exponent inside the second outer
power. For each prime below 59, these identities show a nonzero residue of the
same signed integer; 59 itself has zero residue. The prime 47 uses a period of
55 in n and the original exclusion of residue 26. If a natural prime divisor
were smaller than 59, the corresponding nonzero residue would contradict
integer divisibility.

## Falsifier

An allowed natural n and either failure of divisibility by 59 or a natural
prime q<59 dividing that same signed integer would refute the assertion.
A value in the excluded residue class is outside its domain.

## Evidence

The canonical mathematical source is
`D5/S3/Arith/Primes/WuA227244ConjectureFour.lean`, with one public result and
private proof helpers. Its Scribe displays the full quantified event and one
Proved resolution. Current compilation and registration evidence is supplied
with the StageA handoff; this dossier does not assert frozen membership.

## Triage

| Item | Conclusion and boundary |
| --- | --- |
| C4 | The theorem `result` asserts the full unbounded family with the original exclusion. |
| Mechanism | Periodic modular transfer and finite residues exclude all smaller primes while 59 divides the integer. |
| C2 | Unresolved here; C4 provides no settlement. |
| Necessity of excluding residue 26 | Unresolved here; no assertion is made on that class. |
| General method or originality | No additional theorem or novelty claim; the proof composes existing APIs and consumed reductions. |

## ASSUMED-UNVERIFIED

Literature completeness, global priority and a dominating theorem outside the
searched scope are unverified. The four-slot audit outcome and any linked
exception are reported in the StageA handoff separately from kernel evidence.
