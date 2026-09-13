# Candidates screened out, with the reason

Verdicts on OEIS conjectures examined for the open-problem lane. Recorded so that neither I nor
another driver re-examines them. A kill here means the candidate fails one of the four checks in
`TARGET-GATES.md`; it does not assert that a conjecture is false.

Screened 2026-09-13 unless noted. Where a verdict came from a search seat rather than direct
inspection, the reasoning is reproduced so it can be checked rather than trusted.

## Already settled in the literature

| entry | what settles it |
| --- | --- |
| A048153 | Kutal, June 2026: closed form with class numbers of imaginary quadratic orders, giving the stronger bound `a(n) ≤ n(n−1)/2`. Also an August 2026 proof abstract. |
| A237271 | Hoft, January 2025, for conjecture 1; Kitamura, August 2026, Lean 4 proof for conjectures 4 and 5. |
| A211417 | OEIS records the conjecture as proved by an autonomous AI agent, with a Lean file, June 2026. |
| A117531 | Kutal, 22 August 2026. Note the boundary: the linked Lean development declares Stark–Heegner as a project axiom, so this is a literature settlement, not an axiom-free formalisation. |
| A180017 | Drmota and Spiegelhofer, arXiv:2501.00850, Theorem 1.2. The joint-value theorem gives every difference `s₃(n) − s₂(n) = z` infinitely often; the earlier zero-collision result alone would not. |
| A109074 | Kuperberg's proved enumeration of vertically symmetric alternating-sign matrices, Annals 156 (2002); the conjectured ratio is the consecutive ratio of that count. |
| A001157 | Fried, December 2025. |
| A000040 | Follows from Wilson's theorem. |

A mechanical sweep of 118 corpus entries against the OEIS text found 22 carrying settlement
markers. That sweep matches keywords, so it both misses and over-reports — `A130911`'s "true for
primes up to 10^19" is a verification range, `A306477` is an unclaimed prize, `A034693` reports
a stronger conjecture's verification. Treat 22 as a lower bound and read the entry before
promoting anything.

## Famous problems in disguise

The OEIS wording gives no sign of these. Each was identified by reducing the statement, not by
recognising a name.

| entry | what it actually is |
| --- | --- |
| A105020 | Exactly binary Goldbach. Reparameterising the block as `r(2n+2−r)`, both factors exceed 1, so a semiprime exists there exactly when `2n+2` is a sum of two primes. |
| A101779 | Implies infinitely many Sophie Germain primes: every witness has `k ≥ n`, so arbitrarily large `n` give arbitrarily large `k` with `2k+1` prime. |
| A119591 | Implies infinitely many Mersenne primes, by specialising to `n = 2^m`. |
| A017666 | Implies every odd perfect number is practical, which is impossible for an odd integer above 1. |
| A185150 | Stronger than Legendre: dropping the residue condition leaves "every interval `(n², (n+1)²)` contains a prime". |
| A115366 | Entails infinitely many prime values of the irreducible quadratic `k² + 3k + 1`. |
| A001359 | Wilson's theorem rewritten through the intervening product. |
| A005258 | Irreducibility of the Apéry polynomials; the entry carries Apéry, Brown and the Lucas-theorem survey. |
| A110835 | Sierpiński 1958. |
| A103151 | Self-describes as stronger than Goldbach. |

## Published, with only a finite residue left

| entry | coverage |
| --- | --- |
| A111291 | Zelinsky 2002, Theorem 14: `T(x) > cπ(x)` eventually for every fixed `c`. Only a finite range remains. |
| arXiv:1411.4092 Conj. 2.7, `n=3` | Girstmair's largest-values theorem covers all sufficiently large `b` coprime to 3; a finite range and `3 ∣ b` remain. |

## Reduced object already available

See `TARGET-GATES.md` for the method and the repository-side cases. Upstream case:
`A049473`'s Beatty clause is `Mathlib/NumberTheory/Rayleigh.lean`'s `compl_beattySeq`
instantiated at the Hölder-conjugate pair `√2, 2+√2`, and appears in no repository path.

## Shape excluded: unbounded iteration

| entry | why |
| --- | --- |
| A087207 | Orbit values explode — `a(101) = 2^25`, and near `n = 20000` the first step reaches a 681-digit number — so termination is Collatz-shaped, not a short proof. |
| A100800 | Same shape: iterate `n ↦ n + digitsum(n)` until a multiple of `n`. |
| A153330 | Adjacent Collatz total stopping times. |

## Duplicates within the corpus

`A109908` and `A109909` ask the same existence question. Note that the 2024 paper linked from
those entries, claiming a solution, was examined and its constrained-optimisation step found
defective; it is not treated as a settlement.

## Who else is working this corpus

Tom Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?",
arXiv:2608.11941, builds a benchmark of 492 open OEIS conjectures formalized in Lean from
google-deepmind/formal-conjectures and reports 147 resolved. Entries are now acquiring comments
that record such work. Expect a candidate drawn from that corpus to have been attempted.
