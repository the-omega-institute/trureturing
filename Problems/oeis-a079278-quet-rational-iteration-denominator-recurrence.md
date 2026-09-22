---
slug: oeis-a079278-quet-rational-iteration-denominator-recurrence
bibkey: quet2003a079278
doi: null
url: https://oeis.org/A079278
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.result
---

# Quet's A079278 reduced-denominator recurrence

## Problem

OEIS A079278 states (verbatim):

> %N A079278 Define a rational sequence {b(n)} as b(1) = 1, b(n) = b(n-1) + 1/(1 + 1/b(n-1)) for n > 1; a(n) is the denominator of b(n).
> %F A079278 Conjecture (Quet): a(m+1) = a(m)^2 + a(m)^3 / a(m-1)^2 - a(m)*a(m-1)^2 for m >= 2.
> %D A079278 Suggested by _Leroy Quet_, Feb 14 2003.
> %A A079278 _N. J. A. Sloane_, Feb 16 2003
> %O A079278 1,2

The literal proved statement is

```lean
theorem result (m : ℕ) (hm : 2 ≤ m) :
    (b (m - 1)).den ^ 2 ∣ (b m).den ^ 3 ∧
      (b (m + 1)).den = (b m).den ^ 2 + (b m).den ^ 3 / (b (m - 1)).den ^ 2 -
        (b m).den * (b (m - 1)).den ^ 2
```

The public definition `b` is the rational iteration in `%N`, with only the
harmless total extension `b 0 = 0`. The public theorem `result` states both
conjuncts directly with Lean's reduced-rational denominator projection
`(b k).den`. Consequently the public declarations alone identify `a(k)` with
the denominator of `b(k)` and entail Quet's `%F`; no private bridge theorem is
needed by an external reader to connect a separately named integer sequence.

Here `/` and subtraction are natural-number operations. The divisibility
conjunct proves that the quotient in Quet's formula is exact, rather than
silently interpreting an inexact quotient by floor division. The proof also
establishes the inequality required for the natural-number subtraction.

Not claimed here are a recurrence for the numerator sequence A079269; any
result about A355615, A080581, or A080582; exhaustive literature coverage;
priority for the proof; or that finite computations replace the kernel proof.

## Motivation

The DATE line says `Suggested by _Leroy Quet_, Feb 14 2003`, and the AUTHOR
line says `_N. J. A. Sloane_, Feb 16 2003`. Revision #1, dated Fri May 16
2003 on the history page, already renders the conjecture. Revision #45,
dated Jul 12 2022 20:55:10, still opens the FORMULA line with
`Conjecture (Quet)`, with no settlement comment or proof link. Thus the entry
records an open problem since 2003; no priority claim is made.

## Gap

The following bounded searches were performed on 2026-09-15:

1. The A079278 text and revision history were read. Revision #45 still says
   `Conjecture (Quet)`, while the `start=40` history page shows revision #1
   already carrying the conjecture.
2. Searching OEIS for the exact iteration
   `b(n)=b(n-1)+1/(1+1/b(n-1))` returned only A079278 and its numerator
   companion A079269; neither supplied a proof or settlement of A079278.
3. OEIS searches for the pair recurrence
   `(p,q)->(p(p+2q),q(p+q))` and for `p/(p+q)` found no matching entry. The
   `p(p+2q)` search returned unrelated A234387 and A319227.
4. All four cross-referenced entries were read. A079269 retains its own
   numerator conjecture, A355615 is a different rational iteration, and
   A080581 and A080582 are ratio sequences; none settles A079278.
5. Searches around continued-fraction, Engel, Pierce, Sylvester, and Goebel
   denominator-recurrence families returned established neighboring sequences
   A341862, A006540, A006538, A000058, and A202854, not a settlement of
   Quet's iteration.
6. Crossref searches for `rational iteration reduced denominator recurrence`
   and the pair recurrence returned generic rational-iteration and rational-map
   records and unrelated papers, with no exact proof found.
7. OpenAlex's search for `rational iteration reduced denominator recurrence`
   returned HTTP 429, so that endpoint supplied no result.
8. The arXiv API searches for `rational iteration denominator` and
   `arXiv:2608.11941` returned HTTP 429. The arXiv:2608.11941 abstract page
   was read separately; it describes the OEIS Open benchmark and contains no
   A079278 settlement or appendix proof.
9. The MathOverflow API search for `rational iteration denominator recurrence`
   returned unrelated recurrence and continued-fraction questions, with no
   A079278 or exact-shape proof.
10. The SeqFan archive link referenced by A079269 was fetched and produced no
    readable proof content; the OEIS link confirms only that a posting dated
    2003-02-15 exists.

No prior proof or refutation was found in this searched scope. This is a
`not-found-in-searched-scope` finding, not an exhaustive or priority claim.

## Route

Writing a reduced rational as `p/q`, direct field algebra gives

`p/q + 1/(1+q/p) = p(p+2q)/(q(p+q))`.

Thus the pair recurrence is `(p,q) -> (p(p+2q),q(p+q))`. The coprimality
calculation shows that this map preserves lowest terms, so the next reduced
denominator is `q(p+q)`. The private theorem `b_pair` identifies this pair
recurrence with the rational iteration, and `b_den` transfers the preserved
lowest-term denominator to Lean's reduced-rational projection. The proof of
`result` actively applies `b_den` to each of its three public denominator
expressions before continuing with the integer recurrence.

For the integer recurrences, `q_(m+1) = q_m p_m + q_m^2`. Quet's formula is
equivalent to

`p_m = q_m^2 / q_(m-1)^2 - q_(m-1)^2`,

which follows by unwinding the numerator recurrence. Factoring the denominator
recurrence proves `q_(m-1)^2` divides `q_m^3`; the same expansion supplies the
subtraction inequality, and ring normalization yields the stated equation.

## Falsifier

A natural number `m >= 2` for which `(b (m-1)).den^2` does not divide
`(b m).den^3`, or for which the exact natural-number quotient makes the
displayed equation for `(b (m+1)).den` false, would contradict `result`. A
positive index at which the pair recurrence's denominator differs from
`(b n).den` would contradict the live reduced-form bridge used in its proof.

## Evidence

- Lean module:
  `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.lean`.
- Public definitions `num` and `den`: empty axiom closure.
- Public definition `b`: std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Public theorem `result`: std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- The single-file kernel profile exited 0 in 4.27 seconds wall time, with 51.6
  milliseconds of cumulative type checking and 1,647,034,368 bytes maximum
  resident set size.
- Independently deleting any one of `Mathlib.Data.Nat.GCD.Basic`,
  `Mathlib.Tactic.FieldSimp`, `Mathlib.Tactic.Positivity`, or
  `Mathlib.Tactic.Ring` makes the serial build exit 1; restoring all four gives
  a zero-exit serial build.
- The exact integer pair recurrence was checked for `n = 1..21`: 20
  denominator-step checks, 19 numerator-identity checks, 19 Quet-formula
  checks, and 21 coprimality checks all returned true.
- The values `a(1..6) = [1, 2, 10, 310, 363010, 594665194510]` match the
  entry's `%S` values term for term.
- `a(21)` has 411381 decimal digits. The older `10^4` exact-check heuristic
  does not apply to this doubly exponential sequence; the corrected rule in
  `tools/scripts/agent/openproblem/SCREENED-OUT.md` scales evidence range to
  sequence growth. The finite checks do not establish the universal theorem.

## Triage

`theorem`. Quet's reduced-denominator recurrence is proved for every `m >= 2`,
with an exactness certificate for its natural-number quotient. The resolution
is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

OpenAlex and the arXiv API were unavailable for the stated searches because
both returned HTTP 429. Literature completeness outside the ten bounded
queries above is unverified. No exhaustive literature or priority claim is
made, and the finite exact-integer checks do not establish the universal
statement.
