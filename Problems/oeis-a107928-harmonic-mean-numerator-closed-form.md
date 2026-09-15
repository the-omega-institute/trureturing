---
slug: oeis-a107928-harmonic-mean-numerator-closed-form
bibkey: stephan2010a107928
doi: null
url: https://oeis.org/A107928
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm
---

# Closed form of the A107928 harmonic-mean-numerator recurrence

## Problem

OEIS A107928, NAME (`%N`, verbatim):

> a(n) is the numerator of harmonic mean of a(n-1) and a(n-2).

FORMULA (`%F`, verbatim):

> a(1)=2; a(2)=3; n>=3: a(n) = numerator(2*a(n-1)*a(n-2)/(a(n-2)+a(n-1))).

CONJECTURE (`%F`, verbatim; Ralf Stephan, Dec 01 2010):

> Conjecture: G.f.: x*(2+3*x+12*x^2+8*x^3+8*x^4)/[(1-2*x)*(1+2*x+4*x^2)]. a(3n) = (3/2)*8^n, a(3n+1) = 3*8^n, a(3n+2) = 2*8^n, for n>0. - _Ralf Stephan_, Dec 01 2010

AUTHOR (`%A`, verbatim):

> %A _Zak Seidov_, Jun 10 2005

The first terms (`%S`) are 2, 3, 12, 24, 16, 96, 192, 128, 768, 1536,
1024, 6144, … . The formal claim is
`∀ m ≥ 1, a(3m) = 12·8^(m−1) ∧ a(3m+1) = 3·8^m ∧
a(3m+2) = 2·8^m`. The Lean definition uses `a 0 = 0` as an offset-one
sentinel and implements the reduced numerator as `Rat.num ... .toNat`.
Only the three-residue closed form is formalized by elementary block
induction; no priority claim is made. The printed generating function with
+8x^4 expands to 2, 3, 12, 24, 32, ... and disagrees with the sequence at
n = 5 (a(5) = 16), whereas changing the sign to -8x^4 yields the rational
generating function x(2+3x+12x^2+8x^3-8x^4)/(1-8x^3) of the proved closed
form; the generating-function sentence is neither formalized nor claimed,
and the discrepancy is recorded here, not corrected upstream.

## Motivation

The entry has carried Stephan's explicit unbounded conjecture since 2010.
Proving all three residue classes resolves the stated closed form rather than
only extending the finite sequence table.

## Gap

The dated searches recorded in issue #7586 and its probe comment on
2026-09-13 and 2026-09-14 found no proof or refutation. OEIS revisions #1
through #13 show that revision #3 introduced the conjecture and later
revisions made maintenance changes only. Exact searches returned 0 for OEIS
Open arXiv:2608.11941, google-deepmind/formal-conjectures,
epoch-research/LeanOpenProblems-results, arXiv, MathOverflow, DataCite, and
OpenAIRE. The OpenAlex autocomplete endpoint returned 0; its works endpoint
ended with a budget error and is `ASSUMED-UNVERIFIED`. DataCite and OpenAIRE
were checked by the search seat. These are bounded searches, and the result is
elementary, so no priority claim is made.

## Route

Use the block invariant
`(a(3m+1), a(3m+2)) = (3*8^m, 2*8^m)`. The next harmonic mean is
`12*8^m/5`; since `gcd(12*8^m, 5) = 1`, its reduced numerator is
`12*8^m`, giving `a(3m+3)`. The following harmonic mean is `24*8^m/7`;
since `gcd(24*8^m, 7) = 1`, its reduced numerator is `24*8^m =
3*8^(m+1)`, giving `a(3m+4)`. The third harmonic mean is `16*8^m`,
giving `a(3m+5) = 2*8^(m+1)`. Direct reduction gives the base block
`a(3)=12`, `a(4)=24`, and `a(5)=16`, so induction proves every positive
block.

## Falsifier

One positive m for which any of the three displayed residue-class equalities
fails would contradict the theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm.lean`.
- Main theorem: `stephan_a107928`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator independently evaluated the exact `Fraction` recurrence
  through n = 3000: there were 0 closed-form mismatches, and the first 12
  terms were 2, 3, 12, 24, 16, 96, 192, 128, 768, 1536, 1024, 6144,
  matching `%S`.
- The search seat evaluated through n = 10000 with 0 mismatches.
- The probe independently evaluated through n = 3000 with 0 mismatches.

## Triage

`theorem`. The result is an unbounded universal theorem proved by block
induction.

## ASSUMED-UNVERIFIED

The OpenAlex works endpoint was not verified because it ended with a budget
error. All literature searches are bounded, and no first-publication or
priority claim is made.
The printed generating function has a sign discrepancy at the x^4 term
(disclosed above); no corrected formula is claimed or submitted upstream.
