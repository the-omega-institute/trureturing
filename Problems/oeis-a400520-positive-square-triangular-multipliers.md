---
slug: oeis-a400520-positive-square-triangular-multipliers
bibkey: ratushnyak2026a400520
doi: null
url: https://oeis.org/A400520
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/SquareTriangularMultipliers
---

# Positive square-and-triangular multipliers

## Problem

OEIS A400520, revision #22 (Nov 14 2026 14:42:25 EST), NAME, verbatim:

> a(n) is the least multiplier k such that either n*k or n*k+1 is a square, and either n*k or n*k+1 is a triangular number, or -1 if no such k exists.

COMMENT, verbatim:

> Conjecture: a(n) > 0.

The offset is `0,3`, so the natural index includes zero. A multiplier is
interpreted as positive: this convention is supported by the DATA values
`a(0)=a(1)=1` and by the source program. The word positive is not quoted
as part of NAME. The square and triangular indices range over all natural
numbers, including zero. The two alternatives are independent.

Formally, `Sq(x)` means `exists s : Nat, x=s^2`, `Tri(x)` means
`exists t : Nat, 2*x=t*(t+1)`, and
`P(n,k) = (Sq(n*k) or Sq(n*k+1)) and (Tri(n*k) or Tri(n*k+1))`.
The integer `a(n)` is the least natural `k>=1` satisfying `P(n,k)` if one
exists, and is `-1` otherwise. The full assertion is `a(n)>0` for every
natural `n`, without additional hypotheses or finite cutoffs. The result
also gives a positive witness, identifies `a(n)` with it, proves its
minimality for the original predicate, and proves both initial values.

## Motivation

The assertion asks whether the least-positive-multiplier definition ever
takes its failure branch. An arbitrary positive square triangular multiple
of `n` is sufficient to establish existence, but the sequence minimum is
still taken over the original independent alternatives.

## Gap

The source preregistration is issue
https://github.com/the-omega-institute/trureturing/issues/30790,
with its unchanged full-event registration at
https://github.com/the-omega-institute/trureturing/issues/30790#issuecomment-6892565495.
The source classification is first tier, a newly published OEIS conjecture.
The checked revision #22 and history retained the conjecture with no
explicit proof or refutation in the inspected source. The arXiv query
`all:A400520` returned zero results. Checked related entries A000217,
A000290, A001110, A182334, A001109 and A001108 supplied classical
square-triangular and Pell ingredients, rather than a proof of this named
assertion. Some papers were inaccessible. These bounded readings do not
certify worldwide priority or exhaustive absence of earlier work.

The repository has prime-power local Pell periodicity results, but their
modulus restriction does not directly cover this problem. The proof uses
finite injective dynamics modulo each actual positive `n` and verifies
the bridge to the same discriminant-eight integral orbit.

## Route

Use Mathlib's Pell sequence at parameter three. Its recurrence is
`(x,y) -> (3x+8y,x+3y)` and its invariant is `x^2-8y^2=1`.
The inverse update modulo `n` is `(u,v) -> (3u-8v,-u+3v)`.
Finite injectivity gives a positive return to `(1,0)`, so `n` divides
the positive Pell coordinate `y`. The coordinate `x` is odd; writing
`x=2t+1` yields `2y^2=t(t+1)`. If `y=nq`, choose `k=nq^2`, which is
positive and makes `nk=y^2` both square and triangular. Handle `n=0`
with `k=1`, and apply the natural least-witness principle to `P`.

The orbit-identification and odd-coordinate induction connect the reused
Mathlib facts to this exact source problem. The admission basis is
`open-problem-resolution`; the argument makes no separate novelty claim
for the classical Pell or finite-dynamics ingredients.

## Falsifier

A natural `n` for which every positive natural `k` fails either of the
two required alternatives would refute the original assertion. A failure
of the displayed minimum to satisfy the original predicate or its
minimality would refute the source bridge. The Lean result rules out all
these failures for every natural index.

## Evidence

The mathematical source is
`D5/S3/Arith/Congruence/SquareTriangularMultipliers.lean`, with one public
theorem `result`. Its conclusion contains the universal positivity and
least-witness clauses, as well as `a(0)=a(1)=1`. The definition of `a`
retains the `-1` branch when no positive witness exists. The standard
axiom closure is `Classical.choice`, `Quot.sound`, and `propext`.
The owning Blueprint gives the definitions, parameter correspondence and
complete derivation. Independent source/form/mirror assessment and
publication remain separate from kernel verification.

OEIS source text is attributed to the OEIS Foundation and its contributors
under CC-BY-SA-4.0, https://oeis.org/LICENSE. No OEIS program is reproduced.
The named source is by Alex Ratushnyak; bibliographic metadata is in
`Library/QuadraticForms/ratushnyak2026a400520.md`.

## Triage

The complete mathematical assertion is proved by `result` in
`D5/S3/Arith/Congruence/SquareTriangularMultipliers`.

### What the settlement shows

Proved in that GID: every positive natural number has a positive multiple
that is simultaneously square and triangular, and this sufficient family
establishes the full original independent-alternative statement at every
natural index. The least-positive-witness convention gives the sequence
assertion, including both initial values. There is no prime, squarefree
or coprimality restriction.

The decisive mechanism is the determinant-one Pell update over every
finite residue ring, together with positivity in its integral orbit.
The proof gives existence without claiming an optimal witness bound or
a formula for the least multiplier. Infinitely many suitable multipliers
for each positive index is a neighboring question suggested by iterated
returns and strict Pell growth; it is not an additional public theorem
of this module and has not been independently screened here.

## ASSUMED-UNVERIFIED

Historical openness outside the bounded source and literature readings
is unverified. No worldwide priority claim or complete literature census
is made. Kernel proof does not replace independent admission, source
fidelity, rendered-clause review, required CI, or an actual merge.
