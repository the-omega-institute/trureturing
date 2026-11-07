---
slug: mathar-2013-a097967-literal-recurrence
bibkey: mathar2013a097967
doi: null
url: https://oeis.org/A097967
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MatharA097967.result
---

# Mathar's recurrence for the literal A097967 sum

## Problem

Let a(n) be the rational sum of n!(k!+1)/(k!(n-k)!) over natural k with
1<=k<=n, including both endpoints and empty at n=0. For every natural n>=5,
without an upper bound, the target is

```text
a(n) + (-n-6)*a(n-1) + (6*n+7)*a(n-2) + (-13*n+14)*a(n-3)
     + 4*(3*n-8)*a(n-4) + 4*(-n+4)*a(n-5) = 0.
```

Factorials and all index subtraction are in Nat; factorials are cast to Q
before division. All signed coefficients and recurrence arithmetic are in Q.
There is no integrality premise, recurrence-defined replacement, negative
extension or eventual-only relaxation. The Tier 1 archived OEIS conjecture
is attributed to Mathar in the FORMULA field. Its source has no onset;
n>=5 is the registered nonnegative-index interpretation, not an author quotation.

## Motivation

The recurrence gives an exact unbounded relation among six consecutive values
of a sequence fixed independently by its literal factorial sum.

## Gap

The immutable registration is issue #27326 comment 6689398711. Independent
mathematical evaluation is comment 6690028211; the truth event is already
settled by terminal 6690048528 and readout 6690060143. Formal implementation
does not constitute another research unit or reset that registration.

No exact Lean supplier was found in the searched scope: fresh dev's public
and private D5 source, Library, Problems, Blueprint and theory exact-identifier
searches; pinned mathlib's factorial/binomial ingredients; and the refreshed
GitHub code query A097967 with language Lean (zero indexed results).
The independent evaluation additionally reports zero arXiv all-fields and
Crossref identifier results and only #27326 in all-state issue searches.
These are bounded lexical searches, not exhaustive semantic closure.
A007526's first-order recurrence and factorial sum are established prior art.

## Route

Split each summand by Nat.descFactorial_eq_factorial_mul_choose and
Nat.cast_choose. Reindex the inclusive interval as range n with k+1.
The binomial row sum gives a(n)=b(n)+2^n-1, where
b(n)=sum over k<n of Nat.descFactorial n (k+1), cast to Q.
Nat.succ_descFactorial_succ gives b(n+1)=(n+1)(b(n)+1).
Five substitutions and rational polynomial normalization prove the recurrence
at n=m+5, and every natural n>=5 is of that form.

## Falsifier

A natural n>=5 whose literal rational sum has a nonzero displayed residual
would contradict the exact proposition proved by result.

## Evidence

The mathematical source is D5/S1/Recurrence/MatharA097967.lean.
Its public surface is literal, b, claim : Prop and result : claim.
The six private helpers are consumed in the result's live derivation:
term_split, sum_shift and choose_sum feed literal_formula; literal_formula
and b_step feed recurrence_forward; recurrence_forward feeds result.
The matching Blueprint Scribe describes every public declaration and carries
a Proved OpenProblemResolutionClaim. Kernel compilation, registration machine
status, rendered fidelity and frozen membership have their own producers;
this dossier does not assert their governance state.

## Triage

Admission basis: open-problem-resolution for the entire registered Tier 1
literal-sum conjecture. Every proof declaration is bind-only after helper
inlining; no escape witness is claimed. Utility is none. The polynomial
normalization and known suppliers do not constitute an originality claim.

### What the settlement shows

- **Proved by D5/S1/Recurrence/MatharA097967.result:** the full exact recurrence
  for every natural n>=5. Its internal literal_formula and b_step identities
  explain the factorial/binomial decomposition and elimination mechanism.
- **Source boundary:** the printed subtractive identity involving A007526
  and A000225 is not certified. At n=1 its right side is -1, while the
  literal sum is 2, as recorded by the independent exact evaluation.
- **Open:** extension below five requires a convention for negative indices.
  No sharpness claim for such extensions is made. No additional source
  conjecture, asymptotic or generating-function theorem is settled here.

## ASSUMED-UNVERIFIED

Global originality, priority, complete A007526 bibliography and Cabrera's
2025 article, and exhaustive semantic supplier closure are unverified.
The solver saw the already fixed predicted probabilities, compromising solver
blindness. Independent evaluation retained validity of the fixed truth-event
settlement with that limitation. All model labels belong to OpenAI Codex GPT;
there is no blinded-search or model-diversity claim. The independent mirror/form
review and later publication decisions remain outside this mathematical dossier.
