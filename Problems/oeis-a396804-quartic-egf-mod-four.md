---
slug: oeis-a396804-quartic-egf-mod-four
bibkey: hanna2026a396804
doi: null
url: https://oeis.org/A396804
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
---

# OEIS A396804: the fourth-iterate EGF modulo four

## Problem

Paul D. Hanna's OEIS A396804 (2026-06-09) defines the exponential generating
function by `A(x)=x exp(A^4(x))`, explicitly specifying that superscripts mean
compositional iteration. Its independent modulo-four conjecture is:
`a(n) == [1,2,3,0] repeating (mod 4) for n >= 1`.

Precisely: A is the unique rational formal power series with constant term
zero and `A=X*(exp Rat).subst(iterateComp A 4)`, where the zeroth iterate is X.
The independently established natural sequence satisfies
`(a(n):Rat)=n!*[x^n]A`; the target is `Nat.ModEq 4 (a n) n` for every `n≥1`.
The old, refuted modulo-three pattern is outside this dossier.

## Motivation

This is a first-tier recent OEIS conjecture with an unbounded arithmetic
target. The frozen motivating module treats an ordinary-series iterative
equation. This target adds the factorial normalization, natural integrality,
and a new fourth-iterate congruence, which that module does not supply.

## Gap

The main OEIS entry remains conjectural in retrieved revision 23. The linked
Library note records bounded searches and their failures. A coefficient
identity over Rat alone does not justify an integer remainder statement;
integrality and the zero-constant substitution conditions must be proved.
No claim of exhaustive literature search or first-publication priority is made.

## Route

Define integer composition by the chain-rule recurrence
`C(f,g)(0)=f(0)` and
`C(f,g)(n+1)=Σ(i=0..n) binomial(n,i) C(shift f,g)(i) g(n-i+1)`.
Prove its exact correspondence with factorial-normalized rational FPS
composition when g has zero constant coefficient. This independently gives
natural integrality and compatibility with coefficient reduction.

For `F=X exp(X)`, compute the square's EGF coefficient as
`Σ(k=0..n) binomial(n,k) k k^(n-k)`. Modulo two it equals
`n*2^(n-1)`, hence F squared is X+2H with integral EGF H.
Composition congruence then yields F fourth congruent to X modulo four.
This is the preregistered derivative-recurrence refinement of the proposed
Bell route. The natural fixed-point approximations preserve F's residues
and stabilize degree by degree, giving both the exact solution and its
modulo-four theorem. The companion result proves the proposed statement
that every nonlinear EGF coefficient of A fourth is a multiple of four.

## Falsifier

Any n≥1 at which the actual EGF coefficient is nonintegral or is not
congruent to n modulo four would falsify the claimed result or its source
identification. A second zero-constant rational fixed point would falsify
the uniqueness claim. Merely testing finitely many n cannot prove either.

## Evidence

The three modules are in the registered `D5/S1/Recurrence/Residue` bucket:
`IntegralEGFComposition`, `QuarticEGFFixedPoint`, `QuarticEGFModFour`.
The declarations `unique_solution`, `A_equation`, and
`integral_coefficients` establish the exact formal object. The final
declarations are `mod_four` and `fourth_coeff_divisible`.

A worker-owned Fraction/Horner program independently recomputed n=0..34:
the caller's ten terms agree, all A and B EGF denominators are one, and
both modulo-four checks have zero failures. This diagnostic computation is
separate from the all-n Lean proofs.

## Triage

`theorem`. The target is the single modulo-four assertion for the exact
OEIS series. The construction, integrality and uniqueness theorems discharge
its semantic prerequisites. The three file checks passed, and the two final
theorems printed only the standard three axioms. Repository admission and
merge status are reported separately by the implementation receipts.

## ASSUMED-UNVERIFIED

The main JSON, original triage paragraph and listed Mathlib source declarations
were independently read. The triage seat's review of all seven referenced
entries and the modulo-three supporting text remains attributed reporting;
it has not been repeated here. Google and Bing failed to provide usable
literature evidence. The exact GitHub Lean-code and arXiv phrase searches
are bounded, not exhaustive. The worker did not inspect every OEIS revision.

The kernel verifies the rational-series characterization and the arithmetic
theorems, not the external OEIS page. Identification with OEIS uses the
retrieved defining equation and the separately checked initial terms.
The implementation is by one Codex main thread with lean4 skill; no independent
review, multiple-model consensus, or runner verdict is claimed by this worker.
