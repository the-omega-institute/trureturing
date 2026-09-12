---
slug: oeis-a378580-quotient-theta-composition-mod-four
bibkey: hanna2025a378580
doi: null
url: https://oeis.org/A378580
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour
---

# Coefficients of the A378580 quotient theta composition modulo four

## Problem

OEIS A378580 (Paul D. Hanna, Jan 08 2025) gives the following NAME and
COMMENT, quoted verbatim from `Library/ArithSums/hanna2025a378580.md`.

NAME:

> G.f. A(x) satisfies: A(x/A(x)) = theta_3(x) = 1 + 2*Sum_{n>=1} x^(n^2).

COMMENT:

> Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is square, else a(n) is divisible by 4 if n is nonsquare.

Here A has integer coefficients and constant coefficient one; x/A(x) means
X times its formal unit inverse. The Lean construction and uniqueness theorem
identify the sequence defined by this quotient equation.

## Motivation

This is a first-tier OEIS conjecture from 2025. KPI = open problems resolved.
The target proves the residue assertion for every positive natural index.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not repeat
those searches. The missing formal step was comparison of quotient
substitution arguments, rather than product substitution arguments.

## Route

The escape content is `inverse_agreement`: for power series with constant
coefficient 1, the inverse-difference identity
`f⁻¹ − g⁻¹ = f⁻¹ * (g − f) * g⁻¹` shows that divisibility of `f − g` by
`X^d` survives inversion, so `X/f` and `X/g` agree one degree further.
`quotient_triangular` uses that to compare the quotient substitution arguments
and isolate the degree-n outer difference. This makes the triangular
construction and its uniqueness work for `A(x/A(x))`.

This is exactly the step the frozen sibling
`D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour` does not have. According
to the supplied probe-seat report, importing that sibling and applying its
uniqueness theorem was rejected at the hypothesis `A(X*A) = theta`: its
triangular lemma only compares `X*f` with `X*g`.

Over `ZMod 4`, the reduced theta series T has form `1 + 2*S`, hence `T*T = 1`.
Its unit inverse therefore equals itself. For this reduced candidate, quotient
and product substitutions coincide. The two entries consequently have
word-for-word identical residue conclusions while defining different integer
sequences: uniqueness is argued over the integers, where the substitutions
differ. Modulo four, quotient uniqueness identifies the constructed series
with T, and extracting coefficients proves both residue biconditionals.

The lane imports the frozen sibling for its theta series, product generating
equation, and mod-four identity. Generality is I, and that module is a freeze
prerequisite. Its private helpers were not importable; minimal agreement and
construction helpers were re-proved locally.

## Falsifier

A positive counterexample index n for the integer solution of `A(x/A(x)) =
theta_3(x)` would falsify the claim: a square n with `a(n) % 4 != 2`, or a
nonsquare n with `a(n) % 4 != 0`. The orchestrator's exact check is supporting
evidence only; it does not replace the theorem quantified over every n > 0.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `coeff_thetaSeries` (imported from the frozen sibling),
  `generating_equation`, `generating_unique`, and `mod_four_identity`.
- Public escape lemmas: `inverse_agreement` and `quotient_triangular`.
- Axioms: std3, namely `propext`, `Classical.choice`, and `Quot.sound`.
- The Scribe resolution claim is attached only to `hanna_conjecture`.

## Triage

`theorem`. The formal proof closes both universal residue assertions for the
unique constant-one integer solution of the quoted quotient equation.

## ASSUMED-UNVERIFIED

The verbatim quotes and attribution were supplied by the orchestrator. The
OEIS entry and revision history were read by the search seat on 2026-09-09,
not by this network-disabled seat. The reported literature scope was
identifier search on arXiv, MathOverflow, and GitHub; it was not an exhaustive
search of all literature or private indexes. The probe-seat rejection and
orchestrator's exact numerical check were supplied reports. First-publication
priority and the external source-to-Lean identification are not kernel-checked
facts.
