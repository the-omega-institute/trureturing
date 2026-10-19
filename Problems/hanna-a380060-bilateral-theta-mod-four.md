---
slug: hanna-a380060-bilateral-theta-mod-four
bibkey: hanna2025a380060
doi: null
url: https://oeis.org/A380060
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour
---

# Hanna's bilateral theta congruence, OEIS A380060

## Problem

Paul D. Hanna's OEIS A380060 defines the generating function by:

> G.f. A(x) satisfies A(x) = Sum_{n=-oo..+oo} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n.

The Comments state:

> The term x^(n^2) * (A - x^n)^n/(1 - x^n*A)^n is invariant under sign reversal of n.

> Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is a square, and a(n) is divisible by 4 when n is nonsquare.

Formula (2) states:

> A(x) = 1 + 2*Sum_{n>=1} x^(n^2) * (A(x) - x^n)^n/(1 - x^n*A(x))^n.

The source is [OEIS A380060](https://oeis.org/A380060), with its citation in
[the Library note](../Library/RecurrenceComposition/hanna2025a380060.md).
Preregistration: [#18872](https://github.com/the-omega-institute/trureturing/issues/18872).

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Bilateral generating equation | `IsGF` uses the source's formula (2) over rational power series | The zero term is one and opposite indices coincide; no separate Lean Laurent-series folding theorem is asserted. |
| Infinite sum | Degree $m$ is read from indices $1\le n\le m$ | Each summand contains $X^{n^2}$, so omitted indices contribute zero. |
| Coefficients $a(n)$ | `coeff n A` | Every rational solution of `IsGF` is quantified. |
| Positive index | Natural $n$ with $0<n$ | Degree zero is excluded from the residue assertion. |
| Integer coefficients | An integer $z$ with `coeff n A = (z : ℚ)` | Integrality is a conclusion. |
| Residue two iff square | $z\equiv2\pmod4\iff\operatorname{IsSquare}(n)$ | Both directions are included. |
| Divisible by four otherwise | $\neg\operatorname{IsSquare}(n)\Rightarrow4\mid z$ | Integer divisibility. |
| A generating function exists | The existence conjunct of `claim` | Additional existence, rather than an extra hypothesis restricting the conjecture. |

The public definitions `IsGF` and `claim` are the literal conventions in
#18872. The reused `Agree` and `squareSupport` definitions retain their
original bodies. No source clause is dropped.

## Motivation

The residue pattern identifies exactly which positive coefficients have
2-adic valuation one. The result concerns every positive index and every
rational solution of the generating equation.

## Gap

The literature screen recorded in #18872 found no proof or refutation of
A380060 in the entry, the searched OEIS-proof papers, or the searched formal
conjecture catalogues. Completeness is `ASSUMED-UNVERIFIED`.
The mathematical connection is between the implicit rational series and
an integral coefficient iteration whose reduction is a square-support series.

## Route

Write
$T_m(B)=X^{m^2}(B-X^m)^m(1-X^mB)^{-m}$ and
$F(B)=1+2\sum_{m\ge1}T_m(B)$.
The denominator has constant coefficient one for $m>0$. If two series
agree below degree $d$, their images under $F$ agree below degree $d+1$.
Iterating from one therefore stabilizes every coefficient and constructs
an integer fixed point. The same agreement induction proves uniqueness;
coefficient homomorphisms identify any rational solution with the image
of this integer fixed point.

The proof directly uses the original `agree_pow` and `agree_mul` from
`UnitReversionSquareParity`, `inverse_agreement` and `map_inverse` from
`QuotientThetaCompositionModFour`, and `square_approximation` from
`BilateralQuarterShiftThetaModFour`. These are coefficient-agreement,
unit-inverse and positive-square support results respectively.

Modulo two the fixed-point equation gives $A=1$. Consequently
$T_m(A)=X^{m^2}$ modulo two. For positive $n$, the coefficient of $A$
is twice an integer whose parity is one exactly when $n$ is a square.
The settling theorem `result` turns that parity into the stated
congruence and divisibility conclusions.

## Falsifier

A positive index with a nonintegral rational coefficient, residue other
than two at a square, or a coefficient not divisible by four at a
nonsquare would contradict `result` under the specified equation.
A mismatch between the source's bilateral series and formula (2) would
concern the source-to-formalization bridge, not the Lean theorem.

## Evidence

The settling declaration is
`D5.S1.Recurrence.Invariants.HannaBilateralThetaModFour.result` in
[the Lean module](../D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.lean).
Its public conclusion is the full `claim`, including existence. The axiom
closure of every public declaration is contained in
`{propext, Classical.choice, Quot.sound}`.

### Experiment

[Exact coefficient and folding check](https://github.com/the-omega-institute/trureturing-experiments/tree/3eb5d149563112b44a7dd9de3e8ae722a37da8d1/docs/reports/oeis-a380060-hanna-bilateral-square-mod4).
Command: `python3 /tmp/op-hbsq-stage-b/experiment/check.py 400 /tmp/op-hbsq-stage-b/experiment/b380060.txt`,
using the two files extracted verbatim from that commit; exit 0.
Script SHA-256:
`ac4f3d2284a12019dad41fd71154e25adf3d94694f51a87a66e17127c30d0acb`.
The check verifies folding for $m=1,\ldots,6$, reproduces coefficients
$a(0),\ldots,a(400)$ from the b-file, and checks the fixed-point equation,
residues and half-coefficient square-support parity through degree 400.
These are computed finite checks, not evidence of an unbounded numerical check.

### Escape audit

The audit is unfinished in
[#19022](https://github.com/the-omega-institute/trureturing/issues/19022).
Its targets are the settling `result`,
`UnitReversionSquareParity.Agree`,
`UnitReversionSquareParity.agree_pow`,
`UnitReversionSquareParity.agree_mul`,
`BilateralQuarterShiftThetaModFour.squareSupport`,
`BilateralQuarterShiftThetaModFour.square_approximation`, and
`QuotientThetaCompositionModFour.map_inverse`.
Target-specific source reconstruction, enrolled readout and family-wide
variation evidence have not been supplied. The two published definitions are
included in this delivery's audit scope alongside the five theorem targets;
the theorem-only DTR rule does not supply a definition registration.
No validated registration is claimed.

## Triage

- **Settlement — proved in Lean:** `result` proves the complete residue conjecture under the binding conventions, for all positive indices.
- **Recommended next action — open:** independent final review and admission of the settlement; the Lean and Scribe use the original owner lemmas. This is a delivery boundary, not an unsettled residue assertion.
- **Counterexample or issue-step error — proved absent within the formal statement:** `result` rules out a violating coefficient under `IsGF`. No counterexample is supplied, and the source-to-formalization correspondence retains the boundary above.
- **Asymptotics — open:** the source's asymptotic formula is not addressed.

### What the settlement shows

- **Decisive mechanism — proved in Lean:** `result`, through the private `solution_fixed`, `solution_mod_two` and `halfCoeff_mod_two`, uses degree contraction and reduction modulo two. Half a positive coefficient has exactly the parity of positive-square support. Private `rational_unique` establishes uniqueness of the rational solution; uniqueness is not a separate public theorem.
- **Generalization — proved in prose:** for any integer series $B\equiv1\pmod2$, the constant-one denominator $1-X^mB$ is invertible, and $(B-X^m)^m(1-X^mB)^{-m}\equiv1\pmod2$. Thus $F(B)\equiv1+2\sum_{m\ge1}X^{m^2}\pmod4$. Every coefficient involves finitely many summands, so this calculation is coefficientwise valid. This is a mathematical consequence proved here in prose; no additional Lean theorem is claimed.
- **Companion A380680 — proved in prose for the residue mechanism:** replacing the quotient by $(2-X^m)^m/(1-2X^m)^m$ gives $X^{m^2}$ modulo two; its outer factor $X^{m^2}$ moves the support to $2m^2$. Its distinct settlement is tracked by [#18667](https://github.com/the-omega-institute/trureturing/issues/18667). No other claim about that sequence is settled by this module.
- **Finite numerical agreement — computed:** the experiment above covers degrees 0 through 400 and folding indices 1 through 6, with exit 0 and the pinned script hash. Extension of numerical checking beyond that range is open; the Lean residue theorem itself is unbounded.
- **Other source consequences — open:** no dependency of the source's asymptotic formula on the conjecture has been established. The congruence proof supplies no asymptotic estimate.

## ASSUMED-UNVERIFIED

Literature-search completeness and originality are `ASSUMED-UNVERIFIED`.
The source and literature checks are attributed in #18872 to the Claude Code
orchestrator and GPT Pro literature seat `s7999-gptpro-lit-hanna5`.
The screen includes the OEIS entry, OEIS Open arXiv:2608.11941,
S. Fried's cited OEIS-proof papers including arXiv:2606.09913 and
arXiv:2607.24832, A. Kallat's arXiv:2610.15849 catalogue,
arXiv:2410.07237, and the named GitHub conjecture collections.
No exhaustive literature coverage or first-proof priority is asserted.
The source's sign-reversal identity and formula (2) are the explicit
interpretation bridge; a universal Laurent-series folding theorem is
not part of this Lean delivery. The four-slot audit remains unfinished.
