---
slug: mathar-a174193-order-four-recurrence
bibkey: mathar2016a174193
doi: null
url: https://oeis.org/A174193
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.result
---

# Mathar's OEIS A174193 order-four recurrence

## Problem

R. J. Mathar's unnumbered FORMULA entry for OEIS A174193 gives the algebraic
series
\[
\frac{1-8x+13x^2+24x^3-48x^4-(1-6x+x^2+34x^3-26x^4-4x^5)\sqrt{1-4x}}{2x^2(1-x)(1-4x)^2}
\]
and conjectures the displayed order-four recurrence for its coefficients. The
formal statement uses rational power series, a branch $s$ with constant
coefficient one and $s^2=1-4X$, and the cleared equation $DA=P-Bs$. It asserts
existence of such a source series and the recurrence for every such series and
every natural $n\ge4$.

### Statement echo

The Lean `claim` contains the existence conjunct, the universal source-series
predicate, the guard $4\le n$, natural lagged indices $n-1$ through $n-4$, and
the five rational polynomial coefficient terms exactly. `IsSourceSeries` contains
$\exists s$, $s(0)=1$, $s^2=p$, and $DA=P-Bs$.

## Motivation

The source still labels the recurrence a conjecture. The settling declaration
is `D5.S1.Recurrence.Algebraic.MatharA174193OrderFourRecurrence.result`,
preregistered in [issue #24106](https://github.com/the-omega-institute/trureturing/issues/24106).
The identification of this algebraic series with the counting series of
$\operatorname{Av}(321)^{+1}$ and the background paper's Section 4 questions
are separate claims.

## Gap

The literature screen recorded in issue #24106 found no published settlement
within its checked scope. The OEIS entry remains labelled “Conjecture”; the
recurrence is absent from arXiv:2007.15111v1 and from the screened related
sources. The screen is partial, and completeness is `ASSUMED-UNVERIFIED`.

## Route

Map Mathlib's Catalan series to rational coefficients and set
$s=1-2XC$. The Catalan equation gives $s^2=1-4X$; polynomial normalization
shows $P-Bs$ has a factor $X^2$, and a unit denominator constructs a source
series. Differentiating $DA=P-Bs$ twice and clearing the nonzero factors gives
an inhomogeneous second-order Euler identity with cubic right-hand side $H$.
Two explicit polynomial certificates cancel the square-root terms. Since the
coefficients of $H$ vanish above degree three, coefficient extraction at
$n\ge4$ gives the recurrence. The reused Euler-coefficient theorem is
`D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff`.

## Falsifier

A source series satisfying the stated branch and cleared equation whose
coefficient recurrence fails at some natural $n\ge4$ would refute the claim.
A failure of the permutation-counting identification would not refute this
formal algebraic claim.

## Evidence

The kernel-checked declaration is
`D5.S1.Recurrence.Algebraic.MatharA174193OrderFourRecurrence.result`.
Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.
The source note is `Library/Words/mathar2016a174193.md`.

The independent checker is in
`the-omega-institute/trureturing-experiments` at commit
`b7f0518818771c2150a082e79fdfe6abffd8598e`, path
`docs/reports/mathar-a174193/check.py`; its SHA-256 is
`38ed870ab06543b0ba8dffcac775a263b844902ff5fbd34f81c0432f1335bfbb`.
The command `python3 docs/reports/mathar-a174193/check.py` exits 0 and reports
`ALL_CHECKS_OK`. It checks the two polynomial certificates, 30 displayed OEIS
coefficients, 197 recurrence residuals for $4\le n\le200$, hook-length values
through 25, and deletion counts through 7.

## Triage

- **The exact algebraic source series exists, and every source series satisfies the stated recurrence for all $n\ge4$.** Proved by the kernel-checked `result`; the existence and universal clauses are both in `claim`.
- **The source equation yields $LA=H$ with $H$ cubic; this is the cancellation mechanism that gives the order-four recurrence.** Proved on the live path of `result` by the consumed `inhomogeneous` identity and the two polynomial certificates.
- **The independent checker verifies both polynomial certificates, all 30 displayed OEIS coefficients, 197 recurrence residuals ($n=4,\ldots,200$), the hook-length values through 25, and deletion counts through 7.** Computed by `python3 docs/reports/mathar-a174193/check.py` at the pinned experiment commit; exit 0 and the script SHA-256 above. These finite checks are corroboration.
- **Identification of the source series with the counting series of $\operatorname{Av}(321)^{+1}$ is outside the claim and remains unproved here.** Open; no declaration in this module states that identification.
- **The background paper's Section 4 injection and all-$t$ questions remain unproved here.** Open; they are outside `claim` and have no declaration in this module.
- **For every formal root $s$ with $s^2=p$, the cleared first and second derivative identities hold; `root_derivatives` requires only the square equation.** Proved by the consumed `root_derivatives` declaration on the live path to `inhomogeneous` and `result`.
- **A general theorem for other rational combinations of algebraic roots is not delivered; this proof establishes the fixed stated coefficients.** Open; the module contains only the fixed A174193 coefficients.

### What the settlement shows

The cancellation identities remove the normalized square-root component from a
second-order Euler operator and leave a cubic forcing term. The result therefore
settles the exact all-index recurrence for every formal source series satisfying
the cleared algebraic equation, while leaving the permutation interpretation,
Section 4 injection, all-$t$ questions and a general root-combination theorem
open.

The escape audit is unfinished under
[issue #25507](https://github.com/the-omega-institute/trureturing/issues/25507)
for `result` and the published owner
`D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff`; no
`declared_validated` registration is claimed without the required CI reading.

## ASSUMED-UNVERIFIED

The literature screen is bounded and does not establish worldwide completeness,
priority, or the absence of a later independent proof. The publisher version
of the background article and several later citing works were not fully read.
The escape-audit registrations remain unfinished until their typed evidence and
required CI `current` DTR readings exist.
