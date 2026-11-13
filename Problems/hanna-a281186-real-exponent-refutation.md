---
slug: hanna-a281186-real-exponent-refutation
bibkey: hanna2017a281186
doi: null
url: https://oeis.org/A281186/internal
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.result
---

# Hanna's A281186 real-exponent positivity conjecture

## Problem

Paul D. Hanna's sole COMMENTS conjecture in OEIS A281186, revision 10, states:

> Conjecture: if G(x) = exp( 1/G(x) * Integral G(x)^t dx ) for some fixed real t, then G(x) will consist entirely of nonnegative coefficients iff t >= 8/3.

The source normalization is $G(0)=1$, the primitive has constant coefficient zero, and $G^t=\exp(t\log G)$ in $\mathbb R[[x]]$. The source EGF is $A(x)=\sum_{n\ge0}a(n)x^n/(n!3^n)$; its positive normalizing factors preserve signs. Preregistration [#24155](https://github.com/the-omega-institute/trureturing/issues/24155) makes existence explicit for every real parameter.

### Statement echo

| Source clause or binding convention | Lean counterpart | Fidelity |
| --- | --- | --- |
| Fixed real exponent $t$ | `claim` quantifies over every $t:\mathbb R$ | Includes zero, negative and irrational parameters. |
| Source integral equation | `IsSourceSeries` | Its full body is the literal preregistered equation. |
| Normalization $G(0)=1$ | First conjunct of `IsSourceSeries` | Selects the normalized formal logarithm and unit inverse. |
| Zero-constant primitive | Existential $J$, constant coefficient zero, derivative $\exp(t\log G)$ | Expresses the source `intformal` convention without a duplicate integral operator. |
| Existence for every exponent | First conjunct of `claim` | An assertion of the claim, not an extra premise of `result`. |
| Entirely nonnegative coefficients | Every natural degree $j$, including zero | Ordinary coefficients and EGF coefficients have the same sign. |
| If and only if $t\ge8/3$ | Equivalence in the universal solution clause of `claim` | No parameter or degree bound. |
| Refutation | `result` | Literal closed type $\neg\,\mathtt{claim}$. |

All declarations are under `D5.S1.Recurrence.Algebraic.HannaRealExponentPositivityRefutation`; names below use that namespace. The public definitions are `IsSourceSeries` and `claim`. The sole public theorem is `result`; the coefficient and certificate lemmas are private.

## Motivation

The settling GID is `D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.result`. Its module has generality `I`, utility `kind=certified-instance` with `basis=refutes` directed to `claim`, and admission basis `open-problem-resolution (#24155; Refuted)`. It uses `deposit-uncovered` with no atom or cover.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Gap

The bounded literature screen in #24155 read the OEIS entry, JSON and history, related original papers, arXiv identifier and full-text searches, bibliographic indices and repository results. It found no settlement of this exact assertion. The A232692 certificate concerns a different source series; a negative coefficient of a series does not imply one of its cube. It does not settle this claim.

Literature completeness is `ASSUMED-UNVERIFIED`: author and citation discovery and several broader endpoints did not yield complete usable results. This is a source-specific refutation, not an exhaustive novelty or priority claim. The source note is [hanna2017a281186](../Library/Certificates/hanna2017a281186.md); the source has no DOI or arXiv identifier.

## Route

Assume `claim` and specialize to $t=8/3$. Its existence conjunct supplies a literal source series $G$. With $y=\log G$, differentiation gives $(1+y)y'=\exp((5/3)y)$. The private source bridge and weighted derivative invariant imply

$$ (n+1)![x^{n+1}]G=3^{-n}Q_n(0),\qquad n\in\mathbb N, $$

where

$$ Q_0(z)=1,\qquad Q_n(z)=((5n+3)z+6-n)Q_{n-1}(z)+3(1+z)Q'_{n-1}(z)\quad(n\ge1). $$

An integer-list recurrence implements these polynomials. Kernel reduction checks its literal checkpoint and the remaining updates, establishing $Q_{719}(0)<0$. Therefore $720![x^{720}]G<0$. The claim's threshold clause at $8/3$ makes the same expression nonnegative, a contradiction.

`result` has proof shape `content`: the arbitrary-order `derivative_certificate` remains on its proof path through `source_coefficient`. There are no D5 imports or direct frozen dependencies. The proof reuses pinned Mathlib's formal power-series and polynomial operations. Neither Python nor a decimal hash is a proof premise.

## Falsifier

A discrepancy in the literal source equation, normalization, coefficient bridge or certified sign would invalidate this route. The formal proof checks the preregistered real-series interpretation and literal negation. A proof of the same `claim` would contradict `result` within the accepted formal system. Independent existence of all source solutions and a corrected threshold are outside this theorem.

## Evidence

The kernel-checked declaration `result` refutes `claim`. Its private prerequisites include `source_coefficient`, `numeric_negative` and `Q_negative`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The independent experiment is [docs/reports/hanna-a281186 at 03afdbc2b42c9f2bc3608d6824f55073435e5c67](https://github.com/the-omega-institute/trureturing-experiments/tree/03afdbc2b42c9f2bc3608d6824f55073435e5c67/docs/reports/hanna-a281186). The exact committed `check.py` was extracted without modification and run as `python3 /Users/auric/.op-scratch/hanna-stageb/check.py`, exit 0, ending `ALL_CHECKS_OK`. Its SHA-256 is `0825fef221faa297ecf868184fa3917652b0fb7961cb12d392f7e94652ca767d`. The tested scope is the first 20 published terms, the source differential identity through degree 18, agreement of the integer and Lagrange recurrences at order 719, signs through degree 720 at $t=8/3$, and the stated rational exponential majorant. These computations do not prove an unbounded sign classification.

## Triage

| Item | Status and evidence kind | Evidence and exact scope |
| --- | --- | --- |
| Existence and positivity at $t=8/3$ conflict with the forced degree-720 coefficient | Proved; kernel-checked | `result`, the closed negation of the literal joint assertion. |
| Source-to-coefficient identity at every natural order | Proved; kernel-checked | Private `source_coefficient`: for every literal source series at $8/3$ and every $n\in\mathbb N$, $(n+1)![x^{n+1}]G=(1/3)^nQ_n(0)$. |
| Certified finite recurrence has $Q_{719}(0)<0$ | Proved; kernel-checked | Private `numeric_negative` and `Q_negative`; the literal checkpoint and terminal sign use kernel reduction, with no unchecked Python, decimal or hash premise. |
| First 20 terms match literal source iteration; integer and Lagrange recurrences agree | Computed | The experiment entry's command, exit 0 and SHA-256 above; degrees 0 through 19 and order 719 respectively. It also checks the source differential identity through degree 18. |
| Degrees below 720 are positive | Computed | The same experiment, at $t=8/3$, checks $0\le m<720$; degree 720 is negative. Formal minimality is not claimed. |
| Infinite negativity on $[8/3,267/100]$ | Open | The issue gives an analytic argument; this delivery neither formalizes nor independently analytically audits it. The checker verifies only its rational majorant. It is not used by `result`. |
| Corrected threshold, full real-parameter classification and eventual sign patterns | Open | No such theorem is delivered. The single boundary counterexample does not supply them. |
| Independent existence and uniqueness of every source solution | Open | Not separately formalized here; the assumed `claim` supplies the source series inside the contradiction. |

### What the settlement shows

The proposed sufficient threshold fails at its own boundary: any source series at $8/3$ has a negative degree-720 coefficient, while the claim asserts its existence and nonnegativity. The arbitrary-order coefficient identity survives as a kernel-checked private lemma. The source's initial 20 terms and its differential identity through degree 18 survive the independent computation; finite positive prefixes do not imply coefficientwise nonnegativity. No downstream paper relying on the conjecture was located in the bounded literature screen of #24155. The interval strengthening, all-real classification, eventual signs, independent existence and uniqueness, and formal minimality remain outside this settlement.

## ASSUMED-UNVERIFIED

Literature completeness and exhaustive priority exclusion are `ASSUMED-UNVERIFIED`. The bounded searches do not prove absence of all earlier settlements. The interval analytic argument is not an independently audited theorem of this delivery. The independent arithmetic experiment is a cross-check and is not part of the Lean trust basis.
