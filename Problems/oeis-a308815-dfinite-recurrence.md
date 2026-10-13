---
slug: oeis-a308815-dfinite-recurrence
bibkey: mathar2020a308815
doi: null
url: https://oeis.org/A308815
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/A308815DFiniteRecurrence.result
---

# Mathar's D-finite recurrence for OEIS A308815

## Problem

OEIS A308815, FORMULA section, states:

> Conjecture: D-finite with recurrence: n*(2*n+1)*a(n) -32*(9*n-4)*(n-1)*a(n-1) +1024*(3*n^2-23*n+29)*a(n-2) +65536*(n-2)*(2*n-5)*a(n-3)=0. - _R. J. Mathar_, Jan 27 2020

Its PARI definition is:

> a(n) = 16^n*sum(i=0, n, (-2)^i*binomial(n, i)*C(2*n-i));

Here $C_k$ is the ordinary Catalan number. Put

$$a_n=16^n\sum_{i=0}^n(-2)^i\binom ni C_{2n-i}.$$

For every natural $n\ge3$, the conjecture asserts

$$n(2n+1)a_n-32(9n-4)(n-1)a_{n-1}
+1024(3n^2-23n+29)a_{n-2}+65536(n-2)(2n-5)a_{n-3}=0.$$

The external tier-1 claim is preregistered in
https://github.com/the-omega-institute/trureturing/issues/15713.
The signed PARI formula is the sequence convention; the NAME line's
unsigned $2^i$ conflicts with the displayed data.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Natural sequence index and finite sum $0\le i\le n$ | `a308815`, `Finset.range (n+1)` | Exact natural indices; integer summands |
| $16^n(-2)^i\binom ni C_{2n-i}$ | `a308815`, Mathlib `Nat.choose` and `catalan` | Literal signed formula; natural subtraction at $2n-i$ |
| Every $n\ge3$ | `claim` | No extra hypothesis |
| Four recurrence coefficients and lags | `claim` | Integer coefficient arithmetic; natural lagged arguments |
| The recurrence equals zero | `result : claim` | Whole assertion proved |

## Motivation

Farkas, Moschetti, Naranjo and Pirola's Theorem 1.1, page 1 of
arXiv:1906.10406v2, identifies this signed sum with alternating Catalan
numbers and odd-cover counts for general curves of genus at least three.
The geometric counting theorem is cited, not formalized here.
The source locators are `Library/Geometry/farkas2021alternating.md`
and `Library/Words/mathar2020a308815.md`.

## Gap

The preregistration's bounded source and literature screen identifies the
Mathar recurrence as still labelled Conjecture. The recurrence is now proved
by `D5.S1.Recurrence.A308815DFiniteRecurrence.result` for all $n\ge3$.
Exhaustive historical absence of an inaccessible or unpublished proof is
not established by that screen.

## Route

Write $C(X)$ for Mathlib's ordinary Catalan power series over the rationals.
The imported `PowerSeries.catalanSeries_sq_mul_X_add_one` supplies its
quadratic equation. The private `cat_ode` differentiates it and eliminates
the square to obtain

$$X(1-4X)C'(X)+(1-2X)C(X)=1.$$

The private `b_sum` identifies
$b_n=[X^{2n}](1-2X)^nC(X)$ with the signed Catalan binomial sum;
`a_eq` gives $a_n=16^nb_n$ after the integer-to-rational cast.
For $n=m+3$, set

$$r_n(X)=-n+(n+1)X+(6n-6)X^2+(-2n-6)X^3+(8-4n)X^4,$$

$$H_n(X)=n(2n+1)(1-2X)^3
-2(9n-4)(n-1)X^2(1-2X)^2
+4(3n^2-23n+29)X^4(1-2X)+16(n-2)(2n-5)X^6,$$

and $U_n=(1-2X)^{n-2}(1-4X)r_n(X)C(X)$.
The private `certificate` proves the exact identity

$$XU_n'-2nU_n=H_n(X)(1-2X)^{n-3}C(X)+(1-2X)^{n-2}r_n(X).$$

The Euler derivative cancels the degree-$2n$ coefficient on the left.
The forcing polynomial on the right has degree at most $n+2<2n$.
`forcing_zero` and `annihilation` express these facts, and `b_recurrence`
extracts the four shifted coefficients. `result` scales by $16^n$ and
returns to the integers. This coefficient certificate implements the
annihilating operator; a separate differential equation for the generating
series of the binomial transform is not asserted as a Lean theorem.

## Falsifier

A mismatch with the signed source expression or an index $n\ge3$ violating
the recurrence would refute the target. The unsigned NAME formula is a
different sequence. Finite agreement alone is not the universal conclusion.

## Evidence

The mathematical source is `D5/S1/Recurrence/A308815DFiniteRecurrence.lean`;
its exposition is `Blueprint/D5/S1/Recurrence/A308815DFiniteRecurrence.scribe.cs`.
The only public theorem is
`D5.S1.Recurrence.A308815DFiniteRecurrence.result : claim`.
Its admission basis is `open-problem-resolution (#15713; Proved)`;
its proof shape is `bind-only`, with no escape witness and no direct frozen
D5 dependency. Private theorem helpers have live consumers. All statements
are symbolic and unbounded; none retains a numerical certificate, checker,
bounded enumeration or numeric reduction, so the module has `utility: none`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The positive public `result` is an escape-audit target. Its escape audit is
unfinished under https://github.com/the-omega-institute/trureturing/issues/15923.
The target has the `DTR-Unregistered` observation (effect Observe).
No Reg mirror is delivered. Missing evidence comprises an enrolled readout,
raw-source reconstruction and selection, variation, sensitivity,
observational dependence and a decoded typed registration.

### Experiment

The independent experiment is
[`docs/reports/oeis-a308815-dfinite-recurrence/`](https://github.com/the-omega-institute/trureturing-experiments/tree/606aeab68b46632c86a284c8793cc78c2171e440/docs/reports/oeis-a308815-dfinite-recurrence).
Measurement command: `python3 -c` on the pinned script bytes obtained by
`git show 606aeab68b46632c86a284c8793cc78c2171e440:docs/reports/oeis-a308815-dfinite-recurrence/check.py`; exit 0.
Rerun command: `python3 check.py` in that pinned directory.
The SHA-256 of `check.py` is
`d40f575913a33fcb60a373cfb2fb8bb80028ea340c3d255f780a485d87e6477b`.
The signed formula matches all 17 displayed terms, and the unsigned formula
does not. The recurrence has zero failures for $3\le n\le300$.
The quartic expression $4z(1+z)B^4-(1+4z)B^2+1$ has zero coefficients
through $z^{120}$. The implicit derivative agrees modulo the quartic,
and the factored differential-operator identity has difference zero.
These last two symbolic checks concern the experiment's route; they are
not additional kernel-checked theorems in this module.

## Triage

| Item | Status and evidence |
| --- | --- |
| Catalan quadratic and differential identity | Proved: imported Mathlib quadratic and private `cat_ode` |
| Signed binomial transform and coefficient certificate | Proved: private `b_sum`, `a_eq`, `certificate`, `forcing_zero`, `annihilation` and `b_recurrence` |
| The complete order-three recurrence | Proved: public `result`, all natural $n\ge3$ |
| NAME sign discrepancy | Source reading: the NAME line prints $2^i$, the PARI line prints $(-2)^i$ |
| Seventeen terms and finite recurrence range | Computed: pinned experiment above; exactly 17 terms and $3\le n\le300$ |
| Quartic generating-series relation and factored operator | Computed: pinned experiment above, coefficients through $z^{120}$ and its rational-function identities |
| Closed-form generating function | Open in this formalization: the paper's Theorem 1.2 provides a formula; it is not proved by this module |
| Asymptotics | Open in this formalization: the OEIS asymptotic formula is not proved by this module |

### What the settlement shows

The decisive mechanism is the kernel-checked coefficient certificate
`certificate`, with boundary cancellation in `forcing_zero` and
`annihilation`. It proves the recurrence at every admissible index,
including $n=3$, without division by an endpoint-dependent denominator.
The signed sequence and all four coefficients are fixed by the source;
no extension to other transforms or geometric counting statements is
claimed. The recurrence no longer needs to be assumed for this sequence.
The paper's geometric count and generating-function statements retain
their own hypotheses and evidence; this module does not replace them or
establish the OEIS asymptotic formula.

## ASSUMED-UNVERIFIED

The bounded literature screen does not certify exhaustive absence of
other historical proofs. The linked escape audit remains unfinished;
no completed four-slot registration is asserted. No additional mathematical
hypothesis is assumed in the recurrence proof.
