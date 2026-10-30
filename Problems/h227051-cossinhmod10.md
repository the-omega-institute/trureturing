---
slug: h227051-cossinhmod10
bibkey: hanna2013a227051
doi: null
url: https://oeis.org/A227051
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.result
---

# Hanna's mixed trigonometric and hyperbolic congruence

## Problem

Paul D. Hanna's OEIS A227051, revision 10, first FORMULA states:

> a(n) == 3 (mod 10) for n>0 (conjecture).

Its NAME is “E.g.f.: 1/(cos(x) - sin(x)*sinh(x)), omitting the zero-valued coefficients of odd powers of x.” The source offset is `0,2`. Preregistration: [#21582](https://github.com/the-omega-institute/trureturing/issues/21582).

### Statement echo

Over $\mathbb Q[[x]]$, let $D(x)=\cos x-\sin x\sinh x$, $A(x)=D(x)^{-1}$ and $a_n=(2n)![x^{2n}]A(x)$. The five public definitions `sinhSeries`, `denominator`, `A`, `a` and `claim` retain these literal formal Taylor expressions. The factorial normalization uses the existing `IntegralEGFComposition.eCoeff` owner. The result states that for every natural $n\ge1$ there is an integer $z$ with $a_n=z$ in $\mathbb Q$ and $z\equiv3\pmod {10}$. The natural-number guard is exactly the source's positive-index condition; the existential integer makes integrality explicit. There is no finite cutoff or convergence hypothesis.

## Motivation

The frozen settling GID is `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.result`. Its admission basis is `open-problem-resolution (#21582; Proved)`. The result establishes the conjectured last digit for all positive indices of the source sequence.

## Gap

The congruence concerns the literal reciprocal, so an integer recurrence alone would not settle it. The private theorem `z_bridge` identifies every rational coefficient with the integer recurrence before any reduction modulo primes. The four-slot escape audit of the public `result` is unfinished: [#21976](https://github.com/the-omega-institute/trureturing/issues/21976). The guarded existential with rational equality and integer congruence lacks a verified full-telescope realization and sensitivity bridge; no registration is claimed validated.

## Route

Put $d_n=(2n)![x^{2n}]D(x)$. The finite Gaussian binomial identity gives $d_{2r}=1$ and $d_{2r+1}=-1-2(-4)^r$. The product $DA=1$ yields a triangular binomial convolution with diagonal coefficient $d_0=1$. Strong induction proves integrality and uniqueness of its inverse over any commutative ring. Its inverse modulo $2$ is the constant sequence $1$, while modulo $5$ it is $1,3,3,\ldots$. Coprimality combines the two residues into the source's modulo-$10$ statement.

## Falsifier

The source assertion would fail if a positive-index rational coefficient were nonintegral or its integer value had a last digit other than $3$. The kernel-checked `result` excludes both possibilities in the stated formal Taylor interpretation. The computed boundary $a_0=1$ explains the strict positive-index guard.

## Evidence

The Lean module is `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.lean`; `result` proves its full public `claim`. Its Blueprint renders the five definitions and the expanded quantified result. The source note is `Library/RecurrenceComposition/hanna2013a227051.md`. All formal coefficient identities take place over $\mathbb Q$ or $\mathbb Z$ before passing to residue rings; factorials are not inverted in those residue rings.

### Finite computation

[Experiment directory at c9c98088282dff637d01ad153bff1883546d7d3b](https://github.com/the-omega-institute/trureturing-experiments/tree/c9c98088282dff637d01ad153bff1883546d7d3b/docs/reports/hanna-a227051-mod10).

Command: `git -C ../trureturing-experiments show c9c98088282dff637d01ad153bff1883546d7d3b:docs/reports/hanna-a227051-mod10/check.py | python3`, exit $0$; script SHA-256 `51567856e7c316e150b9b3cba92e704546e3670daa9059a41082ff7feff62b58`. The immutable script was retrieved from this commit and executed unchanged with Python 3. It reproduces all $16$ published values, including $1,3,53,2333,191673,25307913,4900979093$; the full-product and odd-zero checks hold through degree $240$. Rational inversion and the integer recurrence agree for $0\le n\le120$; integrality and the denominator law hold over this tested range, and the positive-index congruences hold for $1\le n\le120$. The finite calculation is not evidence for an experimental all-index claim.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Distinct inverse residues and integrality | proved; kernel-checked | Private `z_bridge` identifies $a_n$ with an integer for every $n$; `z_two` proves residue $1$ modulo $2$ for every $n$; `z_five` proves residue $3$ modulo $5$ for positive $n$. Public `result` combines them. |
| Denominator law for every $r$ | proved; kernel-checked | Private `ec_den_even`, `ec_den_odd`, `d_even` and `d_odd` give the finite coefficient law and odd coefficient vanishing without analytic convergence or factorial inversion in a residue field. |
| Triangular inverse over any commutative ring | proved; kernel-checked | Private `conv_unique` quantifies over any commutative ring and any fixed denominator sequence with $d_0=1$. Its consumers `z_two` and `z_five` identify the two reduced inverse sequences. |
| Excluded boundary and published coefficients | computed | The experiment above gives $a_0=1$, all $16$ published values, and full-product and odd-zero checks through degree $240$. Its exact recurrence comparison is limited to $0\le n\le120$. |
| Stronger moduli and other mixed denominators | open | They need separate arguments; no assertion for them is delivered. |
| Independent OEIS asymptotic estimate | open | It is neither proved nor changed by this congruence result. |

The decisive mechanism is the parity-dependent denominator law together with triangular inverse uniqueness. The uniqueness lemma extends to arbitrary commutative rings with a denominator of constant term one; this is the extension actually proved here. No source result is claimed to depend on the conjecture, and its independent asymptotic statement is unaffected.

### Literature status

The bounded screen recorded in #21582 located no prior settlement. OEIS revision 10, arXiv identifier and author searches, indexed web screens, and the readable related papers supplied no matching proof. Carlitz's two relevant full texts were unavailable, and citation-discovery APIs returned rate limits. Kallat's logarithmic-weight criterion does not directly apply: the experiment gives $6[x^6]\log A=379/60$, whose denominator is divisible by $2$ and $5$.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the unread Carlitz texts and failed discovery APIs prevent a complete literature claim. The source is OEIS-only, with no DOI, arXiv identifier or journal version asserted. Stronger moduli, other mixed denominators and the independent asymptotic estimate remain open here. Escape registration remains unfinished under #21976.
