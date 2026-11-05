---
slug: oeis-a226839-triangular-egf-mod-three
bibkey: hanna2013a226839
doi: null
url: https://oeis.org/A226839
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/HannaA226839Congruence.result
---

# Hanna's triangular-exponent EGF congruence

## Problem

Paul D. Hanna's OEIS A226839, returned revision 11, gives the NAME:

> E.g.f.: exp( Sum_{n>=1} x^(n*(n+1)/2) / n! ).

Its FORMULA is:

> a(n) == 1 (mod 3) (conjecture - valid up to n=1024; if true for n>=0, why?).

The offset is `0,4`. The immutable preregistration is
[#23823](https://github.com/the-omega-institute/trureturing/issues/23823#issuecomment-6505813924).
The source note is `Library/RecurrenceComposition/hanna2013a226839.md`.
The source question and source editorial approval do not supply a proof.

### Statement echo

Over $\mathbb Q[[X]]$, set
$T_m=\lfloor m(m+1)/2\rfloor$,
$H(X)=\sum_{m\ge1}X^{T_m}/m!$ and $A(X)=\exp(H(X))$.
For every $n\in\mathbb N$, including zero, there is a $k\in\mathbb Z$ with
$(n!: \mathbb Q)[X^n]A=1+3(k:\mathbb Q)$.

The public definitions `triangular`, `H` and `A` retain the literal
exponent, coefficientwise positive-index rational sum and formal exponential
substitution. The denominator is $m!$, not $T_m!$.
The private `coeff_H` proves local finiteness using $m\le T_m$.
The public `innerIntegral` is the natural finite sum over $0\le m\le n$
of $(m+1)^{\overline{n-m}}$ when $0<m$ and $T_m=n$, zero otherwise.
The private `factorial_ratio` and `eCoeff_H` derive its equality to
$n![X^n]H$. There is no assumed integer representation or finite cutoff.
The sole public theorem `result` is exactly the displayed all-index event.

## Motivation

The settling GID is
`D5/S1/Recurrence/Residue/HannaA226839Congruence.result`.
Its admission basis is `open-problem-resolution`, under the preregistered
external named conjecture exception. Conservative proof classification is
`bind-only`; the settlement of the external assertion supplies the admission
basis. All other declarations are definitions or live consumed helpers.
There is no asserted independent escape witness or new general EGF engine.
Utility is `none` for this unbounded symbolic argument.

## Gap

The source's integrality and congruence must hold for the original rational
EGF, so an integer recurrence or finite agreement would be insufficient.
The proof derives the exact integral coefficient bridge before modular
reduction. The four-slot audit remains unfinished under
[#23839](https://github.com/the-omega-institute/trureturing/issues/23839).
The typed Reg family compiles its equivalence, actual-positive, variation,
sensitivity and dependence proofs, but its binding record is
`declared_unresolved`, `source.residual_requires_open`, certificate null.
No registration completion is claimed.

## Route

For $T_m=n$, the normalized inner coefficient is
$n!/m!=(m+1)^{\overline{n-m}}$.
For $m=1$ it contributes one at degree one.
For $m=2$ the ratio is three.
For $m\ge3$, $T_m-m\ge3$, and the rising factorial contains a multiple of
$3!$, hence of three. Thus the actual integral inner coefficients reduce
modulo three to the identity sequence, with zero constant term.

The existing `IntegralEGFComposition.eCoeff_composition` identifies the
coefficients of the source exponential with integral composition.
`composition_map` transports this integral composition to
$\mathrm{ZMod}(3)$, and the original private
`QuarticEGFModFour.composition_identity_right` evaluates composition with
the identity. The output is one at every index, including zero.
Integer divisibility gives the displayed witness $k$.
No homomorphism from $\mathbb Q$ to $\mathrm{ZMod}(3)$ is used.

## Falsifier

The exact assertion would fail at any natural index with a nonintegral
factorial-normalized source coefficient or a residue different from one
modulo three. The kernel-checked result excludes both within the stated
rational formal-power-series interpretation.

## Evidence

The Lean source is
`D5/S1/Recurrence/Residue/HannaA226839Congruence.lean`; the Blueprint
renders all four public definitions and the full quantified result.
The result uses only `Classical.choice`, `Quot.sound` and `propext`.
Mathematical identity and freeze state are owned by canonical machine
artifacts, not this dossier.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Original all-index integrality and mod-three assertion | proved; kernel-checked | Public `result`, every natural index including zero, original rational EGF. |
| Actual integral normalization of H | proved; kernel-checked | Private `factorial_ratio`, `coeff_H`, `eCoeff_H`; original denominators and locally finite support. |
| Identity residue of the inner coefficients | proved; kernel-checked | Private `ratio_dvd_three` and `inner_mod_three`; transferred through existing integral composition. |
| Coefficient computation or finite experiments | not computed | No experiment or numerical check was run for this delivery. The source's reported n<=1024 check is attributed only. |
| Escape registration | unresolved | Compiled typed family; current binding report unresolved under #23839. |
| Stronger moduli or other exponent sequences | unresolved | No additional theorem is delivered. |
| A226838 | unqualified | Source-linked possible successor only; no open or solved status claimed. |

The decisive mechanism is divisibility of the actual factorial ratio,
followed by the existing integral composition transport.
The proof identifies conditions useful for similar source series, but no
additional extension is claimed proved. No other source assertion or
previous mathematical settlement is changed by this result.

### Literature boundary

The current OEIS record retains its conjecture wording.
The bounded repository/private, pinned Mathlib and third-party Lean screens
found existing general EGF machinery but no exact settlement.
The exact-ID arXiv, Crossref, MathDB, MathOverflow, Math StackExchange and
formal-conjectures screens located no exact answer.
An arXiv Hanna/EGF query located the abstract of
Heninger–Rains–Sloane, `math/0509316v4`, concerning a different Hanna
conjecture; its full text was not checked.
Challenged or irrelevant general-web results supply no absence evidence.
The available history readings establish the source's explicit zero-index
scope; not every standalone historical revision was read.

## ASSUMED-UNVERIFIED

Literature completeness and first-proof priority remain
`ASSUMED-UNVERIFIED`: differently described or unindexed proofs, unpublished
ownership and a full citation graph were not excluded.
The source note supplies the exact provenance and limits.
The unresolved registration is disclosed under #23839 and is not a theorem
of undecidability or an assertion that the residual is inexhaustible.
