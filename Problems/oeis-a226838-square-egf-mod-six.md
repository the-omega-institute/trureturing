---
slug: oeis-a226838-square-egf-mod-six
bibkey: hanna2013a226838
doi: null
url: https://oeis.org/A226838
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/HannaA226838Congruence.result
---

# Hanna's square-exponent EGF congruence modulo six

## Problem

Paul D. Hanna's OEIS A226838, revision #14, states in NAME:

> E.g.f.: exp( Sum_{n>=1} x^(n^2) / n^n ).

Its FORMULA asks:

> a(n) == 1 (mod 6) (conjecture - valid up to n=1024; if true for n>=0, why?).

The offset is `0,5`. The exact source is
https://oeis.org/A226838, with public history at
https://oeis.org/history?seq=A226838. The Library source note is
`Library/RecurrenceComposition/hanna2013a226838.md`.
The immutable preregistration is
[#23866, comment 6507420858](https://github.com/the-omega-institute/trureturing/issues/23866#issuecomment-6507420858).
The source's finite check is attributed to the source; it is not a universal proof.

### Statement echo

Over $\mathbb Q[[X]]$, set
$H(X)=\sum_{m\ge1}X^{m^2}/m^m$ and $A(X)=\exp(H(X))$.
For every $n\in\mathbb N$, including zero, there exists $k\in\mathbb Z$ with
$(n!:\mathbb Q)[X^n]A=1+6(k:\mathbb Q)$.
There is no integrality assumption or finite cutoff. The denominator is $m^m$,
not $m!$, and the exponent is $m^2$, not a triangular number.

The public `H` is the coefficientwise guarded `finsum` over natural indices;
private `coeff_H` proves its degree-n support lies in `range(n+1)`.
The public `A` substitutes `H` into the rational formal exponential.
The public `innerIntegral(n)` sums the natural quotient $n!/m^m$ over
$0\le m\le n$ with $0<m$ and $m^2=n$, zero otherwise.
The private `factorial_ratio` and `eCoeff_H` identify its rational cast with
$n![X^n]H$. The sole public theorem `result` is the exact all-index assertion.

## Motivation

The result GID is `D5/S1/Recurrence/Residue/HannaA226838Congruence.result`.
The admission basis is `open-problem-resolution`, under the
preregistered external named open-problem exception. Conservative proof shape
is `bind-only`; no separate escape witness or general EGF engine is claimed.
The remaining declarations are three source definitions and nine consumed
private helpers, whose live dependency paths are retained in the admission form.
Utility is `none`: this is an unbounded symbolic argument, not finite enumeration,
a checker, numerical reduction or a certified finite instance.

## Gap

Integrality and congruence must hold for the original rational EGF at every
natural index. Finite agreement or a recurrence with an assumed integral solution
would not discharge that assertion. The proof establishes the actual integral
coefficient bridge before reducing modulo six.
The retained Reg family compiles, but its binding is `declared_unresolved`,
certificate null, `IE-C050 ClosedTruthReadout`, `source.actual_observation`.
The missing accepted source-observation binding is tracked under
[#23884](https://github.com/the-omega-institute/trureturing/issues/23884)
by the CLAUDE §3.9 linked-issue exception. No audit completion is claimed.

## Route

For every positive $m$, $m^m$ divides $(m^2)!$.
For every $m\ge2$, $6m^m$ divides $(m^2)!$: the proof treats $m=2,3$
directly. For $m\ge4$, $6\mid(m-1)!$ gives $6m\mid m!$;
$(m!)^m\mid(m^2)!$ follows from product-factorial divisibility, and
$6m^m\mid(6m)^m$ completes the chain.
Consequently the actual integral inner coefficient sequence is one at index one
and zero elsewhere modulo six; its constant coefficient is zero.

Existing `IntegralEGFComposition.eCoeff_composition` and `eCoeff_exp`
identify the normalized outer coefficients with integral composition.
`composition_map` transports the integral sequence to $\mathrm{ZMod}(6)$,
and the original private `QuarticEGFModFour.composition_identity_right`
evaluates the identity substitution. For $m\ge2$, positive-index power
divisibility follows from the stronger local mod-six divisibility; $m=1$ is
immediate. The product-factorial step uses the pinned Mathlib theorem
`Nat.prod_factorial_dvd_factorial_sum`. The frozen composition supplier is
used without modification or exposure.
The result is one at every natural index, including zero; integer divisibility
then supplies $k$ and the exact rational equality.
No homomorphism from $\mathbb Q$ to $\mathrm{ZMod}(6)$ is used.

## Falsifier

The assertion would fail at any natural index with a nonintegral normalized
coefficient or residue different from one modulo six. The kernel-checked result
excludes both within the stated rational formal-power-series interpretation.

## Evidence

The mathematical source is
`D5/S1/Recurrence/Residue/HannaA226838Congruence.lean`, SHA-256
`7fc9391bac1fdbd24cbaf003367a4882abd50f3a49c03508be1ea55483ea9834`.
Its result statement identity is
`sha256:2a860207ee9913dd8379d7b22c17e7adba350bbb21e6b50e386b7dc2f3a397d1`.
The source and all accepted dependencies use only `Classical.choice`,
`Quot.sound` and `propext`.
Freeze membership and current registration status remain machine-owned.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Original all-index integral mod-six assertion | proved; kernel-checked | Exact original rational EGF and integer witness for every natural n including zero. |
| Integral normalization of H | proved; kernel-checked | `power_dvd_square_factorial`, `factorial_ratio`, `coeff_H`, `eCoeff_H`; original denominator and locally finite support. |
| Inner identity residue | proved; kernel-checked | `six_power_dvd_square_factorial`, `inner_mod_six`; transferred through existing integral composition. |
| Finite numerical check | source-reported only | The source reports n<=1024; no independent numerical result is asserted. |
| Four-slot registration | unresolved | The compiled typed family has no accepted binding certificate; `source.actual_observation`, #23884. |
| Larger moduli or other sparse exponent/denominator pairs | unresolved | No extension theorem is established. |
| Implication of arXiv 2610.11648v2 | no exact implication established by the completed focused reading | Conditional p-adic criteria were read; target coefficient/decomposition, period/strength/base-value, all-index and global-integrality bridges remain unverified. These premises are not claimed false and the method is not ruled out. |

The decisive mechanism is divisibility of the actual normalized inner
coefficients followed by the existing integral-composition transport.
It suggests testing other sparse series whose normalized inner coefficients
reduce to the identity, but neither a general extension nor its admission
is established here.

### Literature boundary

The source history contains fourteen revisions; revision 11 states the
FORMULA lower bound as zero. No exact full answer was located in the checked
weighted-permutation, Hurwitz-series, EGF-composition and related statements. Missing or challenged web
responses are not absence evidence. The proof is repository-derived and is not
attributed to the OEIS entry.

An independent focused reading of Yuta Nishibuchi, *A Unified Framework for
p-adic Congruences and p-adic Interpolations of Sequences*, arXiv:2610.11648v2,
established no exact implication for this series in that source. The checked
records are the [history](https://arxiv.org/abs/2610.11648), [v2
abstract](https://arxiv.org/abs/2610.11648v2), [HTML](https://arxiv.org/html/2610.11648v2),
[PDF](https://arxiv.org/pdf/2610.11648v2), and [source
archive](https://arxiv.org/src/2610.11648v2). The paper supplies conditional
p-adic criteria, but applying them here would require target-specific
normalized coefficient valuations or a valid decomposition, the correct
period, prime strength, and base-value links for both p=2 and p=3, all-index
coverage including zero, and a global integrality bridge to an integer witness.
These conditions remain unverified for this series. This reading does not
claim that the conditions are false or rule out the method, and it does not
establish a global novelty or priority claim. The paper is prior-work context,
not the identifier of the OEIS source and not an asserted proof of this
conjecture.

## ASSUMED-UNVERIFIED

Literature completeness and first-proof priority remain `ASSUMED-UNVERIFIED`;
unindexed, differently phrased or unpublished proofs have not been excluded.
An unresolved registration is neither a theorem of undecidability nor a claim
that a residual is inexhaustible.
