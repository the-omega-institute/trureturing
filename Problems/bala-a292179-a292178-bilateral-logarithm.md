---
slug: bala-a292179-a292178-bilateral-logarithm
bibkey: bala2025bilaterallog
doi: null
url: https://oeis.org/A292179
triage: theorem
motivation_gids:
  - D5/S3/Analytic/PowerSeries/BalaBilateralLog.full_event
---

# Bala's two-parameter bilateral logarithm identity

## Problem

Peter Bala's [OEIS A292179](https://oeis.org/A292179), revision 20,
has the following COMMENTS conjecture, pinned in
[oeis/oeisdata at 733c77ba475e0b6fa0b8abe7681ef040217ae7f7](https://github.com/oeis/oeisdata/blob/733c77ba475e0b6fa0b8abe7681ef040217ae7f7/seq/A292/A292179.seq):

> Conjecture: Sum_{n in Z - {0}} (x - a^n)^n / n = -log(1 - x) for |x| < 1 and |a| < 1. - _Peter Bala_, Mar 02 2025

[OEIS A292178](https://oeis.org/A292178), revision 27, states the same
question in its COMMENTS, pinned at
[571197984aeda7b8b680fe3a1f6a43f9898cd441](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A292/A292178.seq):

> More generally, it appears that Sum_{n = -oo..+oo, n <> 0} (x - a^n)^n / n = -log(1 - x) for |x| < 1 and |a| < 1. - _Peter Bala_, Nov 03 2024

These comments represent one problem. The source does not explicitly fix
the scalar field or logarithm branch. The binding event in
[#29113](https://github.com/the-omega-institute/trureturing/issues/29113#issuecomment-6786264041)
uses arbitrary complex parameters in the separate open unit disks and
the principal complex logarithm, and includes the ordinary real source
series with its real logarithm. Negative powers require nonzero a; the
raw expression at a=0 is undefined and is not assigned a value.

For every complex x,a with norm(x)<1 and norm(a)<1, put, for every m>=1,

$$p_m=\frac{(x-a^m)^m}{m},\qquad
q_m=\frac{(-1)^{m+1}a^{m^2}}{m(1-xa^m)^m},\qquad
F(x,a)=\sum_{m\ge1}p_m+\sum_{m\ge1}q_m.$$

The complete event asserts separate absolute convergence and
F(x,a)=-Log(1-x). For every such pair with a!=0 and every integer n!=0,
the ordinary powers and divisions in b_n=(x-a^n)^n/n are valid;
b_m=p_m and b_(-m)=q_m. The raw nonzero-integer family is absolutely
summable, and its unordered sum, the sum of its two tails and its
symmetric-truncation limit all equal F. For all real x,a with abs(x)<1
and 0<abs(a)<1 the value is -Real.log(1-x), including both signs.
For every fixed complex x in its disk, F is continuous in a at zero
and is the unique extension on the full a-disk continuous at zero and
agreeing with the punctured raw sum. No sign, diagonal, fixed-parameter,
combined-norm or smaller-disk restriction is imposed.

### Statement correspondence

All local names below belong to `D5.S3.Analytic.PowerSeries.BalaBilateralLog`.

| Event clause | Lean counterpart |
| --- | --- |
| The two separately defined tails, m>=1 | `positive x a k`, `negative x a k`, with m=k+1 |
| Their sum independent of the proposed value | `regularSum`, defined by two natural tsums |
| Full separate complex disks, absolute convergence, principal value | First block of `full_event`; includes nonzero tail denominators and Re(1-x)>0 |
| Every ordinary nonzero-integer term and negative-index correspondence | `raw` on nonzero parameter/index subtypes; second block of `full_event` |
| Absolute raw family, unordered/two-tail sums, symmetric truncations | Second block of `full_event`; truncations run over k=0,...,N-1 and hence source indices +/-1,...,+/-N |
| All real source parameters, both signs and real logarithm | `realRaw` and third block of `full_event` |
| Regular zero values, continuity and uniqueness on the full disk | Fourth block of `full_event`; arbitrary H continuous within the disk at zero and agreeing off zero is EqOn F there |

## Motivation

This is the tier-1 externally published two-parameter conjecture
preregistered in #29113, distinct from an already recorded diagonal
specialization. Its sole settling declaration is
`D5/S3/Analytic/PowerSeries/BalaBilateralLog.full_event`.
The owning Scribe attaches one `OpenProblemResolutionClaim(Proved)` to
that declaration and this slug. The admission basis is
`open-problem-resolution`; the unchanged module has `utility: none`.
Mathematical truth, admission, integration and literature novelty are
separate claims. The typed claim does not certify admission or delivery.

## Gap

Pinned Mathlib supplies negative-binomial summation, logarithm Taylor
summation, geometric convergence, product summability and Fubini.
The full source event requires their parameter correspondence, joint
absolute summability before cancellation, nonzero ordinary-power
bridges, real-log correspondence and the regular zero-extension
conditions. The bounded repository and supplier screen in #29113 did
not identify an existing full-event statement. It included private
originals in `FinalLaurentEvaluation`, whose integer-binomial wrappers
reduce to the same upstream choose supplier and whose coupled result
has a different combined-norm hypothesis. No separate escape witness
is claimed for this application of the suppliers.

## Route

Expand the finite positive row using coefficients
c(n,m)=(-a^n)^m*x^(n-m)*choose(n,m)/n for m>0 and zero for m=0.
Their norm row is bounded by (norm(x)+norm(a)^n)^n. With
rho=(1+norm(x))/2<1, the row is eventually bounded by rho^n.
Geometric comparison proves joint absolute summability before any
interchange. The finite binomial row gives ((x-a^n)^n-x^n)/n.
The pinned negative-binomial HasSum at x*a^(k+1) identifies each
column with -q_(k+1); absolute Fubini cancellation leaves the pinned
logarithm Taylor series. Ordinary integer-power normalization gives
the raw bridges, the full bilateral sum and its symmetric limit.
Complexification and positive 1-x give the real-log statement.
The regular sum is constant in a on the disk; the punctured
neighborhood filter at zero proves uniqueness of its continuous extension.

The proof classification is `proof_shape: bind-only` for `full_event`
and every private theorem below, after expanding the helper graph to
the pinned suppliers. The terminal uses the external-problem exception;
the helpers are allowed because of the actual consumers listed here.
There are no direct frozen D5 mathematical suppliers and no claimed
escape witness. Definitions have no theorem proof-shape classification.

| Private theorem | Actual consumers |
| --- | --- |
| `disk_product` | `denominator_ne`, `coefficient_column` |
| `denominator_ne` | `raw_field`, `full_event` |
| `envelope_summable` | `positive_norm_summable`, `coefficient_absolute` |
| `positive_norm_summable` | `regular_identity` |
| `coefficient_support` | `coefficient_absolute`, `coefficient_column`, `coefficient_row` |
| `coefficient_row_norm` | `coefficient_absolute` |
| `coefficient_absolute` | `regular_identity` |
| `coefficient_column_term` | `coefficient_column` |
| `coefficient_column` | `regular_identity` |
| `coefficient_row` | `regular_identity` |
| `regular_identity` | `bilateral`, `regular_continuous_zero`, `extension_unique`, `real_correspondence`, `full_event` |
| `integer_positive` | `bilateral`, `full_event` |
| `integer_negative` | `bilateral`, `full_event` |
| `bilateral` | `extension_unique`, `real_correspondence`, `full_event` |
| `regular_continuous_zero` | `full_event` |
| `extension_unique` | `full_event` |
| `raw_field` | `full_event` |
| `real_correspondence` | `full_event` |

The private `coefficient` definition is consumed by the coefficient
helpers and `regular_identity`; private `integerTerm` is consumed by
the integer bridges, `bilateral` and `full_event`. The five public
definitions describe the source families and their regular sum.

## Falsifier

A well-defined real source-domain pair with a different bilateral
value would refute the source assertion. Failure of an ordinary-power
bridge, absolute convergence, principal-log equality, real correspondence
or zero-extension clause would contradict the full event. A complex-only
counterexample would address the specified strengthening unless the
source's complex intent were independently fixed. The undefined raw
expression at a=0 supplies no counterexample.

## Evidence

The mathematical evidence is `full_event` in
[the D5 source](../D5/S3/Analytic/PowerSeries/BalaBilateralLog.lean), with
[the source-bound Reg reconstruction](../Reg/D5/S3/Analytic/PowerSeries/BalaBilateralLog.lean)
and [the owning Scribe](../Blueprint/D5/S3/Analytic/PowerSeries/BalaBilateralLog.scribe.cs).
The compiled theorem statement identity is
`sha256:cfa16b4f63ea3670ff516012c45819638398745620c257362a49a16d260c8285`;
its accepted axiom closure is `Classical.choice`, `Quot.sound`, `propext`.
The [canonical frozen module state](../Golden/Frozen/state/D5/S3/Analytic/PowerSeries/BalaBilateralLog.lean.json)
has statement identity
`sha256:a91c3224893d9bc66032f238309adae06a62c9e5e9db320c9e8614ae74066776`.
The pinned toolchain is Lean v4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The `declared_validated` Reg evidence reconstructs the entire nullary theorem, with its
quantifiers inside the proposition, and selects the original principal-log
function operand. Its rejected constant readout fails at x=a=0;
the actual logarithm readout is nonconstant on the complex state domain.
The continuation is unknown and asserts no undecidability conclusion.

The [source note](../Library/AnalyticClosure/bala2025bilaterallog.md)
owns the exact quotations and bounded supplier/literature scope.
The [mathematical settlement](https://github.com/the-omega-institute/trureturing/issues/29113#issuecomment-6787091681)
and [unchanged-event terminal](https://github.com/the-omega-institute/trureturing/issues/29113#issuecomment-6787097841)
fix the original mathematical answer and account independently of publication.
No numerical experiment substitutes for the kernel evidence.

## Triage

The full mathematical event is proved by the compiled declaration,
including the real source series and separately defined regular extension.
The paired OEIS entries count as one external source problem.
The declaration is canonically frozen under `open-problem-resolution`.
The typed Proved claim and this dossier agree on that settling declaration.
Independent prefreeze review is approved; the final independent review triplet,
required CI and integration into dev remain pending.
The result gives neither a value for the raw expression at zero nor an
assertion outside the stated disks. It establishes no worldwide priority
or exhaustive literature absence.

## ASSUMED-UNVERIFIED

The bounded qualification in #29113 inspected the source comments,
selected classical binomial/Lagrange/Lambert formulas, DLMF 17.8,
Schlosser's arXiv:math/0302270v4 theorem/corollary statements,
Horn's arXiv:math/0609689v1 and selected Bouzeffour-Halouani formulas.
No complete full-event supplier was identified in that inspected scope.
Wang-Wang's full paper (DOI 10.1080/10652469.2025.2520604), the original
Horn 2003 item, Berndt-Chu's full paper
(DOI 10.1090/S0002-9939-06-08553-4), untraversed citations, other implicit
suppliers and individual OEIS revision views requiring sign-in remain
uninspected. Metadata or abstracts do not verify those unread texts.
The bounded third-party Lean queries and repository duplicate screen
are not an ecosystem census. Global novelty, priority, persistence of
openness and exhaustive absence of earlier proofs are unverified.
