---
slug: oeis-a400644-rounded-three-term-norm
bibkey: oeis2026a400644
doi: null
url: https://oeis.org/A400644
triage: theorem
motivation_gids:
  - D5/S0/Tower/Tribonacci/Values
  - D5/S1/Recurrence/ComplementaryGoldenRatioLimit
---

# OEIS A400644 rounded three-term norm ratio

## Problem

OEIS A400644 revision 28 has the name:

> a(n+1) = round(sqrt(a(n)^2 + a(n-1)^2 + a(n-2)^2)).

Its conjectural comment is:

> Numerical evidence suggests that the ratio of consecutive terms (a(n+1)/a(n)) tends to 1.356203065626295... which is the largest positive real root of x^6-x^4-x^2-1=0. Setting x^2=t gives t^3-t^2-t-1 which yields the tribonacci constant (A058265) as the largest positive root.

The Mathematica source initializes `a(1)=a(2)=0`, `a(3)=1` and uses
`Round[Sqrt[a[n]^2+a[n-1]^2+a[n-2]^2]]`. The Python source starts
`[0,0,1]`, computes `s` as the sum of the last three squares, puts
`r=isqrt(s)`, and appends `r+(s>r*r+r)`.

The target quantifies over the unique sequence with values in the
nonnegative integers on every positive index and over every recurrence
index `n>=3`. It asks for the full infinite consecutive-ratio limit.

## Motivation

The published numerical conjecture is an external tier-1 question,
preregistered at https://github.com/the-omega-institute/trureturing/issues/15948.
The intended binding is ProblemSlug `oeis-a400644-rounded-three-term-norm`,
GID `D5/S1/Recurrence/OEISA400644.result`, and `ResolutionKind.Proved`.
The fixed initial data do not make this infinite asymptotic theorem a
certified finite instance. Computational utility is `none`.

## Gap

The bounded source assessment read revision 28 and every displayed
revision 28 through 1 with the associated discussions. The earlier informal
argument omits the implication from small local relative rounding error to
stability of the actual consecutive ratios. Its divergent product indexed
over all integer radicands is not a product along the actual sequence.
This identifies a missing bridge in that argument; it does not refute the
conjecture or exclude an unpublished completion.

The arXiv abstract searches were `all:"A400644"` (0 results),
`all:"rounded" AND all:"tribonacci"` (0),
`all:"rounded" AND all:"Euclidean norm"` (8), and
`all:"rounded" AND all:"recurrence" AND all:"limit"` (22), with at most
30 results per query. None of the inspected returned abstracts supplied
this exact theorem. These bounded searches do not establish global absence.
Offsite complete proofs and inaccessible or unpublished sources remain
unverified. The independently verified OEIS JSON, internal entry and history readings
returned HTTP 200 and retained revision 28 with its conjectural wording
(source reading: 2026-10-12T21:39:40Z). Revision 28 is the exact statement
source. A complete prior published settlement would require reuse rather
than a new resolved-problem claim.

Repository and pinned Mathlib searches include private declarations.
The reusable Tribonacci root and strict affine-contraction results supply
parts of the proof, but the linear unrounded Tribonacci ratio result does
not prove the rounded recurrence's limit.

## Route

Use the exact zero-based sequence `a(0)=a(1)=0`, `a(2)=1`, and set
`sourceA(n)=a(n-1)` on positive indices. Strict half-unit error proves
agreement with nearest-integer rounding at every integer radicand; hence
half-tie conventions cannot affect the recurrence. Strong induction proves
uniqueness for every natural-valued sequence satisfying the source data.

Monotonicity and the square-root estimate give
`a(n+5)>=a(n+2)+1`. A block induction implies divergence of the rounded
terms. Put `b(n)=a(n+2)^2` and
`e(n)=b(n+3)-b(n+2)-b(n+1)-b(n)`.
Then `|e(n)|<=2a(n+4)` for the actual signed rounding error.

For the existing Tribonacci root lambda, define
`T(n)=b(n+2)+(lambda-1)b(n+1)+b(n)/lambda`.
Its coefficients are positive and `T(n)>=b(n+2)>0`.
The cubic identity gives `T(n+1)=lambda*T(n)+e(n)`.
Thus `e(n)/T(n)->0` and `T(n+1)/T(n)->lambda`.

The bounded coordinates `v(n)=b(n+2)/T(n)` lie in `[0,1]`.
Their two-step recurrence has coefficient limits
`alpha=(lambda-1)/lambda`, `beta=lambda^(-3)`, with
`0<=alpha`, `0<=beta`, `alpha+beta<1`.
Let `U=1/(1+alpha+beta)>0`. The deviations from U obey a second-order
stable recurrence with a vanishing error. The maxima of each pair of
consecutive deviations satisfy the existing strict affine-contraction
criterion. This covers both parities and proves `v(n)->U` for all indices.
Quotient continuity now gives the squared ratio limit lambda, and square-root
continuity gives the original ratio limit `rho=sqrt(lambda)`.
Positive-root uniqueness for the Tribonacci cubic identifies rho as the
largest positive root of the exact sextic.

## Falsifier

A mismatch in initial values, rounding or positive-index recurrence would
invalidate source correspondence. A ratio limit for a finite prefix,
a single parity or an unrounded trajectory does not prove this target.
A failure to control the normalized coordinates over all indices would
leave the analytic bridge unresolved.

## Evidence

The mathematical source is `D5/S1/Recurrence/OEISA400644.lean` and its
canonical exposition is `Blueprint/D5/S1/Recurrence/OEISA400644.scribe.cs`.
The full result is `D5.S1.Recurrence.OEISA400644.result : targetClaim`.
The theorem proves the full infinite source claim with no additional assumptions.
The Reg mirror contains theorem-specific equivalence bridges, whole-family
variation, sensitivity and observational-dependence proofs for all public
targets. Its raw source-occurrence selections remain incomplete; no
`declared_validated` registration is asserted.
The exact typed attempts remain `declared_unresolved`, with null
certificates and `source.selection_missing`, under the source-owner
exception at https://github.com/the-omega-institute/trureturing/issues/16003.
The issue records the 16 public targets and their missing source selections;
it does not certify those selections. No active resolution claim is attached
to an unfrozen result.

The per-declaration proof shapes below use the immutable frozen and pinned
upstream boundary after inlining local helpers. They are semantic judgments,
not machine-assigned statuses. Every auxiliary has an actual consumer on
the proof path to `result`; its retention basis is that consumption. Only
`result` has the tier-1 `open-problem-resolution` admission basis. No helper
uses a standalone external-resolution exception. All declarations have
semantic utility `none`: these are unbounded analytic statements or their
definitions and proof steps, with no retained computational certificate,
checker, enumeration or numerical-reduction declaration.

| Declaration | Visibility | Proof shape | Actual live consumers | Admission basis |
|---|---|---|---|---|
| `rho_pos` | public | bind-only | `positive_sextic_root_eq_rho`, `rho_is_largest_positive_root` | consumed auxiliary; no standalone basis |
| `rho_sextic` | public | bind-only | `rho_is_largest_positive_root` | consumed auxiliary; no standalone basis |
| `positive_sextic_root_eq_rho` | public | bind-only | `rho_is_largest_positive_root` | consumed auxiliary; no standalone basis |
| `rho_is_largest_positive_root` | public | bind-only | `result` | consumed auxiliary; no standalone basis |
| `sqrt_bracket` | public | bind-only | `sourceRound_spec` | consumed auxiliary; no standalone basis |
| `sourceRound_spec` | public | bind-only | `sourceRound_real_error` | consumed auxiliary; no standalone basis |
| `sourceRound_ge_sqrt` | public | bind-only | `a_mono` | consumed auxiliary; no standalone basis |
| `sourceRound_real_error` | public | bind-only | `a_block_growth`, `err_bound`, `sourceRound_nearest_unique` | consumed auxiliary; no standalone basis |
| `a_zero` | public | bind-only | `sourceA_spec` | consumed auxiliary; no standalone basis |
| `a_one` | public | bind-only | `sourceA_spec` | consumed auxiliary; no standalone basis |
| `a_two` | public | bind-only | `sourceA_spec` | consumed auxiliary; no standalone basis |
| `a_recurrence` | public | bind-only | `a_mono`, `a_block_growth`, `err_bound`, `sourceA_spec` | consumed auxiliary; no standalone basis |
| `a_mono` | public | bind-only | `a_pos`, `a_le` | consumed auxiliary; no standalone basis |
| `a_pos` | public | bind-only | `result`, `a_block_growth`, `b_pos`, `err_bound`, `relative_err_bound` | consumed auxiliary; no standalone basis |
| `a_unique` | public | content | `source_unique` | consumed auxiliary; no standalone basis |
| `a_le` | private | bind-only | `a_block_growth`, `a_tendsto`, `err_bound` | consumed auxiliary; no standalone basis |
| `a_block_growth` | private | bind-only | `a_block_lower` | consumed auxiliary; no standalone basis |
| `a_block_lower` | private | content | `a_tendsto` | consumed auxiliary; no standalone basis |
| `a_tendsto` | private | content | `relative_err_tendsto` | consumed auxiliary; no standalone basis |
| `b_pos` | private | bind-only | `proj_ge`, `proj_pos`, `ratio_limit`, `square_ratio_limit`, `v_bounds` | consumed auxiliary; no standalone basis |
| `proj_ge` | private | bind-only | `proj_pos`, `relative_err_bound`, `v_bounds` | consumed auxiliary; no standalone basis |
| `proj_pos` | private | bind-only | `proj_ratio_tendsto`, `relative_err_bound`, `square_ratio_limit`, `v_bounds`, `v_step` | consumed auxiliary; no standalone basis |
| `err_bound` | private | bind-only | `relative_err_bound` | consumed auxiliary; no standalone basis |
| `proj_step` | private | bind-only | `proj_ratio_tendsto` | consumed auxiliary; no standalone basis |
| `relative_err_bound` | private | bind-only | `relative_err_tendsto` | consumed auxiliary; no standalone basis |
| `relative_err_tendsto` | private | content | `proj_ratio_tendsto` | consumed auxiliary; no standalone basis |
| `proj_ratio_tendsto` | private | content | `ca_limit`, `cb_limit`, `square_ratio_limit` | consumed auxiliary; no standalone basis |
| `v_bounds` | private | bind-only | `forcing_bound` | consumed auxiliary; no standalone basis |
| `v_step` | private | bind-only | `delta_step` | consumed auxiliary; no standalone basis |
| `ca_limit` | private | content | `forcing_limit` | consumed auxiliary; no standalone basis |
| `cb_limit` | private | content | `forcing_limit` | consumed auxiliary; no standalone basis |
| `coefficient_bounds` | private | bind-only | `center_pos`, `delta_limit`, `delta_step` | consumed auxiliary; no standalone basis |
| `center_pos` | private | bind-only | `square_ratio_limit` | consumed auxiliary; no standalone basis |
| `forcing_bound` | private | bind-only | `forcing_limit` | consumed auxiliary; no standalone basis |
| `forcing_limit` | private | content | `delta_limit` | consumed auxiliary; no standalone basis |
| `delta_step` | private | bind-only | `delta_limit` | consumed auxiliary; no standalone basis |
| `delta_limit` | private | content | `v_limit` | consumed auxiliary; no standalone basis |
| `v_limit` | private | content | `square_ratio_limit` | consumed auxiliary; no standalone basis |
| `square_ratio_limit` | private | content | `ratio_limit` | consumed auxiliary; no standalone basis |
| `ratio_limit` | private | content | `result` | consumed auxiliary; no standalone basis |
| `sourceRound_nearest_unique` | private | bind-only | `sourceRound_round` | consumed auxiliary; no standalone basis |
| `sourceRound_round` | private | bind-only | `sourceA_spec`, `source_unique` | consumed auxiliary; no standalone basis |
| `sourceA_spec` | private | bind-only | `result` | consumed auxiliary; no standalone basis |
| `source_unique` | private | content | `result` | consumed auxiliary; no standalone basis |
| `result` | public | content | terminal external result | open-problem-resolution |

The definitions have no theorem proof-shape classification. Each is
necessary in the exact statement or in the consumed proof, without a
standalone admission basis.

| Definition | Visibility | Role | Actual consumers |
|---|---|---|---|
| `rho` | public | exact algebraic limit/root | `positive_sextic_root_eq_rho`, `result`, `rho_is_largest_positive_root`, `rho_pos`, `rho_sextic`, `ratio_limit` |
| `sourceRound` | public | integer nearest-rounding implementation | `a_mono`, `a_unique`, `sourceRound_ge_sqrt`, `sourceRound_real_error`, `sourceRound_spec`, `a_block_growth`, `err_bound`, `sourceA_spec`, `sourceRound_nearest_unique`, `source_unique` |
| `a` | public | unique recursively constructed zero-based natural sequence | `a_mono`, `a_one`, `a_pos`, `a_recurrence`, `a_two`, `a_unique`, `a_zero`, `result`, `sourceA`, `targetClaim`, `a_block_growth`, `a_block_lower`, `a_le`, `a_tendsto`, `b`, `b_pos`, `err_bound`, `ratio_limit`, `relative_err_bound`, `relative_err_tendsto`, `sourceA_spec`, `source_unique` |
| `b` | private | positive squared source terms | `err`, `proj`, `proj_ge`, `proj_pos`, `proj_step`, `ratio_limit`, `square_ratio_limit`, `v`, `v_bounds`, `v_step` |
| `err` | private | actual signed squared recurrence error | `err_bound`, `proj_ratio_tendsto`, `proj_step`, `relative_err_bound`, `relative_err_tendsto` |
| `proj` | private | positive actual Tribonacci projection | `ca`, `ca_limit`, `cb`, `cb_limit`, `proj_ge`, `proj_pos`, `proj_ratio_tendsto`, `proj_step`, `relative_err_bound`, `relative_err_tendsto`, `square_ratio_limit`, `v`, `v_bounds`, `v_step` |
| `v` | private | bounded relative coordinate | `delta`, `delta_step`, `forcing`, `forcing_bound`, `square_ratio_limit`, `v_bounds`, `v_limit`, `v_step` |
| `ca` | private | first variable coefficient | `ca_limit`, `delta_step`, `forcing`, `forcing_bound`, `forcing_limit`, `v_step` |
| `cb` | private | second variable coefficient | `cb_limit`, `delta_step`, `forcing`, `forcing_bound`, `forcing_limit`, `v_step` |
| `alpha` | private | first limiting coefficient | `ca_limit`, `center`, `center_pos`, `coefficient_bounds`, `delta_limit`, `delta_step`, `forcing`, `forcing_bound`, `forcing_limit` |
| `beta` | private | second limiting coefficient | `cb_limit`, `center`, `center_pos`, `coefficient_bounds`, `delta_limit`, `delta_step`, `forcing`, `forcing_bound`, `forcing_limit` |
| `center` | private | proved positive contraction center | `center_pos`, `delta`, `delta_step`, `square_ratio_limit`, `v_limit` |
| `delta` | private | deviation from center | `delta_limit`, `delta_step`, `v_limit` |
| `forcing` | private | vanishing perturbation | `delta_limit`, `delta_step`, `forcing_bound`, `forcing_limit` |
| `sourceA` | public | positive-index presentation | `result`, `targetClaim`, `sourceA_spec`, `source_unique` |
| `sourceSpec` | public | original initial data and exact round recurrence | `result`, `targetClaim`, `source_unique` |
| `targetClaim` | public | whole source theorem; used as result type | `result (type)` |

## Triage

Proved by `D5/S1/Recurrence/OEISA400644.result`: the decisive mechanism is
the positive scalar projection together with a
strict contraction of bounded relative coordinates. It avoids assuming
that vanishing local error alone implies a ratio limit. The proof does not
require an infinite-product amplitude estimate.

Extensions to other initial values or rounded higher-order norm recurrences
remain open here. No adjacent result is included. The source comment's
numerical limit and root identification are the only external conclusion
addressed; no additional source consequence is claimed.

## ASSUMED-UNVERIFIED

No additional mathematical hypothesis is assumed in the closed result.
Global novelty and absence of an offsite, inaccessible or unpublished
complete proof are not established by the bounded source and literature
searches. The current source-binding certificates for all 16 public
audit targets remain unresolved under
https://github.com/the-omega-institute/trureturing/issues/16003; the compiled
typed attempts are retained, and none is described as `declared_validated`.
Final independent reviews, required CI, merge and verification on `dev`
remain necessary before resolved-problem credit.
