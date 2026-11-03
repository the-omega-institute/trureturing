---
slug: oeis-a381524-hermite-absolute-differences
bibkey: sheppard2025a381524
doi: null
url: https://oeis.org/A381524/internal?rev=18
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.result
---

# Absolute Hermite coefficient modes: the complete A381524 difference assertion

## Problem

OEIS A381524, revision 18, by Mike Sheppard (2025), defines:

> Smallest exponent of x of maximal coefficient (ignoring signs) in Hermite polynomial of order n.

Its independently printed Comments assertion is:

> Conjecture: Differences are either +1 or -1.

The offset is zero. Let $H_n$ be the physicists Hermite polynomial represented
by the original `HermiteSignedMode.physicistsHermite`, and let $b(n)$ be the
least $j\in\{0,\ldots,n\}$ maximizing $|[x^j]H_n|$. The complete event is

$$
\begin{aligned}
\forall n\in\mathbb N,\quad &b(n)\le n,\\
&\forall k\le n,\quad |[x^k]H_n|\le |[x^{b(n)}]H_n|,\\
&\forall k\le n,\quad |[x^k]H_n|=|[x^{b(n)}]H_n|\ \Longrightarrow\ b(n)\le k,\\
&b(n+1)-b(n)\in\{1,-1\}\quad\text{in }\mathbb Z.
\end{aligned}
$$

Both selector values are cast to integers before subtraction. Every natural
order, including zero, every exponent from zero through the order, parity
zeros and all ties are included. The source's `HermiteH` convention and
examples fix physicists normalization: $b(5)=3$, and $b(8)=2$ chooses the
smaller of the tied exponents two and four. The claim is the one entire
Differences assertion with its selector certificate, without a uniqueness
premise, finite cutoff or asymptotic qualification.

## Motivation

This is a Tier 1 explicit recent OEIS conjecture under the repository's source
classification, not an arXiv assertion or a difficulty measurement. The exact
whole event is preregistered at
https://github.com/the-omega-institute/trureturing/issues/25789#issuecomment-6586906062.
The neighboring signed selector in A381423 has differences $1,-3$ and is a
separate result. Its helpers and the source's separate tie-classification
assertion are outside this dossier's resolution claim.

## Gap

The accepted bounded source examination found the same definition, Comments
assertion, examples and offset in revision 18 and the retrieved current
revision 18. The source's programs and examples supply conventions and finite
data, not a universal proof. No exact whole-target solver was identified in
the inspected scope:

- Exact A381524 and maximal-coefficient phrase queries in arXiv metadata each
  returned zero matches. The broader Hermite mode query inspected only the
  first 30 of 540 metadata results; 510 remained uninspected. A separate
  coefficient query inspected 21 titles and three selected abstracts, without
  a full-text screen of those papers.
- arXiv:1909.03874v2 was checked through bounded term scans of 11 TeX members
  and selected normalization/coefficient passages; arXiv:1801.07980v2 through
  bounded term scans and its initial convention/recurrence. Their probabilists
  Wronskian normalization is not an established mode-preserving bridge.
- arXiv:2204.07526v2 was checked through bounded term scans of 16 TeX/Bib
  members and selected orthonormal-Hermite pointwise-bound passages. The
  specific Dudeja–Hsu Lemma 35 remains unidentified; this inspection does not
  complete the screen of that citation.
- GitHub code-search requests returned HTTP 403. The inspected public Problems
  page displayed 1000 of 1663 entries. Three selected third-party Lean sources
  had differing pin and license limits; their bounded inspection established
  no exact admissible whole-target supplier.

Original D5 public/private declarations and pinned Mathlib were examined
before local proof development. The original coefficient extraction and
finite-maximum interfaces supply part of the argument. The signed mode's
concrete $n-4r$ thresholds do not directly instantiate to the absolute
$n-2r$ family. Within-row maximality alone does not supply the adjacent-order
transition. These are bounded reuse findings, not worldwide absence or
current-openness claims.

## Route

The proof uses the original `physicistsHermite`, `signedCoeff` and
`HermiteSignedMode.polynomial_coeff`, whose original statement and proof are
preserved with only the consumed extraction made public. For exponent
$n-2r$, its absolute coefficient is a positive weight $w(n,r)$ when $2r\le n$;
the other parity coefficients are zero. Adjacent weights obey

$$
4(r+1)w(n,r+1)=(n-2r-1)(n-2r)w(n,r)
\qquad(2(r+1)\le n).
$$

The threshold $2r\le n$ and $4r\le(n-2r+1)(n-2r+2)$ is the nondecrease test
from the preceding weight. Its true indices form an initial segment.
Induction proves global maximality at the last true index and strict decrease
beyond it. Choosing that last index reverses to the least exponent among all
tied maxima. Threshold persistence and rollback across adjacent orders bound
the index increment by zero or one; $b(n)=n-2\operatorname{mode}(n)$ then gives
the exact integer difference $1$ or $-1$. The same argument includes order zero.

## Falsifier

A natural order at which the defined selector fails any full-range maximum
or least-tie obligation, or whose adjacent integer difference is neither
$1$ nor $-1$, would falsify the complete formal event. Finite examples alone
cannot establish it. No signed-selector, uniqueness or asymptotic surrogate
is substituted for this test.

## Evidence

The owning Scribe binds exactly one `OpenProblemResolutionClaim(Proved)` to
`D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.result` for this slug. Its exact
frozen identities are:

- Module: `D5/S3/Analytic/Polynomial/HermiteAbsoluteMode`, statement identity
  `sha256:5303c1213e0ff3c9430ffb07325d3f6c48fb03e94c18384b1aeaea180d1d8fe5`.
- Whole theorem `result`, statement identity
  `sha256:c3e260b5a52e394f99f879492ca4b33fa516e5615e07fe37395a0375d9a27e68`.
- Complete proposition `claim`, statement identity
  `sha256:facac8b9042d55112c726de672d9b824c51b2eb37993305f89a6f9d90b8a572f`.

The accepted independent conclusions use the unchanged compiled mathematical
evidence with `noSorry` and axiom closure `Classical.choice`, `Quot.sound`,
`propext`. The admission basis is `open-problem-resolution` for the whole
preregistered external event; `escape_witness: none` and `utility: none`.
Proof shape is separate from that admission basis. The accepted per-theorem
classification and actual live consumers are:

| Declaration suffix | proof_shape | Live consumers |
| --- | --- | --- |
| `zero_candidate` | bind-only | `mode` nonempty certificate |
| `mode_rises` | bind-only | `mode_step`, `weight_le_mode`, `b_spec`, `result` |
| `le_mode` | bind-only | `mode_step`, `weight_le_mode`, `weight_lt_mode` |
| `second_mono` | bind-only | `rises_lower`, `rises_next`, `rises_previous` |
| `rises_lower` | bind-only | `weight_le_mode` |
| `rises_next` | bind-only | `mode_step` |
| `rises_previous` | bind-only | `mode_step` |
| `mode_step` | bind-only | `result` integer-jump conjunct |
| `weight_pos` | bind-only | `adjacent_le`, `b_spec` exclusion of zeros |
| `adjacent` | bind-only | `adjacent_le` |
| `adjacent_le` | bind-only | `weight_le_mode`, `weight_lt_mode` |
| `weight_le_mode` | content | `weight_lt_mode`, `b_spec` maximality |
| `weight_lt_mode` | content | `b_spec` least-tie conjunct |
| `coefficient_cases` | bind-only | both selector conjuncts of `b_spec` |
| `b_spec` | content | `result` selector conjunct |
| `result` | content | Reg `source_registration` actual law and dependence |

Definitions and their decidability instance are consumed type/definition
support, not additional theorem content. The existing extraction
`HermiteSignedMode.polynomial_coeff` is bind-only, with preserved statement
identity `sha256:4295bdb6223b1da40e22523dcdbb52f92642fe627927807633e64e1d34b7cc19`,
and is consumed by the original `a_spec` and absolute `b_spec`. It is not a new
mathematical result.

The sole newly authored public D5 theorem, `result`, has the accepted
`declared_validated` source-family registration in
`Reg/D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.lean`, using the enrolled
`DependentFamily.realize` template. Its state and output are natural numbers:
the readout is the entire $\mathbb N\to\mathbb N$ selector family, without
truncation. Source equivalence reconstructs the complete conjunction;
variation and sensitivity use the rejected constant-zero family, and actual
dependence uses indices zero and one. Reg `rejected_law` is a consumed
bind-only audit helper. Empty anchors impose no hidden finite restriction.
Continuation is unknown, which asserts neither undecidability nor
inexhaustibility. This audit evidence is separate from mathematical
proof shape and supplies no invented escape witness.

## Triage

`theorem`. The proved formal result contains both the complete all-natural
selector certificate and the entire adjacent-difference assertion. Its
mechanism is the last nondecreasing weight threshold together with its
adjacent-order persistence and rollback. Ties are retained rather than
excluded. No uniqueness theorem, tie classification, asymptotic result or
generalized mode-transition theorem is asserted here; those remain outside
this event. The source citation and search limits below remain unresolved.

## ASSUMED-UNVERIFIED

Source-to-Lean fidelity is a content correspondence supported by the accepted
independent source/form/mirror review, not a kernel proof about OEIS prose.
The universal reading combines the source's unqualified Differences assertion
with its zero offset; OEIS does not literally print a forall formula.
The author line is dated February 26, 2025, whereas the database creation
field is March 16, 2025; those are distinct provenance fields.

The specific Dudeja–Hsu Lemma 35 remains unidentified. The metadata,
pagination, code-search, selected-passage and third-party pin/license limits
in Gap remain in force. No exhaustive search, worldwide current openness,
priority or originality certification follows from them. No further result
depending on the source's separate tie conjecture is claimed. The Library
source is citation-only, and its examples/programs are not proof evidence.
