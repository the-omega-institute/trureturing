---
slug: mertens-2005-range-two-stable-matching
bibkey: mertens2005stable
doi: 10.1088/1742-5468/2005/10/P10008
url: https://arxiv.org/abs/cond-mat/0509221v2
triage: wall
motivation_gids:
  - D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_submultiplicative
---

# Mertens range-two cyclic stable partial matchings

## Problem

For each labelled cycle of size N>=5, neighbors are exactly the four signed
offsets ±1,±2. Each vertex independently chooses a uniform strict ranking of
these neighbors and prefers every acceptable neighbor to being single. A
matching may leave vertices single. Each endpoint of a potential blocking edge
must prefer it to its current assignment, with single endpoints always willing.
Let p_N be the proportion of profiles admitting at least one stable matching,
counting every preference profile once. The exact goal is the existence of one
real q in (0,1), c,C>0 and N0>=5 such that c*q^N<=p_N<=C*q^N for every N>=N0,
including odd and even N. Supplier SourceModel uses N=n+5.

## Route

Use open-interval certificates retaining the true rank of exterior requests,
with injectivity of all integer partner targets. Restriction induces an
injection of certified words into pairs of shorter certified words. Six fresh
vertices fulfil boundary requests; pair remaining free vertices at distance at
most two, with at most one central single. Matched new vertices rank their
partners first. The central single has four matched buffer neighbors. This is
the proposed general concatenation and cyclic closure construction, including
small cycles with extra buffer wrap edges.

The independent paper argument gives b_(N-6)<=a_N<=b_N and one lambda with
6<=lambda<24 and lambda^(N-6)<=a_N<=lambda^(N+6) for every N>=7. Here b counts
certified words and a counts solvable labelled cycle profiles. This is a
paper-level result, not the current formal theorem. An alternative bounded
defect Fekete inference allows a coarser fixed upper constant and the identical
full probability target; it does not assume or supply the missing word maps.

## Triage

Unresolved: the complete Lean/Scribe theorem. The partial source modules are
WIP, not separately admitted results or a solved problem. No conditional
certificate-completion or cyclic-bridge premise replaces the original target.

The source-cycle cut is implemented in `CyclicBridge`: actual signed offsets,
single rank four, and the supplier ranks give an open certificate on the same
word for every N>=5. Its profile injection gives a_N<=b_N; exact normalization
gives p_N<=b_N/24^N. `PaddedCompletion` constructs the actual injective boundary
requests for two separated pieces and for closing one word, then applies the
six-site involution. Integer targets are never truncated or quotient-counted.
The actual padded word map recovers both input words and is injective on
preference words; its buffer assignments are first-ranked when nonzero.
Buffer offsets fulfill the requests, stay within range and isolate new singles.
Old--old stability survives separated placement; the cyclic closure helpers
preserve original request destinations and exclude old--old wrap edges.

The concrete padded word has a full certificate in `padded_certificate`:
all old/new assignments are reciprocal, all nonzero integer targets are
injective, and every old, mixed and new edge is nonblocking, including singles.
The certified word injection proves b_m*b_k<=b_(m+k+6) for all natural m,k,
without counting certificate witnesses. The padded source and its two Reg
mirror attempts have a successful scoped native Lean report. Its canonical
Scribe Markdown is emitted and retains the complete construction and scope.

Exact remaining mathematics: for closure, produce the actual source matching
and prove cyclic stability, including the extra buffer--buffer
wrap edges at m=1, then derive the profile injection b_m<=a_(m+6) for every
m>=1. The requester/buffer involutions alone do not supply these conclusions.
The exact triangle count, strict growth bound and final common-q normalization
remain separate obligations. No pending contributor result is assumed.

The generic Fekete inference must be consumed with proved concatenation and
closure hypotheses. Faithful Reg bindings and independent pre-freeze audit
remain necessary; no mathematical component is separately admitted here.

The research line is https://github.com/the-omega-institute/trureturing/issues/29622.
Its 2026-11-26T15:30:00Z deadline and all prior forecasts and dispositions remain
unchanged. Threshold0 is unresolved, not a refutation or line termination.
This work claims neither formal acceptance nor worldwide novelty or priority.

The source and its Scribe definitions remain unfrozen Stage A components.
Guarded direct Lean checks are distinct from native target builds, scoped
reports, canonical Markdown emission, inventory acceptance and required CI.
The successful padded scoped report covers its mathematical and Reg targets
and imports. The padded Markdown is tracked. Current inventory rejects five
other Stage A Markdown projections absent from tracked files and the inherited
`docs/reports/licenses/formal-conjectures-mertens-Apache-2.0.txt` path under the
existing reports policy. Its license bytes and supplier attribution are
preserved. Full-project verification, inventory acceptance and required CI
remain separate obligations. Main is observation-only; this contribution
makes no main-cache health or delivery claim.

The faithful registration gap is
https://github.com/the-omega-institute/trureturing/issues/29645.
The padded certificate and padded count inequality have compiled typed
dependent-family mirrors retaining their full original telescopes, concrete
certificate observations and exact cardinality operands. Native reporting
records both as declared_unresolved with IE-C050, source.selection_missing.
Source-selection and occurrence bindings remain absent; neither is
declared_validated. The earlier source-count mirror and other certificate,
completion and source-rank targets retain their unfinished audit obligations.
The padded Scribe uses explicit no-formula projection gaps for declarations
outside the fixed projection corpus. No freeze or publication PR is authorized
before the separately assigned independent pre-freeze audit.
