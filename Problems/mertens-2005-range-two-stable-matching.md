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

Exact remaining mathematics: complete the assignments and preference word on
the whole concatenated interval, prove reciprocity and target injectivity for
all old/new vertices, and prove every new or mixed edge nonblocking. Upgrade the proved word
injection to certified output and derive b_m*b_k<=b_(m+k+6). `CyclicClosure` constructs the actual source matching and profile on m+6 sites,
proves acceptability and cyclic stability, and gives the injection
b_m<=a_(m+6) for every natural m, including m=1, m=2 and both parities.
The first m ranking coordinates recover the input word; certificate and
matching witnesses are not counted. A matched buffer endpoint rejects every
strict improvement. A buffer single is central and has only matched buffer
neighbors, so the m=1 extra buffer wrap edges and edges from old singles are
covered. The matching, stability, recovery and cardinality statements have
cache-guarded direct Lean checks with only the standard three axioms. Native
build/report, Scribe projection and Reg binding acceptance remain separate.
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
The native scoped report reports a busy main cache during preparation;
main is observation-only for this contribution. No main-cache health,
canonical statement-material production or delivery is claimed.

The faithful registration gap is
https://github.com/the-omega-institute/trureturing/issues/29645.
The source-count comparison has a typed dependent-family mirror with its full
original telescope and actual cardinality operands. Source-selection and
native binding evidence are absent; no declared_validated status is claimed.
The closure-count comparison also has a typed dependent-family mirror
retaining its complete length quantifier and actual cardinality operands.
Its native bindings remain absent. Other certificate, completion, stability,
recovery and source-rank audit targets still need faithful mirrors. Canonical Markdown emission is unfinished: the combined source selection lacks
native statement material, while the author-formula-only selection reaches
native report preparation and has no successful emission. Direct Reg checking
with the Reg workspace stops at the missing temporary-root TheoremUnit import;
there is no successful Reg compilation or native binding result. No freeze or publication PR is authorized
before the separately assigned independent pre-freeze audit.
