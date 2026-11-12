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

Exact remaining obligations are general request completion in the full old/new
certificate, stability of every translated and cyclic edge, the actual
concatenation and closure injections on preference profiles, the cyclic source
model correspondence (including N=5), the 16-profile exclusive-triangle count,
normalization, and the final uniform same-q bound. The generic Fekete inference
must be consumed with these proved hypotheses, not supplied as an assumption.
Faithful Reg evidence and independent pre-freeze audit remain necessary.

The research line is https://github.com/the-omega-institute/trureturing/issues/29622.
Its 2026-11-26T15:30:00Z deadline and all prior forecasts and dispositions remain
unchanged. Threshold0 is unresolved, not a refutation or line termination.
This work claims neither formal acceptance nor worldwide novelty or priority.

Checked partial scope: the supplier model and its seven ported API lemmas,
interval certificate restriction, profile-count submultiplicativity, the
all-parity six-orders lower bound, the open exclusive-triangle obstruction,
and the two abstract logarithmic Fekete bounds passed direct Lean file checks
at the project pins. Their printed theorem axiom closures are subsets of
propext, Classical.choice and Quot.sound. These are partial checks, not a
normal project build, report, source-model bridge or solution. The generic buffer layout and arbitrary injective request-completion theorem
also passed these file checks with standard axiom closures. Full translated
and cyclic stability, source correspondence and the Reg mirror remain open.

The faithful registration gap is
https://github.com/the-omega-institute/trureturing/issues/29645.
Scribe sources exist, but canonical Markdown emission is unfinished because
the selected declarations have no produced native statement material. No
Markdown projection, freeze, declared_validated status or delivery is claimed.
