---
slug: mertens-2005-range-two-stable-matching
bibkey: mertens2005stable
doi: 10.1088/1742-5468/2005/10/P10008
url: https://arxiv.org/abs/cond-mat/0509221v2
triage: theorem
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

Let b(m) count ranking words admitting an open-interval certificate, and let
A(n) count successful SourceModel.Profile n profiles, each counted once.
Certificates retain signed exterior requests at their actual ranks, require
injectivity of every nonzero integer target including exterior targets, and
exclude every internal blocking edge. Restriction and word splitting give
b(m+k)<=b(m)b(k). Putting prescribed partners first gives 6^m<=b(m), including
odd lengths with a final exterior request.

Six inserted vertices fulfill boundary requests, pair the remaining free sites
at distance at most two, and leave at most one central single. Matched buffer
vertices put their partners first; every neighbor of a buffer single is
matched. The actual word injections give b(m)b(k)<=b(m+k+6) and
b(m)<=A(m+1). The latter is a source cycle with m+6 sites, including m=1, m=2,
all wrap edges and both parities. Cutting an actual stable partial matching
gives A(n)<=b(n+5). Certificates and matching witnesses are not counted.

For f(m)=log b(m), Mathlib Fekete and the bounded-defect estimate in
FixedGapGrowth give a real h with h*m<=f(m)<=h*m+f(6). Exponentiation gives
exp(h)^m<=b(m)<=exp(h)^m*b(6). The sixteen distinct exclusive-triangle words
supply b(3)<=13808<13824=24^3, hence h<log 24. Set q=exp(h)/24,
c=1/exp(h)^6 and C=b(6). The actual cyclic comparisons and exact division by
24^(n+5) give the full source event for every n>=2, equivalently N>=7.

## Triage

The unconditional Lean theorem is
`D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.result`:
there exist real q,c,C with 0<q<1 and c,C>0 such that, for every natural n>=2,
c*q^(n+5)<=SourceModel.solutionProbability(n)<=C*q^(n+5).
There is no completion, count, rate, perfect-matching or parity premise.
The corresponding Scribe carries the exact source-probability statement and
the proved specialization of the source problem. The matching, counting and
analytic lemmas form the derivation of this single probability estimate.

### What the settlement shows

The decisive mechanism is the pair of word injections with a fixed six-site
gap: they bound the logarithmic counting defect independently of length.
Fekete then supplies one growth base for all lengths, while the exclusive
triangle makes that base strictly smaller than 24. These are proved in
`PaddedCompletion.count_padded_supermultiplicative`,
`CyclicClosure.count_le_successful_profile_count`,
`FixedGapGrowth.fixed_gap_log_bounds`, and `TriangleCount.count_three_bound`,
and consumed by `GrowthTransfer.result`. Singles and both parities are in the
proved domain. The constants need not be sharp; no exact value of q is claimed.
The proof does not settle general d,r in Conjecture 3, complete-graph
asymptotics, or any additional external problem. Global novelty and priority
remain unproved.

The model is a consumed compatibility port of the Formal Conjectures Authors'
API at dc0fa7334537d8733edceaba09fd88163eeb7cef. Supplier Lean/mathlib pins are
incompatible with direct import; the port retains N=n+5, labelled rankings,
existential partial matchings and singles. The exact Apache-2.0 license is
`docs/reports/licenses/formal-conjectures-mertens/LICENSE.txt`.

The incomplete information-escape audit is tracked at
https://github.com/the-omega-institute/trureturing/issues/29645.
Typed mirrors retain actual observations, original telescopes, exact source
reconstruction and variation evidence where provided. Raw source-selection
and occurrence bindings remain absent, and coverage of all public helper
targets is unfinished; no declared_validated status is claimed. Canonical
Scribes retain explicit no-formula gaps for unsupported component projections.
The final probability statement and the available closure and count formulas
are displayed explicitly.

The research line is
https://github.com/the-omega-institute/trureturing/issues/29622.
