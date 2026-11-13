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

Six inserted vertices fulfill boundary requests. The free vertices in each
three-site half form a clique containing its central vertex. A matching covers
either the whole clique or the clique with its center removed, according to
parity; if both centers remain single, their edge joins them. Thus the remaining
free sites are paired at distance at most two with at most one central single. Matched buffer
vertices put their partners first; every neighbor of a buffer single is
matched. The actual word injections give b(m)b(k)<=b(m+k+6) and
b(m)<=A(m+1). The latter is a source cycle with m+6 sites, including m=1, m=2,
all wrap edges and both parities. Cutting an actual stable partial matching
gives A(n)<=b(n+5). Certificates and matching witnesses are not counted.

For f(m)=log b(m), Mathlib Fekete and the bounded-defect estimate in
GrowthTransfer give a real h with h*m<=f(m)<=h*m+f(6). Exponentiation gives
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
`GrowthTransfer.fixed_gap_log_bounds`, and `OpenCertificates.count_three_bound`,
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

## Motivation

The frozen declaration
`D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_submultiplicative`
supplies the upper counting relation for open ranking words. Connecting that
relation to six-site completion and actual cyclic profiles yields a probability
estimate for Mertens's d=1,r=2 specialization: one common q for every labelled
cycle size N>=7, including both parities. Each vertex independently samples one
of the 24 strict rankings of its four neighbors. Stable partial matchings allow
singles, and each successful preference profile contributes once.

## Gap

`GrowthTransfer.result` closes the unconditional same-q two-sided exponential
bound for `SourceModel.solutionProbability`, with N=n+5 and n>=2. The open-word
and cyclic injections supply its counting comparisons; no completion or
perfect-matching hypothesis remains. The general d,r conjecture, sharp values
of q and the constants, and worldwide literature novelty or priority are not
established by this specialization.

## Falsifier

A fidelity claim fails if the model excludes singles, omits either parity or
any N>=7, changes the independent uniform distribution on the 24 four-neighbor
rankings, counts certificate or matching witnesses instead of successful
profiles, or uses different exponential bases for odd and even sizes. A source
comparison must preserve the signed offsets ±1,±2 and the blocking rule with
single endpoints. These checks concern the exact specialized claim, not the
unproved general d,r conjecture.

## Evidence

The five frozen proof hosts are `BufferLayout`, `OpenCertificates`,
`PaddedCompletion`, `CyclicClosure` and `GrowthTransfer` under
`D5/S3/Combinatorics/Graph/Roommates/`; their corresponding typed Scribes and
generated statements are under `Blueprint/D5/S3/Combinatorics/Graph/Roommates/`.
`Library/Entropy/mertens2005stable.md` records the source locator and scope.
The consumed `SourceModel.lean` compatibility port attributes the Formal
Conjectures Authors at `bocowgill/formal-conjectures` revision
`dc0fa7334537d8733edceaba09fd88163eeb7cef`; its Apache-2.0 license is retained at
`docs/reports/licenses/formal-conjectures-mertens/LICENSE.txt`.
The unfinished information-escape registration is tracked in
https://github.com/the-omega-institute/trureturing/issues/29645.

## ASSUMED-UNVERIFIED

The bounded literature search does not certify worldwide openness, novelty or
first priority. The general d,r problem and sharp constants remain outside the
proved conclusion. Source-selection and occurrence bindings in the Reg audit
remain unfinished under issue #29645; those records are not
`declared_validated`. These are limits of source qualification and audit
evidence, not additional mathematical assumptions of `GrowthTransfer.result`.
