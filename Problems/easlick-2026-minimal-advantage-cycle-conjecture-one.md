---
slug: easlick-2026-minimal-advantage-cycle-conjecture-one
bibkey: easlick2026minimaldice
doi: null
url: https://arxiv.org/abs/2610.40321v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Dice/EaslickSixBound.conjecture_one
---

# Easlick's complete minimal-advantage dice cycle conjecture

## Problem

Terry Easlick, *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*, arXiv:2610.40321v1, Conjecture 1, states:

> n=6 is the largest n≥3 such that the set of non-standard n-sided dice admits a non-transitive cycle of maximum length n with uniform and minimal winning advantage.

The exact target is the conjunction $S(6)$ and $\forall n\in\mathbb N,\ n\ge7\Rightarrow\neg S(n)$.
For $n\ge3$, a die is a nondecreasing list of exactly $n$ labels in $[1,n]$, with repetitions permitted. The standard tuple is included, as in the source's Example 1 and its full graph enumeration. Each of the $n^2$ independent face-index pairs has equal weight. A strict win excludes ties from the numerator and retains them in the denominator.
Let $m_n$ be the least attainable strict-win probability greater than one half. An edge $d\to e$ means that the actual unconditional probability that $d$ beats $e$ equals $m_n$. A cycle is a nonempty list of pairwise distinct dice, with every successive edge and its closing edge. The proposition $S(n)$ says that a cycle of length $n$ exists and that no cycle of any length $k>n$ exists. The theorem quantifies over all such $k$ and all $n\ge7$; it introduces no finite cutoff.

## Motivation

A local winning margin does not determine a global cycle bound. The six-face case requires an upper bound over the entire graph, whereas excluding every larger face count requires a uniform construction. The settlement combines those two obligations without replacing the source's attained-minimum graph by an assumed score graph.

## Gap

The complete source question is registered in [issue #24119](https://github.com/the-omega-institute/trureturing/issues/24119). The pinned source explicitly labels Conjecture 1 and its general determination as open. Bounded prior source-family and repository searches found no exact reusable settlement; OpenAlex coverage was rate limited. Current exact repository searches for Easlick and arXiv:2610.40321v1 identify this source note and this delivery. These searches delimit checked surfaces and establish no worldwide absence or priority claim. No corresponding theory volume is present, so the modules use the canonical uncovered deposit route.

## Route

The four mathematical modules establish the following live chain.

1. `EaslickMinimalAdvantage` equates occurrence counting with the full independent face-index product. Explicit even and odd attaining pairs prove the least attainable strict-win probability, rather than assuming the author's formula. For even $n$ it is $1/2+1/n^2$ and for odd $n$ it is $1/2+1/(2n^2)$. The exact edge criterion is consequently an integer score equality. Generic nested padding preserves die validity, gives the two-sided clone win-count identity, and recovers seeds and clone indices from constructed dice.
2. `EaslickCycleSeeds` proves arbitrary-input soundness of an executable die/cycle checker and kernel-checks six concrete seed cycles. Their face counts are 6, 7, 8, 9, 10 and 11, with respective lengths 6, 14, 29, 10, 110 and 14. The seven- through ten-face input rows reproduce Easlick's Appendices G--J; the six-face witness is constructed here and the eleven-face witness is derived by padding. Each cycle has its closing edge, valid vertices and no repeated vertex.
3. `EaslickPaddedCycles` constructs a single simple closed cycle from nested clone blocks, proving quotient/remainder injectivity, alternating orientations, wrap-around and exact minimum-edge preservation. The seed branches handle 7 through 11; the generic construction handles every larger even and odd face count. For every $n\ge7$ it constructs a cycle longer than $n$, which contradicts $S(n)$.
4. `EaslickSixBound` enumerates all 462 sorted six-face dice. Its arbitrary-input rank/fiber/cut checker proves a bound for every simple closed cycle in a checked finite graph. The actual score-19 graph and rank tables pass that checker by kernel reduction. Rank is constant around a cycle. Each rank fiber has at most seven vertices; in each seven-vertex fiber, two distinct vertices have the same unique internal successor. A seven-cycle would exhaust that fiber and contradict successor injectivity. This bounds every six-face cycle by six. The explicit six-cycle attains the bound, proving $S(6)$, and `conjecture_one` combines both unbounded obligations.

## Falsifier

A failure of the occurrence/index bridge, minimum attainment, die validity, distinctness, closing edge, padding injectivity, complete six-die enumeration or generic checker soundness would invalidate the corresponding formal route. A proof only for finitely many face counts or lengths would not settle this question. The retained theorem is exactly `ConjectureOne`, not a finite-prefix surrogate or a statement conditional on an unverified certificate law.

## Evidence

The Lean sources and matching canonical Blueprint Scribes are `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.lean`, `EaslickCycleSeeds.lean`, `EaslickPaddedCycles.lean` and `EaslickSixBound.lean`, with the same basename under `Blueprint/D5/S3/Combinatorics/Dice/`. The final declaration is `D5/S3/Combinatorics/Dice/EaslickSixBound.conjecture_one`. Its typed `OpenProblemResolutionClaim` selects this whole question with `ResolutionKind.Proved`. The four modules expose 37 mirrored declarations, including 21 public theorems; current scoped kernel evidence uses only `propext`, `Classical.choice` and `Quot.sound`.

Easlick's source and reused seed rows are attributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) in the source module, Blueprint and `Library/Certificates/easlick2026minimaldice.md`. Citation of source definitions, stated minimum and stated six-face result is distinct from repository-derived padding, checker soundness, exact certificates and the complete conjecture proof.

## Triage

Tier 1, `theorem`, complete resolution `Proved`. Supporting modules have substantive escape witnesses and live consumers. `EaslickCycleSeeds` and `EaslickSixBound` have checker utility: each supplies arbitrary-input soundness, an actual checked first instance and a consumer in the final proof. `EaslickMinimalAdvantage` and `EaslickPaddedCycles` have `utility: none` and supply reusable unbounded constructions. The final exact external question uses open-problem-resolution admission. Consumed bind-only helpers remain proof organization and are not counted as new mathematical content.

Four-slot escape audits are unfinished under the [issue #24145 exception](https://github.com/the-omega-institute/trureturing/issues/24145). Of 21 public theorem targets, only `above_half_iff`, `minimum_probability` and `edge_iff` are `declared_validated`; their Reg source is preserved. `winCount_eq_indexWinCount` is `declared_unresolved`, IE-C050. The other 17 targets have missing or unvalidated audits: `threshold_attained`, `padded_winCount`, `threshold_padding`, `padded_isDie`, `padded_eq_imp`, `checkCycle_sound`, `sourceSeed_check`, `finite_cycle_witnesses`, `cycle_edge_at`, `padded_cycle`, `longer_cycle`, `not_S_above_six`, `checkRank_sound`, `sixRank_check`, `six_cycle_bound`, `S_six` and `conjecture_one`. This includes all four checker soundness/instance results; the issue's existing text does not enumerate those four. The exception is disclosed for the entire target set, and supplies no audit validation or mathematical proof.

An exact successor candidate is to determine, for every $n\ge7$, the maximum simple-cycle length in this same attained-minimum graph. The present theorem constructs a length greater than $n$ and does not determine that maximum. This candidate remains open here and has no new prediction or research terminal.

## ASSUMED-UNVERIFIED

Lean verifies the encoded mathematical statements, not external authorship, licensing or publication history. Source interpretation and provenance retain the accepted independent pre-freeze review's scope; bounded literature searches are not exhaustive. Missing audits remain missing despite the linked exception. Repository freezing and a registered resolution claim do not establish PR merge, dev integration, worldwide priority or a delivered KPI. The original mathematical cutoff, late confirmation and prediction scores are unchanged; this is publication of the existing proof.
