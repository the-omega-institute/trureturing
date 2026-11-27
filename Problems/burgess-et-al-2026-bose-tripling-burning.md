---
slug: burgess-et-al-2026-bose-tripling-burning
bibkey: burgess2026burningsteiner
doi: null
url: https://arxiv.org/html/2608.25627v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.claim
  - D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.result
---

# Ordinary burning under Bose tripling of Steiner triple systems

## Problem

Andrea C. Burgess, Peter H. Danziger, Caleb W. Jones, Trent G. Marbach and
David A. Pike ask in §5 of *Burning Steiner Triple Systems*:

> Theorems 4.7 and 4.8 also show that doubling a projective triple system or tripling an affine triple system increases the burning number by one. We ask if these are the only non-degenerate systems whose burning numbers increase on doubling or tripling.

The tripling implication registered in [#34982](https://github.com/the-omega-institute/trureturing/issues/34982) says that for every nonempty finite Steiner triple system $H$, if $H$ is nondegenerate and $b(H)<b(\operatorname{Bose}(H))$, then $H$ is isomorphic to a projective $\mathrm{PG}(d,2)$ or an affine $\mathrm{AG}(e,3)$ triple system. The source and the registered operation are located in the [Library note](../Library/FiniteGeometry/burgess2026burningsteiner.md).

## Motivation

The implication asks whether a rise in ordinary burning number identifies the geometric input families. An ordinary round chooses a source outside the preceding burned set and simultaneously adds the completions of pairs from that preceding set. The source may also be reached by propagation in its own round. Lazy burning repeatedly completes pairs from a seed set, and $b_L$ is the minimum seed size. Nondegeneracy requires $b_L(K)=b_L(H)-1$ for every inclusion-maximal nonempty proper subsystem $K$.

## Gap

This is a Tier 1 question from §5. The preregistration records bounded arXiv, Crossref, repository, GitHub and related-paper searches that found no settlement of the cited Bose implication. Its OpenAlex citing-work search was rate-limited. [Preregistration #34982](https://github.com/the-omega-institute/trureturing/issues/34982)

## Route

Take the translates of $\{0,1,4\}$ and $\{0,2,7\}$ modulo 13. The pair completion defines a Steiner triple system. Every nonblock triple generates the full system, so every maximal proper subsystem is a block. The base has lazy burning number 3, and every block has lazy burning number 2.

The Bose construction uses the vertical triples and $\{(x,i),(y,i),(x*y,i+1)\}$ for distinct $x,y$, with layers modulo 3 and $x*y$ the base pair completion. A legal schedule for the base is $(0,1,2,3,6)$. For the order-39 Bose system, with points encoded by $3x+i$, a legal schedule is $(0,1,3,6,4,7)$. The four-round upper bound is 8 burned points. In the fifth round, at most $\binom{8}{2}$ further pair completions and one source give at most 37 burned points. These bounds and schedules give exact ordinary burning numbers 5 and 6.

Projective orders have the form $2^{d+1}-1$, with 13 strictly between 7 and 15. Affine orders have the form $3^e$, with 13 strictly between 9 and 27. Thus the base belongs to neither family.

## Falsifier

The witness must satisfy unique pair completion, nondegeneracy over all maximal proper subsystems, strict increase under the specified Bose blocks and exclusion from both geometric families. The exact burning numbers require legal schedules and lower bounds under the preceding-round propagation rule.

## Evidence

The frozen `D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.result` has type `¬ claim`. Its proof uses the two exact ordinary burning numbers, nondegeneracy and the two family exclusions. The Blueprint attaches `OpenProblemResolutionClaim` with `ResolutionKind.Refuted` to this declaration.

The admission basis is `open-problem-resolution (#34982)`. The proof shape of `result` is `content`. Its live dependencies `burning13` and `burning39` use finite schedule certificates and universal small-round bounds. The designated refutation result is exempt from four-slot escape registration.

## Triage

### What the settlement shows

- **Proved by `BoseTriplingBurningRefutation.result`.** A nondegenerate order-13 system outside both geometric families has a one-round increase under Bose tripling. Even an increase of exactly one fails to characterize those families for this operation.
- **Open here.** A classification of systems whose burning number increases under Bose tripling, the doubling question, and the direct-product tripling reading remain outside this settlement.
- **Source scope.** The publication's claim in §5 that tripling $\mathrm{AG}(m,3)$ produces $\mathrm{AG}(m+1,3)$ conflicts with its cited Bose block rule. In the Bose tripling of $\mathrm{AG}(2,3)$, the seed $\{((0,0),0),((1,0),0),((0,1),0)\}$ has sizes $3,6,12,27$ under successive simultaneous pair completions. The direct product with the three-point affine system uses coordinatewise completion and gives $\mathrm{AG}(3,3)$, where any three points generate at most their nine-point affine span. This finite calculation distinguishes the two operations. The Lean result concerns the registered order-13 witness and the exclusivity implication for Bose tripling. [Publication §5](https://arxiv.org/html/2608.25627v1#S5.p4)

## ASSUMED-UNVERIFIED

Literature completeness and independent priority remain unverified beyond the searches recorded in #34982.
