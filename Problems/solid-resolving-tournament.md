---
slug: solid-resolving-tournament
bibkey: hakanenpavan2026solid
doi: null
url: https://arxiv.org/abs/2610.35041v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.result
---

# Tournament solid-metric lower bounds

## Problem

Hakanen and Pavan, *Solid-Resolving Sets on Directed Graphs*, arXiv:2610.35041v1,
Conjecture 3.4, page 8, asserts that every tournament of orders
$6,7,8,9,10,11$ has solid-metric dimension at least $4,5,5,5,5,6$, respectively.
The source is recorded in `Library/ConceptDynamics/hakanenpavan2026solid.md`.
Preregistration: [#22881](https://github.com/the-omega-institute/trureturing/issues/22881).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| All tournaments of order $n$ | Every relation on `Fin n` satisfying the reused loopless exclusive-or `IsTournament` | No strong-connectivity or diameter hypothesis |
| Directed distance, including unreachable vertices | `SolidResolvingTournamentBase.directedDistance`, the extended-natural infimum of directed walk lengths | Deleting repeated-vertex cycles identifies the infimum with shortest-path length |
| Distance to a nonempty vertex set | `SolidResolvingTournamentBase.distanceToSet`, the infimum over its subtype | Infinity is retained when every member is unreachable |
| Definition 1.1, every nonempty $X\ne\{v\}$ | `SolidResolvingTournamentBase.IsSolidResolving` | Literal subset quantifier and inequality |
| Minimum solid-set cardinality | `SolidResolvingTournamentBase.solidMetricDimension` | Natural infimum; full-set solidity gives attainment |
| Orders $6,7,8,9,10,11$ and bounds $4,5,5,5,5,6$ | The six conjuncts of `SolidResolvingTournament.claim`, proved by `result` | No dropped clause or extra assumption |

The namespaces in this dossier have prefix `D5.S3.Combinatorics.Graph.Walks`.
All auxiliary profile hypotheses are discharged inside the settling proof.

## Motivation

`D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.result` proves the complete
six-part claim. The decisive mechanism bounds the number of outside vertices of a
solid landmark set by a chain cover of its constrained distance profiles.

## Gap

The source presents randomized searches in support of Conjecture 3.4. A uniform
proof must handle every orientation, non-strong tournaments and infinite directed
distances. A finite search at order six does not establish the remaining five bounds.

## Route

The literal solid predicate is equivalent to the ordered-pair strict-distance
criterion. For a solid set, distinct outside vertices have incomparable profiles.
Induced landmark tournaments of sizes three, four and five admit a complete finite
classification. Directed-walk upper bounds impose the profile constraints; finite
extended-natural reduction handles strong cases, and terminal singleton, triangle
and four-vertex cases handle non-strong ones. Chain covers bound outside cardinality
by one, two and five. Adding the landmark cardinality gives total-order bounds
$3\mapsto4$, $4\mapsto6$, $5\mapsto10$. The general cardinality-to-dimension argument
then gives the six claimed inequalities.

## Falsifier

A loopless tournament on one of the six specified finite vertex types with a solid
set smaller than the corresponding claimed bound contradicts `result`. A profile
outside the certified covers, a missed induced tournament type, or an invalid
infinite-distance reduction would falsify a required intermediate argument.

## Evidence

The four modules are `SolidResolvingTournamentBase`, `SolidResolvingTournamentProfiles`,
`SolidResolvingTournamentTerminal` and `SolidResolvingTournament` in
`D5/S3/Combinatorics/Graph/Walks/`. Their Scribes display every public declaration.
The sole resolution claim is Proved on the settling `result`.

The escape audit is unfinished for all 47 public theorems and lemmas:
[#23622](https://github.com/the-omega-institute/trureturing/issues/23622).
The missing source-law reconstruction, whole-family variation, role/anchor
sensitivity and observational-dependence proofs prevent a faithful four-slot
registration. No registration is claimed validated.

### Independent computation

The experiment is [the immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/5c2d6baa984b8efd8261eea4484ceaa9e78eb0a2/docs/reports/solid-resolving-tournament).
Its `check.py` has SHA-256
`948610b5a86963b2ff1ace02aea969decf707f78f47e707ca341f8453d5c4736`.
The exact script extracted from that commit was executed with
`python3 /tmp/op-solidtour/check-rework.py`, exit 0,
with final result `ALL_CHECKS_OK`.
It checks all labelled landmark tournaments of sizes three, four and five;
strong-profile covers and non-strong terminal cases; literal versus ordered solidity
through order four; and all $32768$ labelled tournaments at order six. The order-six
dimension histogram is $\{4:1440,5:21984,6:9344\}$.
It does not enumerate all tournaments at orders seven through eleven and is not
Lean evidence for their universal bounds.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Arbitrary-order landmark bounds $3\mapsto4$, $4\mapsto6$, $5\mapsto10$ | proved | Kernel-checked private `SolidResolvingTournament.landmark_bound_3`, `landmark_bound_4`, `landmark_bound_5`; arbitrary finite ambient vertex type |
| Literal solid definition and ordered-pair criterion | proved | Kernel-checked `SolidResolvingTournamentBase.solid_iff_ordered`; the definition retains every nonempty subset |
| General path upper bounds, finite ENat reduction, terminal singleton/triangle/four-component profile bounds, conditional six-part assembly | proved | Kernel-checked `SolidResolvingTournamentBase.directedDistance_le_walkBound`, `SolidResolvingTournamentProfiles.profile_finite_bound`, `SolidResolvingTournamentTerminal.nonstrong_profile_bound_*`, `strong_enat_profile_bound`, and private `SolidResolvingTournament.claim_of_card_bounds` |
| Six universal lower bounds | proved | Kernel-checked `SolidResolvingTournament.result` with all six conjuncts |
| Independent checker | computed | The immutable script, command, exit code and SHA-256 above; exact tested scope only |
| Sharpness at arbitrary orders and other landmark sizes | open | No general sharpness or other-landmark-size theorem is asserted |

### What the settlement shows

The constrained-profile and chain-cover argument proves the landmark bounds for
arbitrary ambient order, rather than only for the six conjectured orders. It
includes infinite distances and non-strong orientations. The full six-part assertion
of Conjecture 3.4 is proved; randomized evidence is unnecessary for these lower bounds.
The order-six computation separately verifies attainment of bound four at that
order. General sharpness, the arbitrary-order minimum and existence of every
intermediate dimension remain open here. The bounded source reading identifies no
additional theorem requiring a new conclusion from this settlement; a complete
literature dependency analysis is unverified.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration records a partial
screen of the versioned source, arXiv metadata, Crossref, Semantic Scholar, OpenAlex,
MathOverflow, Zenodo, public Lean settlements and repository results. No settlement
was located in that searched scope. Rate-limited citation services, inaccessible
older full texts, the conference full text and a complete citation graph are outside
the verified reading. No claim of worldwide priority or exhaustive novelty is made.
