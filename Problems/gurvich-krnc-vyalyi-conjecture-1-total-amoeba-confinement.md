---
slug: gurvich-krnc-vyalyi-conjecture-1-total-amoeba-confinement
bibkey: gurvichkrncvyalyi2025amoebas
doi: 10.1007/s00025-025-02421-6
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Walks/AmoebaHost.total_confinement
url: https://arxiv.org/abs/2401.07484
---

## Problem

Vladimir Gurvich, Matjaž Krnc and Mikhail Vyalyi, *Growing Trees and
Amoebas’ Replications*, arXiv:2401.07484v1/v2 and DOI
[10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6), state
Conjecture 1 in Section 2.1 of arXiv v1 and on page 11 of the published PDF:
if an amoeba A=(H,m) has maximum degree greater than its number of roots k by
more than two, then A is totally confined.

The formal target keeps the complete ordinary finite-host reading: every finite
simple tree H, every multiplicity function m, every extension length l, every
finite initial tree T containing H, every multiplicity-preserving copy and
transported multiplicity placement, every simultaneous family of distinct arms,
and every minimum growth ordered by total host edges. Length zero,
zero multiplicities and k=0 remain included. Total confinement requires a finite
host containing T in which every such copy is dead.

## Motivation

The result addresses the complete named conjecture, including its universal
quantifiers over copies, initial hosts, arms and total-edge minimizers. The
source's infinite union-limit questions are separate and are not part of this
finite assertion.

## Gap

The source leaves this finite total-confinement assertion open. The proof must
construct a finite host for an arbitrary initial T, realize all transported
multiplicity arms simultaneously for every copy, and show that every
minimum-total-edge growth coincides with the containing host. A bounded example,
a selected growth, an infinite-host cardinal argument or a narrower arm model
would leave the target unresolved.

## Route

The formalization uses a finite layered tree. A safe branching degree avoids
all intervals [deg_H(v), deg_H(v)+m(v)) at once. The core receives a finite
branching budget and a finite depth buffer. Unique paths in a tree place every
copy within the core radius, supply the required fresh first edges jointly,
and continue every arm without return or collision. The total-edge comparison
then forces surjectivity and adjacency reflection for every minimizing
containing map. The arbitrary initial copy is preserved by the core embedding.

## Falsifier

A finite H, multiplicity function m and length l satisfying the strict degree
condition, together with a finite initial T containing H, for which no finite
confining supertree exists would refute the result. A counterexample must use
all copies, transported multiplicities, simultaneous arms and total host-edge
minimization. Failure of a different construction or an infinite-host variant
would not refute this statement.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/Graph/Walks/AmoebaHost.total_confinement`. Its definitions
and supporting theorems are in `AmoebaConfinement` and `AmoebaHost`; the emitted
Blueprint pages mirror the closed Lean statements. The canonical scoped report
covers both modules and records the standard axiom closure
`Classical.choice`, `Quot.sound` and `propext`. The Library note
`D5/L/Combinatorics/gurvichkrncvyalyi2025amoebas` records the verified DOI,
URLs and source locators.

The source mapping is the published Section 2 definitions and Conjecture 1,
with the arXiv v1/v2 versions as corresponding source records. The construction
retains every original finite quantifier and makes no claim about infinite
cardinal minimization.

## Triage

### What the settlement shows

- **Settlement — proved, kernel-checked:** `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.total_confinement` proves the complete finite-host Conjecture 1 under the stated degree condition.
- **Mechanism — proved, kernel-checked:** `exists_safe_degree` supplies a branching degree outside every multiplicity demand interval; `exists_buffered_host` supplies a finite layered host with the required core budgets and depth; `sprout_copy`, `hasExtension_one` and `hasExtension_of_buffer` give simultaneous fresh arms and their finite continuations; `dead_of_hasExtension` turns total-edge minimality into coincidence with the same containing host.
- **Boundary — retained:** the theorem includes l=0, m=0 and k=0, all transported multiplicity placements and all minimum total-edge growths. It concerns finite simple tree hosts. Infinite union limits and cardinal minimization remain separate questions.
- **Escape audit — unfinished:** the eight public theorem targets named by the preregistration have no `declared_validated` Reg mirrors. The concrete audit boundary and missing dependent-family evidence are disclosed under [issue #23364](https://github.com/the-omega-institute/trureturing/issues/23364#stage-a-escape-audit-boundary). No registration is represented as validated.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the cited arXiv versions, published paper,
direct predecessor and the recorded repository search. Worldwide absence,
priority, novelty and completeness of all indexed or posted work are
ASSUMED-UNVERIFIED. No such claim is needed for the formal theorem or its
canonical resolution metadata.
