---
slug: feldman-zigzag-conjecture-nine-three
bibkey: feldman2026missingzigzag
doi: null
url: https://arxiv.org/html/2609.26114v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.feldman_conjecture_nine_three
---

# Feldman's Conjecture 9.3: balanced zigzag choices

## Problem

David V. Feldman, *The Missing Zigzag: Cycles of Semitone Trichords and a
Conservation Law in Equal Temperament*, arXiv:2609.26114v1, Section 5,
equation (2), Conjecture 9.3. For each integer `t>=2`, set `n=3t`. For every
`k=2,...,n-2`, choose one labelled directed form in `ZMod n`:

| Label | From | To |
| --- | --- | --- |
| I | `1` | `k-1` |
| II | `k` | `1-k` |
| III | `-1` | `k` |
| IV | `k-1` | `-k` |
| V | `-k` | `1` |
| VI | `1-k` | `-1` |

At `k=2`, exactly II, III, IV, and V are permitted. Labels remain different
choices when their endpoint pairs coincide. Balance means integer
outdegree minus indegree zero at each nonzero residue; no closedness,
connectivity, Eulerian-circuit, or cycle condition is added. Let `a(t)` be
the number of these actual balanced labelled choices. The full conjecture is

`a(2)=4`; for every `r>=2`, `a(2r)=4a(2r-1)`; and for every `r>=1`,
`(2r)a(2r+1)=6(2r-1)a(2r)`.

## Motivation

The finite choice object and balance predicate in `Choices.lean` directly
encode the stated count. The endpoint in
`FeldmanConjectureNineThree.feldman_conjecture_nine_three` carries all three
clauses in a single theorem. Its two companion closed-count theorems establish,
for every `r>=1`, `a(2r)=4*6^(r-1)*choose(2r-2,r-1)` and
`a(2r+1)=2*6^r*choose(2r-1,r)`, which are stronger than the recurrences.

## Gap

The mathematical candidate has a kernel-checked all-parameter proof and an
independent source review for its exact source checkpoint. The repository
has canonical joint first-Freeze state files for the eleven Zigzag modules.
The endpoint's typed Scribe `Proved` claim binds the sole Conjecture 9.3 result
to this dossier, and its emitted Markdown carries the matching resolution
marker. Current required CI, merge into `dev`, and completion audit remain
pending. Resolution is derived from the typed claim, not hand-written here.

The bounded prior-art screen in the Library note found no matching later
public proof in its checked sources. It did not establish global novelty or
priority. The author's pinned repository treats a stricter finite `BadPlan12`
and lacks this all-parameter balance-only theorem.

## Route

Inversion pairs the nonchromatic classes. `PathData` records five reachable
frontier states in each of two signed sectors, with twelve distinct labelled
interior transitions per sector. `ChoiceClassification` and `Retirement`
prove that old interior nodes cannot be touched by later edges, and that the
remaining local balance equations force the recorded transitions. `PathEncoding`
turns paths into labelled choices; `DecodedBalance` recovers their balance
and injectivity. `EvenPaths` handles the antipodal terminal pair and
`OddPaths` the singleton terminal, proving both literal choice/path
equivalences for all positive `r`.

`WeightedPaths` counts the positive-sector path charges in a finite Laurent
polynomial. Its scalar recurrence has seeds `f_0=2`, `f_1=4z` and
`f_m=2z f_(m-1)+3z^(-1) f_(m-2)`. The negative sector is reached through a
label-aware reflection, not an identification of its form labels.
`LaurentCoefficients` solves the recurrence by a finite antidiagonal sum and
extracts the two required coefficients. The endpoint composes these with
the exact even and odd equivalences and the elementary binomial identities.

## Falsifier

An omitted balanced choice, lost multiplicity from coincident endpoints,
later edge touching a retired vertex, missing antipodal or singleton terminal,
failure of either inverse law, coefficient mismatch, or extra source
restriction would break this correspondence. A recurrence for a proxy count
without the equivalences would not settle the question.

## Evidence

For the source checkpoint `d2621fdf37c370557f924c11b26ff706d0d4964b`,
the source review approved all eleven Lean owners and all 68 theorems;
designated independent tests reported kernel exit 0 over 1489 jobs and
consumer checks at `t=2,3,4`. The reported axiom closure contains only
`propext`, `Classical.choice`, and `Quot.sound`. These are source-stage
readings; the companion, joint first Freeze, and typed binding have separate
local checks. Current required CI and completion audit remain pending.
Independent finite table and boundary tests found literal
balanced counts `4,12,48` at `n=6,9,12`; they do not replace the all-`r`
proof.

## Triage

`theorem`; Tier 1 external named Conjecture 9.3, preregistered before the
probe. This record anchors only that conjecture, not the broader Open
Problem 13.1. The theorem's content admission and source fidelity have
independent source-stage approval. Delivery and KPI credit require current
required CI, merge into `dev`, and completion audit; this record claims neither.

## ASSUMED-UNVERIFIED

The bounded literature screen excludes neither private nor unindexed work,
and OpenAlex/Semantic Scholar were rate limited. Worldwide absence, priority,
final publication, and post-checkpoint future CI are not verified by this
record. The Lean kernel verifies the formal statements, not their mapping to
the published prose; that mapping has a separate source review.
