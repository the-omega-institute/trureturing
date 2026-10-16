---
slug: klavzar-et-al-2025-mobile-general-position-cylinders
bibkey: klavzaretal2026mobileproducts
doi: 10.1016/j.dam.2025.10.041
url: https://arxiv.org/abs/2505.00535
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.result
---

# Mobile general position on the seven-cycle and ten-cycle cylinders

## Problem

Klavžar, Krishnakumar, Kuziak, Shallcross, Tuite and Yero, “Moving through
Cartesian products, coronas and joins in general position”, arXiv:2505.00535v2,
Discrete Applied Mathematics 379 (2026), 768–780,
DOI 10.1016/j.dam.2025.10.041, Section 3, after Proposition 3.7:

> Hence, the only unknown values are Mobgp(C₇ □ Pₛ) and Mobgp(C₁₀ □ Pₛ) for s ≥ 5. We conjecture that the answer is four in these cases.

The conclusion is $\operatorname{Mob}_{gp}(C_7\square P_s)=
\operatorname{Mob}_{gp}(C_{10}\square P_s)=4$ for every integer $s\ge5$.
It is the tier-1 published conjecture preregistered in
[issue #17705](https://github.com/the-omega-institute/trureturing/issues/17705).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Shortest-path membership | `OnGeodesic` | Sum of the two distances equals the endpoint distance, on the connected cylinders. |
| No three occupied vertices on a common shortest path | `IsGeneralPosition` | All triples of pairwise distinct occupied vertices are quantified. |
| One move along an edge to an unoccupied vertex, preserving general position | `LegalMove` | Exactly one occupied vertex is erased and the new vertex inserted. |
| A sequence of legal moves from the initial set visits every vertex | `IsMobile` | A finite sequence with the stated initial configuration, every consecutive move legal, and a visit to every vertex. |
| Largest cardinality of a mobile general position set | `mobGP` | Natural-number supremum; the upper bound and a size-four witness establish attainment here. |
| Cartesian product of cycle and path | `cylinder` | Mathlib `cycleGraph r` and `pathGraph s`, on `Fin r × Fin s`; path height counts vertices. |
| Both exceptional circumferences, all $s\ge5$, answer four | `claim`, `result` | Both equalities, the natural-height quantifier and its guard occur literally. |

Zero-based labels are a relabelling of the source vertices. The pairwise
inequalities in `IsGeneralPosition` express three distinct vertices; the
sequence length and configuration indices express the source's finite moves.
They impose no extra hypothesis on the cylinder claim.

## Motivation

These are the two cylinder families left undetermined by Section 3 of the
source. The theorem settles both for every height in the published question.
The source's prism results and Proposition 3.7 determine the other cylinder
circumferences in this range.

## Gap

The source explicitly leaves the two values open. The literature screen
includes arXiv:2507.16622, arXiv:2501.19385v5, arXiv:2510.01294v2,
arXiv:2604.15909v1 and arXiv:2412.09837v3; no prior settlement was found in
that scope. Literature completeness remains `ASSUMED-UNVERIFIED`.

## Route

The module is
`D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.lean`.
Its sole public theorem is `result : claim`, with admission basis
`open-problem-resolution (#17705; Proved)`.

The cycle metric uses `MatchingCliqueCycle.cycle_distance`, published at its
existing owner `D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.lean`.
The module combines the cycle and path metrics, classifies the five cycle
coordinates in row order, and propagates an invariant of the occupied
columns. A constructive four-robot traversal supplies the matching lower
bound. All supporting lemmas remain private and are used by the proof.

## Falsifier

A mobile general position set of at least five robots in either cylinder,
or a failure of the four-robot construction at an admitted height, would
contradict the theorem. The Lean statement fixes the graph, general-position
condition, legal moves, and complete-coverage quantifier; it assumes no
rigidity or reachability conclusion.

## Evidence

`D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.result` proves
both equalities for every $s\ge5$. The axiom closure of every public
declaration is contained in `{propext, Classical.choice, Quot.sound}`.
The Scribe renders the complete definitions and the expanded result.

The independent numerical check is in the experiments repository:
[mobile-cylinder check at 638142ac63ccff568077b19b8eae6183b5fd4db3](https://github.com/the-omega-institute/trureturing-experiments/tree/638142ac63ccff568077b19b8eae6183b5fd4db3/docs/reports/klavzar-et-al-2025-mobile-general-position-cylinders).
Command: `python3 -I docs/reports/klavzar-et-al-2025-mobile-general-position-cylinders/check.py`
from that repository; exit 0, `ALL_OK`. Script SHA-256:
`a7c9084d88b575e0b6ec7198d2bc4cc38fbb076c6255a1600d526fb3c7b117e6`.
It finds exactly 14 angular words for $r=7$ and 20 for $r=10$; at
$s=2,\ldots,6$ it checks the six-vertex obstruction and vertical-only legal
moves of five robots. Five-set counts for $s=2,3,4,5,6$ are respectively
$(0,0,0,14,84)$ and $(0,0,0,20,120)$. It checks a legal covering four-robot
traversal for $s=2,\ldots,8$. These finite computations do not supply the
uniform-height proof.

Escape audit unfinished:
[issue #17763](https://github.com/the-omega-institute/trureturing/issues/17763)
covers `CylinderSevenTen.result` and the published
`MatchingCliqueCycle.cycle_distance`. The missing evidence comprises lawful
source reconstruction, enrolled readout and variation, sensitivity and
observational-dependence proofs. No completed registration is claimed.

## Triage

### What the settlement shows

- **Mechanism — kernel-checked.** For $r=3a+1$ with $a=2,3$, `rigidity`
  classifies five cycle coordinates whose ordered triples are non-geodesic
  as $b+\varepsilon ai$, $\varepsilon\in\{-1,1\}$. The private
  `five_strict_rows` gives distinct rows for a five-vertex general position
  set. The private `gp_card_le_five` excludes six vertices, `no_horizontal`
  forces legal moves of five robots to be vertical, and `no_five_mobile`
  propagates the unvisited-column obstruction. These declarations occur in
  the kernel-checked proof of `result`.
- **Range — kernel-checked.** `mobile_card_le_four` bounds every mobile set
  by four at every natural height. `four_mobile` constructs a cardinality-four
  mobile set for every $s\ge2$, for $r=7,10$. The public `result` retains
  exactly the published $s\ge5$ guard.
- **Consequences — proved in prose from the source and this result.** Section 3
  following Theorem 3.4 and Lemma 3.5 gives value four for $r\in\{5,6,8\}$
  and $s\ge5$; Proposition 3.7 gives value five for $r=9$ or $r\ge11$.
  The present result gives value four for $r\in\{7,10\}$. These disjoint
  cases exhaust $r\ge5$, so every cylinder value in the range
  $r\ge5$, $s\ge5$ is determined. This classification is a paper-level
  consequence; no additional public classification theorem is asserted.
- **Cylinder completion — proved in prose.** The case split above leaves none
  of the source's cylinder cases unresolved.
- **Torus boundary — open.** The values on torus graphs
  $C_r\square C_s$ remain outside this settlement; the source's Corollary 3.8
  and its torus classification question are unchanged. No torus value follows
  solely from the cylinder proof.
- **Experiment — computed.** The pinned experiment entry in Evidence gives
  the exact finite ranges, command, exit and script SHA-256. Uniform extension
  beyond those tested ranges is supported by the Lean lemmas named above,
  not by extrapolation of the computation.
- **Literature — literature reading.** The source v2 and the screen listed in
  Gap contain no located prior settlement. Completeness is
  `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The literature screen is bounded and is not an exhaustive proof of absence
of a prior settlement. No physical realization, torus classification or
completed escape registration is asserted. The linked audit issue is a
disclosure of missing registration evidence and is not mathematical evidence.
