---
bibkey: notik2026singergolomb
authors: Esther Notik
year: 2026
title: "Golomb rulers with real marks: the real and integer optima agree up to ten marks"
doi: 10.48550/arXiv.2611.22656
url: https://arxiv.org/abs/2611.22656v1
claim: "The paper defines real order chambers, conjectures chamber uniqueness for Singer rulers, and asks whether it extends to the Bose and Ruzsa families."
strata_touched:
  - D5/S3/Geometry/FiniteGeometry/NotikSingerChamber
  - D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber
  - D5/S3/Combinatorics/Golomb/Replay
  - D5/S3/Combinatorics/Golomb/EqualityReplay
  - D5/S3/Combinatorics/Golomb/NotikMinimizers
license: citation-only
triage: anchor
---

# Cyclic constructions in real Golomb chambers

## Verified locator

- arXiv v1 https://arxiv.org/abs/2611.22656v1
- DOI https://doi.org/10.48550/arXiv.2611.22656

The arXiv v1 record and DataCite metadata identify Esther Notik and the title above.

## Source statements

[Section 2 of the paper](https://arxiv.org/pdf/2611.22656v1#page=2) defines a
chamber by inequalities whose directions are fixed by the order of the
labelled distances. Each distance is at least one and each larger distance
exceeds each smaller one by at least one.

[Section 7](https://arxiv.org/pdf/2611.22656v1#page=7) constructs the ordinary
rulers from unit multiples of Singer perfect difference sets. It cuts the
cycle at a largest gap. The conjecture there states that every ruler made
this way is the only shortest point of its chamber. Notik reports exact
certificates for 24,450 distinct Singer rulers with prime-power order at most
103. [Companion code and data](https://doi.org/10.5281/zenodo.24309145).

## Bose and Ruzsa chamber questions

The last bullet of §10, page 8, asks

> Prove the conjecture of Section 7 for all prime powers, for instance by structured dual
> certificates as for the Conway–Guy and Bohman sets in [12]; and ask the same for the rulers
> of Bose [4] and Ruzsa [15].

Notik cites R. C. Bose, “An affine analogue of Singer's theorem”, J. Indian Math.
Soc. (N.S.) 6 (1942), 1–15, and I. Z. Ruzsa, “Solving a linear equation in a set of
integers I”, Acta Arith. 65 (1993), 259–282. [Ruzsa, Theorem 4.4](https://doi.org/10.4064/aa-65-3-259-282)

## Real minimizers with eight to ten marks

Esther Notik defines normalized real rulers by strict increase from zero, pair distances of at least one, and distances of distinct pairs separated by at least one. Theorem 1 gives minima (34,44,55) for eight, nine, and ten marks. Section 10, p. 8, third bullet, asks whether the shortest real rulers at these sizes are exactly the optimal integer rulers. [Paper, arXiv:2611.22656v1](https://arxiv.org/pdf/2611.22656v1#page=8)

The companion archive contains exact branch trees for the lower bounds from five through ten marks. The archived trees and static rows represented in Lean are adapted from Esther Notik's v3 data under CC BY 4.0. The tied-leaf certificates extend the replay to the equality question. [Zenodo archive v3](https://doi.org/10.5281/zenodo.24309145) · [Data attribution and license](../../docs/reports/licenses/notik-golomb-archive.md)
