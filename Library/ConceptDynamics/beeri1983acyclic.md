---
bibkey: beeri1983acyclic
authors: "Catriel Beeri; Ronald Fagin; David Maier; Mihalis Yannakakis"
year: 1983
title: "On the Desirability of Acyclic Database Schemes"
doi: 10.1145/2402.322389
url: https://s3.us.cloud-object-storage.appdomain.cloud/res-files/500-jacm83a.pdf
claim: "Theorem 3.4 equates chordality and conformality with universal pairwise-to-global consistency for finite database schemes; the module formalizes the nonconformal obstruction with an explicit finite-alphabet construction."
strata_touched:
  - D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction
license: citation-only
triage: anchor
---

# Acyclic database schemes and the nonconformal obstruction

## Verified locator

- Catriel Beeri, Ronald Fagin, David Maier, and Mihalis Yannakakis,
  *On the Desirability of Acyclic Database Schemes*, Journal of the ACM
  30(3) (1983), 479–513.
- DOI: 10.1145/2402.322389 (https://doi.org/10.1145/2402.322389).
- Primary text: https://s3.us.cloud-object-storage.appdomain.cloud/res-files/500-jacm83a.pdf
- Section 3, printed page 484, defines conformality: every clique in the
  associated graph is contained in a hyperedge.
- Condition 3.7, printed page 485, defines pairwise consistency by equality
  of projections onto shared attributes, and global consistency by a
  universal relation with exactly the given projections.
- Theorem 3.4, printed page 488, conditions (3) and (7), equates chordality
  and conformality with universal pairwise-to-global consistency; the theorem
  is restated with its proof beginning on printed page 492.

The published theorem concerns finite database schemes. Nonconformality
therefore obstructs universal pairwise-to-global consistency in that setting.
Failure of global consistency alone does not assert an empty natural join.

The module supplies its particular stronger witness: for a clique C with at
least three vertices contained in no scope, it uses C.card - 1 colors and
all scope assignments injective on the clique coordinates. These finite
relations are nonempty, have equal complete overlap projections, and have
empty natural join. Coordinates outside C are unrestricted, and their
overlap values are copied explicitly. The scope index type E is arbitrary;
this exact telescope and construction are not attributed to Theorem 3.4.
This is a known-result formalization without a novelty claim. The module
establishes only the nonconformal branch and does not establish the full
classification.
