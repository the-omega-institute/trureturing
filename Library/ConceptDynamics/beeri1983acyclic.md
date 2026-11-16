---
bibkey: beeri1983acyclic
authors: "Catriel Beeri; Ronald Fagin; David Maier; Mihalis Yannakakis"
year: 1983
title: "On the Desirability of Acyclic Database Schemes"
doi: 10.1145/2402.322389
url: https://s3.us.cloud-object-storage.appdomain.cloud/res-files/500-jacm83a.pdf
claim: "Theorem 3.4 relates chordality and conformality to universal pairwise-to-global consistency for finite database schemes; the module gives an explicit Boolean two-row chordless-cycle obstruction over arbitrary variable and scope types with empty join."
strata_touched:
  - D5/S3/ConceptDynamics/Gluing/TwoRowCycleObstruction
license: citation-only
triage: anchor
---

# Acyclic database schemes and the chordless cycle obstruction

Catriel Beeri, Ronald Fagin, David Maier, and Mihalis Yannakakis,
*On the Desirability of Acyclic Database Schemes*, Journal of the ACM
30(3) (1983), 479–513, DOI
[10.1145/2402.322389](https://doi.org/10.1145/2402.322389).
The [primary text](https://s3.us.cloud-object-storage.appdomain.cloud/res-files/500-jacm83a.pdf)
provides the following locators:

- Section 3, printed page 484, defines chordality and conformality.
- Condition 3.7, printed page 485, defines pairwise consistency by equality
  of projections onto complete shared attributes. Global consistency means
  the existence of a universal relation with exactly the given projections.
- Theorem 3.4, printed page 488, conditions (3) and (7), relates chordality
  and conformality to universal pairwise-to-global consistency. Its proof
  begins on printed page 492.

The published theorem concerns finite database schemes. Failure of global
consistency alone does not assert an empty natural join.

`TwoRowCycleObstruction` supplies an explicit Boolean obstruction from an
induced cycle of any length at least four. Boolean edge charges are zero
along a successor path and one at the closing edge, also for even cycles.
Chordlessness gives coherent local potentials. Each scope has the range
of a Boolean indexed row constructor, hence one or two rows. On cycle
coordinates the rows use the two phase choices; all other coordinates are
false. The constant difference between local potentials aligns phases on
shared cycle coordinates, and both rows are false on the remaining shared
coordinates. Thus every row extends across the complete intersection,
while the odd total charge excludes every global satisfying assignment.

Both the scope index and the ambient variable type are arbitrary and
independently universed. Empty, duplicate and contained scopes are allowed.
A scope with empty cycle support has only one row. This exact telescope
and construction are not attributed verbatim to Theorem 3.4. The finite
schema theorem supplies classical background, without a claim that the
paper states this arbitrary-carrier two-row result or a claim of originality.
Only the chordless cycle branch is established, without the full
acyclicity classification.

## Verified locator

- DOI: 10.1145/2402.322389
- Primary text: https://s3.us.cloud-object-storage.appdomain.cloud/res-files/500-jacm83a.pdf
- Theorem 3.4, printed page 488, and Condition 3.7, printed page 485.
