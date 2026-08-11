---
bibkey: newman1942theories
authors: M. H. A. Newman
year: 1942
title: 'On Theories with a Combinatorial Definition of "Equivalence"'
doi: 10.2307/1968867
claim: Termination and local confluence give a unique reachable normal form.
strata_touched:
  - D5/S0/Rewriting/Newman
license: citation-only
triage: anchor
---

# On Theories with a Combinatorial Definition of "Equivalence"

M. H. A. Newman's paper proves the terminating local-confluence principle now
known as Newman's lemma: when reduction admits no infinite descending chain and
every one-step fork is joinable, every starting term has a unique reachable
irreducible normal form.

The repository declaration states this principle for an arbitrary binary
relation. Termination is expressed by well-foundedness of the swapped relation,
local confluence explicitly joins every pair of one-step successors through
reflexive transitive closure, and the conclusion supplies exactly one reachable
irreducible endpoint for every starting term. The Lean proof is direct; the
literature note attests the theorem statement rather than the proof term.

## Search log

- 2026-08-11: Queried Crossref for DOI `10.2307/1968867`. The resolver returned
  M. H. A. Newman, the exact article title, April 1942, *The Annals of
  Mathematics* 43(2), starting at page 223.
- 2026-08-11: Searched the pinned Mathlib checkout for Newman, termination plus
  local confluence, and unique normal forms. No general reusable theorem was
  found; the repository declaration therefore retains its direct proof.

## Verified locator

- DOI: https://doi.org/10.2307/1968867
