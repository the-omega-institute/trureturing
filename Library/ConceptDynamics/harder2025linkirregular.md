---
bibkey: harder2025linkirregular
authors: Jannis Harder
year: 2025
title: Computational search for regular link-irregular graphs, Mathstodon thread of 14 and 15 December 2025
doi: null
url: https://mathstodon.xyz/@11011110/115716795916671285
license: citation-only
triage: anchor
claim: A six-regular link-irregular graph of order eleven exists; exhaustive search over all six-regular graphs on eleven vertices yields four minimal counterexamples, one of which is separated by link degree sequences except for a single pair distinguished by whether its two degree-two vertices are adjacent.
strata_touched:
  - D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven
---

<!-- GID: D5/L/ConceptDynamics/harder2025linkirregular -->

# Order-eleven regular link-irregular graphs

Discussion thread attached to David Eppstein, "Regular link-irregular graphs",
11011110.github.io, 13 December 2025. The thread is the primary source for the
order-eleven fact; the blog post itself gives only an asymptotic construction.

Jannis Harder, 14 December 2025, reporting on a script using networkx and
pynauty, states that it "finds a 6-regular link-irregular graph of order 11".

Jannis Harder, 15 December 2025: "Of the four minimal counterexamples (found by
going through all 6-regular 11-vertex graphs) there is one where the degree
sequences of the links are almost sufficient to show that they all belong to
distinct isomorphism classes. There is one pair that shares a degree sequence
but only one of them connects two degree-2 vertices, so they can't be isomorphic
either."

The repository witness in the module listed above has that same structure: the
links of two of its vertices share the degree multiset (2,2,3,3,3,3) and are
separated by the adjacency of their two degree-two vertices. The graph published
in that thread and the repository witness were reported to be isomorphic by an
independent web-enabled review seat; the repository did not verify the
isomorphism itself, and does not claim the witness as new.

Order ten is not settled by this source. The reported sampling at order ten was
unsuccessful, which is not a nonexistence proof.

## Verified locator

https://mathstodon.xyz/@11011110/115716795916671285 - the thread rooted at that
status. The two load-bearing posts are by the account jix, dated 14 December 2025
and 15 December 2025. Retrieved 2026-09-11 through the Mastodon context endpoint
/api/v1/statuses/115716795916671285/context, which returns the descendants of
that status as JSON; the quoted sentences are taken verbatim from that response.
