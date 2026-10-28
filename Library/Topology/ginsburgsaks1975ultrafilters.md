---
bibkey: ginsburgsaks1975ultrafilters
authors: John Ginsburg and Victor Saks
year: 1975
title: Some applications of ultrafilters in topology
doi: 10.2140/pjm.1975.57.403
url: https://doi.org/10.2140/pjm.1975.57.403
claim: Theorem 2.12 and its preceding construction give the classical omega1 closing-off method for the D-compact extension of a completely regular space inside its Stone-Cech compactification, for one fixed free ultrafilter D.
strata_touched:
  - D5/S3/Topology/CountablyCompact/InjectiveSelectorClosure
license: citation-only
triage: anchor
---

# Classical omega1 closing-off and its scope

The article appears in Pacific Journal of Mathematics 57 (1975), 403–418.
The method attested here is Theorem 2.12 and its preceding construction,
printed pages 407–408 (PDF pages 6–7). The construction starts with a
completely regular space X inside beta X, fixes one free ultrafilter D
on the natural numbers, and adjoins the D-limit of every sequence from
the union of earlier stages. It iterates through all countable ordinals.
Every sequence in the final union lies in one earlier stage and has its
D-limit in the next stage. The union is D-compact, and induction shows
that every D-compact subspace of beta X containing X contains it.

In the proof on printed page 407, the key bounded-stage observation is:

> it lies entirely within one Xβ

The preceding discussion identifies the construction as an analogue of
Bernstein's Example 4 and mentions Woods's independent characterization.
Those original sources are not attested by this note.

The method is background for InjectiveSelectorClosure. The paper does
not state its exact arbitrary T1 theorem with an arbitrary map q,
FreshClusterSupply, a continuum-sized admissible seed, and preservation
of q-injectivity inside Good. Both exact Lean statements remain
repository-derived; this citation acknowledges the closing-off method,
not those statements or a new-result priority claim.

Example 5.2 on printed page 413 (PDF page 12) is explicitly credited to
Frolík. It invokes the fact that countably infinite subsets of beta N
have 2^c points in their closure to obtain disjoint added sets P1 and P2
making the two extensions countably compact. It refers to the proof of
Lemma 2.9 in its reference [9]; it does not prove an independent-family
cardinal theorem on that page. This is contextual attribution, not a
second attestation of a cardinal-supply theorem. Direct primary
attestation is recorded in
[frolik1960countablycompact](frolik1960countablycompact.md): Lemma 2.8,
printed pages 333–334, gives 2^c accumulation points for an infinite
subset of beta P having no accumulation point in P, where P is separable
metrizable. Lemma 2.9, printed page 334, constructs a countably compact
R with P contained in R contained in beta P minus M and |R| at most c
whenever M is contained in beta P minus P and |M| is strictly below 2^c.
Its cardinal avoidance and omega1 closing-off are classical method
provenance alongside the fixed-D construction above. Frolík explicitly
invokes Pospíšil's cardinal theorem and credits Katětov for the simple
proof of Lemma 2.8; those credits are attested by Frolík, without an
independent reading of their originals. Neither lemma states the exact
arbitrary T1/q-injective good-set theorem.

The generic closure theorem, this classical method, and the original
Feldman–Wilce Question 1 are separate claims. The intended application
still needs free-ultrafilter cardinal supply, fresh good accumulation
points with distinct projected values, a section-dense injective seed,
the actual set Y, and the original graph endpoint. Neither this note nor
the generic theorem establishes original-problem completion, novelty,
worldwide uniqueness, or official acceptance.

## Verified locator

DOI: 10.2140/pjm.1975.57.403.
URL: https://doi.org/10.2140/pjm.1975.57.403.
Primary publisher DOI and URL: https://doi.org/10.2140/pjm.1975.57.403.
The consulted passages are Theorem 2.12 and its preceding construction,
printed pages 407–408, and Example 5.2, printed page 413.
