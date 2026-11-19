---
bibkey: omega2026starformingcertificates
authors: "The Omega Institute repository contributors (the note has no named byline)"
year: 2026
title: "An elementary global certificate bound for 2-star-forming sets"
doi: null
url: https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md
claim: "High-degree deletion certificates are disjoint in every finite simple graph; SF_2 is at most floor((vertex count + beta_2)/2). The six-vertex double star has beta_2=SF_2=4<5=psi_sq."
strata_touched:
  - D5/S3/Combinatorics/Graph/StarForming/CertificateBound
  - D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation
license: citation-only
triage: anchor
---

# Global certificates and the six-vertex double star

## Verified locator

URL: https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md

The complete public source at this exact revision has 80 lines and 4001 bytes,
SHA256 `37d8b0c215194148f736cc305c65d7002cfa2d04ee67327847b937029df345a8`.
The intake supplied an exact GitHub byte comparison. The supplied bytes were
read in full and the SHA256 was independently recomputed on 3 November 2026.
The note has no named byline; the repository owner is not asserted to be an
individual author.

## Exact scope and proof

For every finite simple graph and every inclusion-minimal two-star-forming
set S, let H consist of selected vertices with at least two neighbours in S.
Each vertex of H has an outside deletion certificate. A shared certificate
for distinct s,t would force a path through x to have vertices x,s,t; a
second selected neighbour of the center produces a path avoiding the other
deleted vertex. Thus certificate sets are pairwise disjoint, H injects into
the complement of S, and S minus H is a dissociation set. Consequently
2|S| is at most |V|+beta_2, and SF_2 is at most floor((|V|+beta_2)/2).
No bipartite, triangle-free, nonempty or induced-path hypothesis is present.

The source's second conclusion concerns the double star with adjacent
centers u,v and two leaves at each center, on exactly six vertices.
Its parameters are beta_2=SF_2=4<5=psi_sq. Four leaves attain both set
parameters. Every five-set contains a star-forming four-set. Coloring the
centers together and the leaves separately attains five colors; six colors
force a full injective coloring and fail the closed-neighborhood majority
at a center. The graph is bipartite and triangle-free, so neither larger
graph class admits the proposed universal comparison psi_sq<=SF_2.

## Attribution and limits

The proof and the double-star conclusion are received from the fixed public
note, rather than claimed as new discoveries. The note attributes the known
general comparison beta_2<=SF_2 to Chellali and Favaron (2009). Certificate
injection does not prove that exchanging selected vertices for certificates
preserves dissociation. Neither the rectangular-grid comparison nor a
universal five-sixths theorem is asserted. The note's finite enumeration
through five vertices is supplementary evidence, not its all-graph proof.
Worldwide novelty and priority are not claimed.
