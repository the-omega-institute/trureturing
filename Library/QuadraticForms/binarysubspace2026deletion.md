---
bibkey: binarysubspace2026deletion
authors: Public binary-subspace-orthogonality research workspace; individual derivation attribution unspecified
year: 2026
title: "Degree and list-color deletion for binary subspace orthogonality"
doi: null
url: https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/manuscript/sections/higher-dimensions.tex
claim: "Exact subspace degrees give a sufficient color-preserving reversible deletion rule in every dimension."
strata_touched:
  - D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion
license: citation-only; no unified research-material reuse license selected
triage: anchor
---

# Degree and reversible deletion

The pinned manuscript section `manuscript/sections/higher-dimensions.tex`
has SHA256 `0966718cb9a5c3f99ea85bf291f0c5973a2f4d30a4b9847ada554cdeb9dca6cb`.
The same revision's `notes/subspace-retraction.md`, SHA256
`a705c479d15181016a7420a92fee7d4bf5ea34e35e2af12ddc66733ddacdfdac`,
supplies the earlier degree/list discussion. The complete received scientific
conclusion identifies these as O8. The workspace credits Haobo Ma, Reza Nikandish
and Wenlin Zhang; this does not assign an individual author to this derivation.

Vertices are all nonzero submodules of the binary coordinate space. Every
neighbor of U is a nonzero submodule of U-perp, except U itself when U is
pairwise totally isotropic. The formal proof constructs the map/comap bijection
and derives the exact cardinality from nondegeneracy and dimension. Its count
N is the existing full submodule-lattice cardinality; this module does not claim
the separate Gaussian-binomial counting bridge.

For every palette size k, delete any finite set of vertices satisfying
N(n-dim U)<k. Every coloring of the retained induced graph extends without
changing any retained color. This includes a prescribed coloring of any fixed
clique that is retained. The proof restores vertices one by one and chooses a
color outside the image of their colored neighbors. It is independently written
Lean, without copied source code, enumeration, or an assumed coloring.

The historical n7 k16 preprocessing, clause/variable counts and propagation
counts are attributed reports, not newly reproduced computations. Later written
obstructions exclude 16, 17 and 18 colors. The exact n7 value and the later
19-color exclusion computations remain open/paused as received. No historical
palette is asserted to apply to a different k.

The research workspace's `RIGHTS.md` at this revision has SHA256
`bad872397d230fdb2460961682b36cc773c3a871411c63f032f4b21fa7b0b3e3`
and leaves a unified research-material license unselected. This citation and
independent formal proof make no publication, priority, rights or author-order
decision. The separately licensed clique formalization is reused at its actual
scope.

## Verified locator

URL: https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/manuscript/sections/higher-dimensions.tex

At commit `9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce`, the declared file's
SHA256 matches `0966718cb9a5c3f99ea85bf291f0c5973a2f4d30a4b9847ada554cdeb9dca6cb`.
Proposition `prop:dimension-deletion` and its proof, lines 17–32, give the
degree-versus-list deletion criterion with a fixed clique and restoration in
reverse deletion order. The following dimension-seven preprocessing paragraph
is a separate finite report, with the reproduction boundary stated above.
This fixed source locator preserves the received O8 version and its unresolved
research-material licensing and individual derivation attribution.
