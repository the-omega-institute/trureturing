---
bibkey: radsararanando2026apollonian
authors: Rad Sarar Anando
year: 2026
title: "Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?"
doi: null
url: https://mathoverflow.net/questions/516405
claim: "The second largest ordinary adjacency eigenvalue of the deterministic inner-face Apollonian stages, divided by 2^(m/2), converges to sqrt(2)."
strata_touched:
  - D5/S3/Combinatorics/Apollonian/InnerFaceStages
  - D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds
  - D5/S3/Combinatorics/Apollonian/CutoffGramLimit
  - D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum
  - D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit
  - D5/S3/SpectralTopology/RectangularDilation
license: CC-BY-SA-4.0
triage: anchor
---

## Locator

Rad Sarar Anando, [MathOverflow question 516405](https://mathoverflow.net/questions/516405), revision 1,
GUID `8C9D6CD5-E3A3-4B25-BDB6-FF5A9A3D3A2B`.
The locator covers the inner-face graph construction and the stated second
ordinary-adjacency eigenvalue limit in that revision. The source's numerical
observations, preliminary bounds and question about other leading eigenvalues
are not additional premises or results attributed to the formal theorem.
The quoted construction and question, and their adapted mathematical exposition,
are attributed under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
The adaptations use explicit finite vertex and face indices and separate
the graph construction from the proposed spectral limit.

## Exact construction and question

> Let $G_0=K_4$ with outer triangle $abc$ and central vertex $o$.
> $G_m$ is obtained from $G_{m-1}$ by inserting a new vertex into every
> inner triangular face, joined to its three corners. The outer face
> $abc$ is never subdivided.

The graph is finite, simple and unweighted. Its ordinary adjacency eigenvalues
are listed in nonincreasing order, with multiplicity. The question is

$$
\lim_{m\to\infty}\frac{\theta_2(G_m)}{2^{m/2}}=\sqrt2.
$$

The source's numerical observations and preliminary spectral bounds are not
premises of the graph construction or of the combinatorial laws.
The larger question about other leading eigenvalues is outside this target.

## Construction correspondence

The seed indices $0,1,2,3$ denote $a,b,c,o$ respectively. The three initial
inner faces have ordered corners $(o,a,b),(o,b,c),(o,c,a)$.
At each step the vertex type is the disjoint sum of the old vertex type
and the current inner-face type. A new vertex is adjacent exactly to the
three distinct corners of its own parent face. Old adjacency is retained;
two vertices born in the same step are not adjacent.

For each parent face there are three child faces. Child $i$ replaces corner
$i$ by the parent face's new centre, retaining the other two corners.
The outer triangle is separately distinguished by its seed vertices and
is absent from the subdivision index. No closed vertex-count formula is
needed for the spectral index; four persistent seed vertices suffice.

## Reused mathematics and evidence boundary

The accepted ordinary proof in
[issue #24905](https://github.com/the-omega-institute/trureturing/issues/24905#issuecomment-6548069659)
uses exact degrees, at most two inner faces through an edge, and orientation
from newer to older endpoints. The corresponding all-stage spectral target
is tracked by [issue #24989](https://github.com/the-omega-institute/trureturing/issues/24989).
`D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit.result` proves the exact
`InnerFaceStages.limitClaim`. At fixed cutoff, the second limiting Gram weight
is two: the central seed has weight three, the outer seeds have weight two,
and all other weights are at most two. Gram convergence and the unequal-block
dilation identity give the cutoff limit. The actual adjacency remainder is
controlled by the fixed old block and the birth-oriented late block. Choosing
the cutoff and then the stage proves the stated limit along all natural
stages, with the original real-power normalization. This formalizes the accepted
ordinary argument; it is not a separate claim to an original solution.

The finite source and literature screen did not authenticate an exact competing
deterministic second-eigenvalue limit. Its unread limits include the complete
2005 and 2009 papers and independent retrieval of the 2010 paper. This is no
claim of exhaustive literature coverage, priority, or worldwide openness.
Random one-face subdivision, subdivision of all four faces of a spherical
$K_4$, normalized adjacency, and Laplacian operators have different hypotheses.
