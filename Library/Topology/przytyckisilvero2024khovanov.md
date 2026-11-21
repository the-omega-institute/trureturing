---
bibkey: przytyckisilvero2024khovanov
authors: Józef H. Przytycki; Marithania Silvero
year: 2024
title: Khovanov homology, wedges of spheres and complexity
doi: 10.1007/s13398-024-01594-z
url: https://arxiv.org/abs/2305.18648v1
claim: Section 9.1 conjectures that the first nonzero framed quantum row of a link of braid index at most four has one of the graded group shapes in Corollary 1.6.
strata_touched:
  - D5/S3/Topology/FourBraidKhovanovCube
  - D5/S3/Topology/FourBraidKhovanovHomology
  - D5/S3/Topology/FourBraidKhovanovResolutions
  - D5/S3/Topology/FourBraidKhovanovCounterexample
license: citation-only
triage: anchor
---

# Khovanov homology, wedges of spheres and complexity

Corollary 1.6 allows the potential extreme framed quantum row of a four-strand
braid diagram to vanish or to have graded group $\mathbb Z$ or
$\mathbb Z[k]\oplus\mathbb Z^r[i]$ with $1\le r\le 3$ and $k\ge i$.
Section 9.1 asks for the same graded list at the first nonzero quantum row of
the link. Corollary 9.2 applies the diagram bound to a Khovanov B-adequate
four-strand presentation.

The closure of the four-strand braid with signed generator indices
$(1,2,1,1,-3,2,2,-3,2,1,2)$ has highest nonzero unreduced integral quantum
row at normalized degree $J=17$. This row has rank two in degree $I=5$
and rank one in degree $I=6$, with zero groups elsewhere. Its potential
top is at $J=21$, and the rows $J=21,19$ are acyclic over $\mathbb Z$.
The computation uses the signed resolution cube with the multiplication and
comultiplication of $\mathbb Z[X]/(X^2)$.

The braid has writhe $w=7$. With the grading conversion in Remark 2.1,
$i=w-2I$ and $j=3w-2J$, the first nonzero framed row is $j=-13$.
Its singleton lies in degree $-5$, and its rank-two group lies in degree
$-3$. The ordered summands in Corollary 1.6 put the singleton in the
greater of the two distinct framed degrees. The displayed four-strand
presentation supplies the braid index upper bound in §9.1.

The signed word was selected using the LinkInfo entry `L11n294{0,0}`
in `database-knotinfo` version 2026.11.2. The homology computation uses the
word itself. The periodic closure of its resolution slices gives the circles,
and integral elementary row and column operations certify the relevant
differential images. An independent crossing-port construction gives the
same result. The bounded citing-literature comparison found no explicit
settlement. The database supplies the braid and earlier tabulated group data.
Lipshitz and Sarkar include the link name `L11n294` in their earlier
Steenrod-square computations. Historical priority remains unverified.

- [ArXiv v1](https://arxiv.org/abs/2305.18648v1), pp. 3, 5, and 36–37.
- [Published version](https://doi.org/10.1007/s13398-024-01594-z), pp. 3, 4, and 32.
- [LinkInfo dataset distribution](https://pypi.org/project/database-knotinfo/2026.11.2/).
- [Lipshitz–Sarkar, arXiv:1204.5776v3](https://arxiv.org/abs/1204.5776v3), Table 1, p. 43.
