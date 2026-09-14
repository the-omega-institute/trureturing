---
bibkey: wilkes2018markedtorusrecovery
authors: Gareth Wilkes
year: 2018
title: Profinite rigidity of graph manifolds, II: knots and mapping classes
arxiv: 1801.06386v2
claim: JSJ and fibration-sensitive profinite classification is already available for the stated graph-manifold class. The accompanying ordinary calculation gives explicit marked-cover homology recovery only for a single separating-twist family.
license: citation-only
triage: anchor
---

# Marked cover homology and three-dimensional torus gluing

## Primary sources and earlier-package reading scope

[1] Gareth Wilkes, *Profinite rigidity of graph manifolds, II: knots and
mapping classes*, arXiv:1801.06386v2.
https://arxiv.org/abs/1801.06386
https://arxiv.org/pdf/1801.06386

The earlier package read the primary abstract, parsed PDF Theorems 1.5, 1.6
and 5.4, the edge-gluing conventions in Section 1, and Question 5.1 with its
stated scope. This qualitative graph-manifold theory is not a new open
problem solved by the present calculation. General unmarked graph manifolds
need not all be profinitely rigid. A selected fibration and time section may
not be silently recovered from an arbitrary unmarked profinite isomorphism.
The arXiv metadata labels v2 in February 2018 while the retrieved PDF title
page also prints July 13, 2021; the earlier record did not infer a publication
timeline from that discrepancy. Its PDF screenshot requests failed; parsed
text was inspected, and successful visual inspection was not claimed.
This synchronization turn opened the abstract, not a new full-PDF review.

[2] Gareth Wilkes, *Profinite rigidity of graph manifolds and JSJ decompositions
of 3-manifolds*, arXiv:1605.08244.
https://arxiv.org/abs/1605.08244
https://arxiv.org/pdf/1605.08244

The earlier package read the primary abstract and the relevant parsed
classification statement, including Theorem 10.9. This is provenance for
JSJ pieces and gluing parameters. The argument for the specific two-piece
family is stated directly. No general JSJ or profinite-rigidity discovery
is asserted, and those PDF checks were not repeated this turn.

[3] Daniel Corey and Wanlin Li, *The Ceresa class and tropical curves of
hyperelliptic type*, Forum of Mathematics, Sigma 12 (2024), e54.
DOI 10.1017/fms.2024.36.
https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/ceresa-class-and-tropical-curves-of-hyperelliptic-type/45FB665F25690EB975E500852FA4AFCA

Primary mathematical HTML was read, especially Section 3.1 and Proposition
3.1, with the transvection formula and linearity of disjoint multitwist
increments. The retained cover-graph appendix proves its integral primitive
sublattice and graph-pairing construction. The monodromy mechanism is a
classical input, not a claimed first discovery.

[4] Roland Bacher, Pierre de la Harpe and Tatiana Nagnibeda, *The lattice of
integral flows and the lattice of integral cuts on a finite graph*, Bulletin
de la Societe Mathematique de France 125(2) (1997), 167-198.
DOI 10.24033/bsmf.2303.
https://www.numdam.org/articles/10.24033/bsmf.2303/

The earlier package read the primary metadata record. It did not claim a
full-paper visual review. The theory derives the complete-bipartite matrix
Smith form explicitly, rather than attributing it to an unread numbered result.

[5] Adam Klukowski, *Congruence subgroup property for nilpotent groups and
subsurface subgroups of Mapping Class Groups*, arXiv:2411.06867v2.
https://arxiv.org/html/2411.06867v2

Definition 3, Corollary 11 and Conjecture 13 were read again during
synchronization. The conjecture concerns a full simple-curve orbit relative
to a prescribed finite-index subgroup. A based three-manifold covering kernel,
a single-twist exponent and a surface principal outer-action kernel are
three different objects. The recovery result does not identify them.
Bounded searches do not establish exhaustive novelty or current resolution.

[6] Clay Mathematics Institute, *Poincare Conjecture*.
https://www.claymath.org/millennium/poincare-conjecture/

The earlier research read the official overview of Perelman's solved
conjecture and geometrization. The manifolds constructed here have a
fundamental-group epimorphism onto Z and contain an incompressible gluing
torus. They belong to the graph-manifold setting, outside the simply
connected sphere case. No Ricci-flow PDE estimate or physical toroidal
universe is deduced from the construction.

## Mathematical increment and scope

For M=M_(T_alpha^k), with essential separating alpha, g>=2 and nonzero k,
all pure time-cyclic covers have H1=Z^(2g+1). The selected mod-p surface-homology
cover has degree D=p^(2g). Retain a chosen fixed-point section, so the time
generator maps to zero in the deck quotient. Put G=1+D(g-1),
a=p^(2 min(h,g-h)), b=p^(2 max(h,g-h)), beta=(a-1)(b-1), and q=|k|.
The ordinary proof gives the actual covered mapping-torus homology:

Z^(2G+1-beta) + (Z/q)^((a-2)(b-2)) + (Z/qa)^(b-2)
  + (Z/qb)^(a-2) + Z/(qab).

Its torsion exponent is qD. The free rank recovers beta, then a+b=D+1-beta,
and hence the unordered separating genera. Standard JSJ data make these
parameters the unoriented homeomorphism invariants within this specified
one-twist family. This is marked finite-cover reconstruction. The selected
cover is not claimed characteristic in the whole mapping-torus group, and
no algorithm recognizing arbitrary unmarked three-manifolds follows.

A bounded-|k| corollary uses finite coefficients L=q0 D H!, where q0 is prime
larger than H and p. An actual finite quotient of the marked three-manifold
group, together with its specified deck projection, records that finite
homology. The size bound is deliberately conservative, with no optimality
or polynomial-time guarantee. Standard classification and lattice machinery
are reused; the earlier bounded search did not establish first discovery.

The later contextual probe section recovers signed k relative to an oriented
symplectic marking. This is a different task from the above unoriented
homeomorphism classification, which necessarily records only |k|. It uses
fixed simple-curve probes on the covering surface and does not assume those
probes descend to base-surface mapping classes.

## Earlier diagnostics, preserved rather than rerun

The preceding local package read dev 038ed9c326ae27cc7d4b1c900ba12eba57c2e545
and PR #7710 head 7655948d462ea33de9110a83fd4e6a1691f8d170. It supplied
Sections 40-45 for the older graph-cover appendix and new Sections 46-51 for
the three-dimensional recovery. Current synchronization retains the existing
Sections 1-39 and appends both packages before the new probe material.

The earlier computations comprised six integral cellular cases
(g,h,p)=(2,1,2), k=-3,-1,0,1,2,5, using lifted surface relations and actual
twist words. The expected Gram matrix was not their input. Additional tests
were 16 tensor Smith cases, 13200 arithmetic decoder cases and 216 bounded
finite-coefficient cases. The large grids tested decoder arithmetic rather
than further geometric covers. Higher-genus integer Smith computations were
not completed. These suites were not rerun during the current synchronization.

No Lean/lake or .NET executable is available in the current runtime. These
sections remain ordinary proofs with reproducible prior diagnostics; no new
Lean/Scribe wrapper, freeze certificate, CI edit or independent admission
review is supplied. The earlier local package could not write remotely.
Its mathematical products are now being committed to PR #7710, with the
actual write-back SHAs recorded in the PR conversation and summary.
