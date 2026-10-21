---
bibkey: gutkin2013orthostochastic
authors: Eugene Gutkin
year: 2013
title: "On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices"
doi: 10.1016/j.geomphys.2013.06.009
url: https://arxiv.org/abs/1301.2537v1
claim: "The paper defines F^d-bistochastic matrices as the bistochastic matrices P with p_i^j = ||v_i^j||^2 for a matrix V of vectors in F^d satisfying its equations (1)–(2), introduces d_min(F, n) as the least d for which every bistochastic n × n matrix is F^d-bistochastic, and conjectures that 2 ≤ d_min(n) ≤ 3 for all large n when F = R."
strata_touched:
  - D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation
license: citation-only
triage: anchor
---

# On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices

Eugene Gutkin, arXiv:1301.2537v1 (2013-01-11); J. Geom. Phys. 74 (2013) 28–35. Quotations are from the v1 TeX source.

Index convention:

> The lower (resp. upper) index stands for the column (resp. row).

The two systems of equations (Lemma 1):

> \sum_{i=1}^n\langle v_j^i,v_k^i\rangle = \de(j,k).

> \sum_{i=1}^n\langle v_i^j,v_i^k\rangle = \de(j,k).

The set Iso and the map ν:

> Let $\iso(\F,n,d)$ denote the set of matrices $V\in\M(\F^d,n)$ satisfying the equivalent equations~\eqref{isom_eq},~\eqref{conjug_eq}.

> p_i^j=\langle v_i^j, v_i^j\rangle=||v_i^j||^2.

Definition 1:

> A matrix $P\in\B_n$ is {\em $(\F,n,d)$-bistochastic} ($\F^d$-bistochastic for brevity) if $P=\nu(V)$ for some $V\in\iso(\F,n,d)$.

Conjecture 1:

> Denote by $d_{\min}(n)$ the smallest value of $d$ such that the set of $d$-orthostochastic matrices coincides with $\B_n$. Then there exists $n_0$ such that for $n\ge n_0$ we have $2 \le d_{\min}(n) \le 3.$

Lemma 1 asserts that the two systems are equivalent. For d ≥ 2 they are not; Nechita, Ouyang and Szczepanek (arXiv:2310.03436) point this out.

## Verified locator

- URL: https://arxiv.org/abs/1301.2537v1 (v1, 2013-01-11; source `multi_ortho_arxiv.tex`, md5 `e445abf099401dc95ab514143f58b811`):
  - the index convention, l. 443–444;
  - Lemma 1, l. 463–500;
  - Iso and ν, l. 503–518;
  - Definition 1, l. 522–528;
  - Conjecture 1, l. 1146–1155.
- The arXiv record has only v1.
- DOI: https://doi.org/10.1016/j.geomphys.2013.06.009 (journal title with "multi-dimensional … notions"; the arXiv title reads "multi-dimesional … notion").
