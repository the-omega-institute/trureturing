---
bibkey: vomende2024divisibility
authors: Frederik vom Ende
year: 2024
title: "A Sufficient Criterion for Divisibility of Quantum Channels"
doi: 10.1063/5.0231812
url: https://arxiv.org/html/2407.17103v3
claim: "Definition 1 specifies elementary channels; Proposition 1 and Theorem 1 give necessary and sufficient Kraus-space criteria. Section V asks whether their converses hold."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility
license: citation-only
triage: anchor
---

# Elementary quantum-channel division

The source is arXiv:2407.17103v3, Definition 1, Lemmas 2–3, equation (3),
Proposition 1, Theorem 1 and Section V. The journal DOI identifies the
publication; the journal text has not been checked against the arXiv version.

For orthogonal complex unit vectors $x,y$, the elementary channel has Kraus
operators

$$
K_t=I-(1-\sqrt{1-t})|x\rangle\langle x|,
\qquad L_t=\sqrt t\,|y\rangle\langle x|.
$$

The Kraus space is the complex linear span of a Kraus representation. Its
orthogonal complement uses the Hilbert–Schmidt inner product
$\langle A,B\rangle=\operatorname{tr}(A^*B)$. Proposition 1 says that
$\Phi\Psi_t^{-1}$ being completely positive for some $0<t<1$ implies
$\langle y,K_j^*Gx\rangle=0$ for every Kraus operator $K_j$ and every
$G$ in this complement. Theorem 1 proves existence of such a $t$ if the
additional conditions $\langle x,K_j^*Gx\rangle=0$ also hold. Its separate
rank-reduction conclusion has an additional hypothesis.

Section V asks:

> An open question at this point is whether our sufficient condition is also necessary, and whether our necessary condition is also sufficient.

The source Choi matrix is input-first:
$C(\Phi)_{(i,a),(j,b)}=\Phi(E_{ij})_{ab}$. This agrees with column
vectorization $\operatorname{vec}(G)_{(i,a)}=G_{ai}$; the repository's
output-first Choi supplier is related by swapping both index pairs.

## Verified locator

- DOI: https://doi.org/10.1063/5.0231812
- arXiv v3: https://arxiv.org/html/2407.17103v3
- Definition 1 and Lemma 3 define the elementary channel and its inverse;
  equation (2) gives the inverse formula and equation (3) gives the Choi
  coordinate convention used here.
- Proposition 1 and Theorem 1 state the necessary and sufficient
  Kraus-space conditions.
- Section V contains the quoted open question about whether the sufficient
  condition is necessary and whether the necessary condition is sufficient.

The arXiv v3 HTML was read at the locator above. The journal full text was
not checked because the journal endpoint returned HTTP 403; no
journal-equivalence or priority claim is made.

These are finite-dimensional channel statements. Elementary right division
alone supplies no implementation by a specified physical gate set, no local
operations protocol and no success probability or preparation cost.
