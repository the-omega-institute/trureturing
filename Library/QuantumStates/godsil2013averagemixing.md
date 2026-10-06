---
bibkey: godsil2013averagemixing
authors: Chris Godsil
year: 2013
title: "Average mixing of continuous quantum walks"
doi: 10.1016/j.jcta.2013.05.006
url: https://arxiv.org/abs/1103.2578v3
claim: "Section 11, Question 1 asks whether the discriminant D of the adjacency minimal polynomial always makes D times the average mixing matrix integral. Lemma 1.1 gives the spectral Schur-square formula; Lemma 3.1 proves the D squared bound."
strata_touched:
  - D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality
license: citation-only
triage: anchor
---

# Average mixing of continuous quantum walks

Chris Godsil, arXiv:1103.2578v3; *Journal of Combinatorial Theory,
Series A* 120 (2013), 1649–1662,
[doi:10.1016/j.jcta.2013.05.006](https://doi.org/10.1016/j.jcta.2013.05.006).
Page numbers below refer to the arXiv v3 PDF.

Section 11, Question 1 (page 20) asks:

> Is it true that if $D$ is the discriminant of the minimal polynomial of $X$, then $D\widehat{M}_X$ is an integer matrix?

The minimal polynomial of the graph means the minimal polynomial of its
adjacency matrix over the rationals. Section 1 (page 2) specifies the
spectral projections:

> where $\theta_r$ runs over the distinct eigenvalues of $A$ and $E_r$ is the matrix representing orthogonal projection onto the eigenspace belonging to $\theta_r$.

Lemma 1.1 (page 3) states:

> If $A = \sum_r \theta_r E_r$ is the spectral decomposition of $S = A(X)$, then $\widehat{M}_X = \sum_r E_r^{\circ 2}$.

Here $\circ$ is the Schur (entrywise) product and $E_r^{\circ 2}=E_r\circ E_r$.
This is the spectral expression used by the `avgMixing` definition
in `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.lean`.

Lemma 3.1 (page 5) states:

> If $D$ is the discriminant of the minimal polynomial of $A$, then $D^2\widehat{M}_X$ is an integer matrix.

Question 1 asks for the stronger factor $D$. Questions 2 and 3 of
section 11 concern an algorithm over the rationals and the graphs whose
average mixing matrix is a linear combination of $I$ and $J$.

## Verified locator

DOI: https://doi.org/10.1016/j.jcta.2013.05.006.
Source version: https://arxiv.org/abs/1103.2578v3.
The quoted statements occur on PDF pages 3 (Lemma 1.1), 5 (Lemma 3.1)
and 20 (section 11, Question 1).
