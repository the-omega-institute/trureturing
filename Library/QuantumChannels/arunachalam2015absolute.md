---
bibkey: arunachalam2015absolute
authors: Srinivasan Arunachalam, Nathaniel Johnston and Vincent Russo
year: 2015
title: "Is absolute separability determined by the partial transpose?"
doi: null
url: https://arxiv.org/abs/1405.5853v3
claim: "Section 7 states as open that none of the positive generalized Choi maps Φ_{b,c} of Section 5.3 detects entanglement in absolutely PPT states of M_3 ⊗ M_3."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/1405.5853v3

Published in Quantum Information and Computation 15(7–8), 694–720 (2015); the arXiv abstract page
lists the arXiv-issued DOI https://doi.org/10.48550/arXiv.1405.5853. Version 3 (22 January 2015) is
the quoted version (`v2_separability_from_spectrum.tex`). The family and its positivity region are
in Section 5.3, PDF p. 14; the light shaded region is discussed on p. 16; the open problem is in
Section 7, p. 21.

The family (p. 14):

> We now introduce an infinite family of positive maps based on two real parameters $b,c\geq 0$ that were first studied in [CKL92] (see also [CW11,CS13]). If we let $a := 2-b-c$, then these maps are defined as follows: $\Phi_{b,c}(X) := \frac{1}{2}\begin{bmatrix} ax_{11} + bx_{22} + cx_{33} & -x_{12} & -x_{13} \\ -x_{21} & cx_{11} + ax_{22} + bx_{33} & -x_{23} \\ -x_{31} & -x_{32} & bx_{11} + cx_{22} + ax_{33} \end{bmatrix}.$ Notice that the Choi map $\Phi_C$ is recovered in the $(b,c) = (1,0)$ case. Additionally, in the $(b,c) = (1,1)$ case the map has the form $\Phi_{1,1}(X) = \frac{1}{2}\big(\mathrm{Tr}(X)I - X\big)$, which is the well-known reduction map.

> It is known that $\Phi_{b,c}$ is positive but not completely positive (i.e., capable of detecting entanglement in some state) if and only if $(b,c) \neq (0,0)$, and either $b+c \leq 1$ or $bc \geq (b+c-1)^2$ (or both).

The light shaded region (p. 16):

> Theorem 3 shows analytically that all of the maps in the dark shaded region of Figure 3 are unable to detect entanglement in absolutely PPT states. It is natural to ask whether or not the same is true of the positive maps in the light shaded region. We do not have an analytic proof that this is the case, but numerical evidence suggests that it is.

The open problem (Section 7, p. 21):

> Other open problems in this work include proving that all of the generalized Choi maps $\Phi_{b,c}$ in Section 5.3 are incapable of detecting absolutely PPT entanglement (including those in the light gray region of Figure 3) …

A state $\rho\in M_m\otimes M_n$ is absolutely PPT when $(id\otimes T)(U\rho U^\dagger)\geq0$ for every
unitary $U$; a map detects entanglement in $\rho$ when $(id_3\otimes\Phi)(\rho)$ has a negative
eigenvalue. The Lean reading applies $\Phi_{b,c}$ to the second tensor factor, matching the
second-factor partial transpose of the repository's `APPT`.
