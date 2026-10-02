---
bibkey: andreadakis2024scrambling
authors: Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi
year: 2024
title: "Long-time Quantum Scrambling and Generalized Tensor Product Structures"
doi: 10.1103/PhysRevA.109.052424
url: https://arxiv.org/abs/2312.13386v2
claim: "For an algebra A = direct sum over J = 1..d_Z of 1_{n_J} tensor L(C^{d_J}) on a space of dimension d = sum_J n_J d_J, Proposition 1 (ii) gives the long-time average of the A-OTOC of a Hamiltonian satisfying the non-resonance condition as 1 - (1/d) sum over X in {A, A'} of Tr(R^(0),X R^(1),X') - (1/2) Tr(R_D^(0),X R_D^(1),X'), with R^(0),X_lk = ||P_X(|phi_k><phi_l|)||_2^2 and R^(1),X_kl = <P_X(Pi_k), P_X(Pi_l)> for the eigenbasis phi_k. Proposition 2 proves that the product eigenbasis minimizes it over Hamiltonians that are block diagonal in the sectors, with minimum 1 - (sum_J d_J + sum_J n_J - d_Z)/d, and over all such Hamiltonians when d_Z = 1. The Conjecture of Section IV states that this value is the minimum over the whole family of isomorphic algebras, attained by the algebra whose distinguished basis is the eigenbasis."
strata_touched:
  - D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum
license: citation-only
triage: anchor
---

# Long-time Quantum Scrambling and Generalized Tensor Product Structures

Faidon Andreadakis, Emanuel Dallas, Paolo Zanardi, Phys. Rev. A 109,
052424 (2024), arXiv:2312.13386v2 (quant-ph). Quotations are from the
arXiv v2 source, with the source's macros `\mathds`, `\Tr`, `\ket`, `\bra`
and `\cref` kept as printed.

The sector structure (Eqs. (2) and (3)):

> $\mathcal{H} = \bigoplus_{J=1}^{d_Z} \mathcal{H}_J, \quad \mathcal{H}_J \cong \mathbb{C}^{n_J} \otimes \mathbb{C}^{d_J}.$

and

> $\mathcal{A} \cong \bigoplus_{J=1}^{d_Z} \mathbb{I}_{n_J}\otimes \mathcal{L}(\mathbb{C}^{d_J}), \quad \mathcal{A}' \cong \bigoplus_{J=1}^{d_Z} \mathcal{L}(\mathbb{C}^{n_J})\otimes\mathbb{I}_{d_J}.$

The projections (Section II):

> In terms of \cref{structure_A}, we have $\mathbb{P}_\mathcal{A} (\cdot )=\oplus_J \frac{\mathds{1}_{n_J}}{n_J} \otimes \Tr_{n_J}(\cdot )$ and, similarly, $\mathbb{P}_{\mathcal{A}^\prime} (\cdot )=\oplus_J \Tr_{d_J}(\cdot )\otimes \frac{\mathds{1}_{d_J}}{d_J}$.

Proposition 1 (ii), Eq. (6), with the line break of the source display
removed:

> $\overline{G_{\mathcal{A}}(\mathcal{U}_t)}^{NRC} = 1-\frac{1}{d}\left(\sum_{\mathcal{X}=\{\mathcal{A},\mathcal{A}^\prime\}}\Tr( R^{(0),\mathcal{X}}R^{(1),\mathcal{X}^\prime} ) - \right. \left. -\frac{1}{2}\Tr( R_D^{(0),\mathcal{X}}R_D^{(1),\mathcal{X}^\prime} )\right),$

> where, for algebra $\mathcal{X}$, we define $R_{lk}^{(0),\mathcal{X}} \coloneqq \left\lVert \mathbb{P}_{\mathcal{X}}\left(\ket{\phi_k}\bra{\phi_l} \right) \right\rVert_2^2$, $R_{kl}^{(1),\mathcal{X}} \coloneqq  \left\langle\mathbb{P}_{\mathcal{X}}\left(\Pi_k\right),  \mathbb{P}_{\mathcal{X}}\left(\Pi_l\right)\right\rangle$, and for matrix $M$, $M_D \coloneqq diag(M)$.

The display prints a minus sign at the end of its first line and another
at the start of its second. Read with a single minus sign, Eq. (6) at the
product basis equals the minimum of Proposition 2, Eq. (8); with a plus
sign it would lie below that minimum by $2d_\mathcal{Z}/d$.

The duality (Section IV):

> Note that, in general, for \cref{def_aotoc}, $G_\mathcal{A}(\mathcal{W}\,\mathcal{U}_t \, \mathcal{W}^\dagger)=G_{\mathcal{W}^\dagger(\mathcal{A})}(\mathcal{U}_t )$, where $\mathcal{W}$ is some unitary channel. This means that optimizing over unitary families of Hamiltonians is dual to optimizing over unitary families of algebras.

The Conjecture (Section IV, unnumbered):

> Let $H$ be an NRC Hamiltonian and $\mathcal{A}_f$ be the equivalence class of isomorphic algebras of the form $\mathcal{A}\cong \oplus_{J=1}^{d_\mathcal{Z}} \mathds{1}_{n_J} \otimes \mathcal{L}(\mathbb{C}^{d_J} )$. Then, the algebra corresponding to a gTPS (\cref{structure_H}) for which the Hamiltonian eigenstates have the form $\{\ket{\psi_J}\otimes\ket{\phi_J} \, \vert \, J=1,\dots d_\mathcal{Z}; \, \psi_J = 1,\dots, n_J; \, \phi_J = 1,\dots , d_J \}$ minimizes the $\mathcal{A}$-OTOC LTA over the family of isomorphic algebras. The minimum value is
> $\overline{G_{\mathcal{A}}}^{NRC}_{min}=1-\frac{1}{d} \left( \sum_J d_J + \sum_J n_J - d_\mathcal{Z} \right).$

Section IV A (numerical evidence):

> We make use of the algebra-Hamiltonian duality of the NRC LTA by fixing an algebra $\mathcal{A}$ and searching over the space of Hamiltonians for a violation of the conjecture. As seen in \cref{NRC}, the NRC LTA depends only on the Hamiltonian eigenbasis, which can be represented by a unitary matrix with eigenstates as the columns.

The encoding fixes $\mathcal{A}$ in its distinguished basis, indexes
$\mathbb{C}^d$ by the pairs $(J,(a,b))$ with $a<n_J$, $b<d_J$, takes the
eigenbasis to be the columns of a unitary $U$, and reads the minimum as the
least element of the values of Eq. (6) over the unitary group; the number
of sectors $d_\mathcal{Z}$ is written $r$.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.109.052424 (Phys. Rev. A 109,
  052424, 2024).
- URL: https://arxiv.org/abs/2312.13386v2 (v2, 2024-01-31, the latest
  version; source `main_revised.tex`, md5
  `f0749ffbb93cd5151d595e05150e95ec`): Eqs. (2)–(3) (l. 303–309), the
  projections (l. 311), Proposition 1 (ii) (l. 353–358), the duality
  (l. 406), Proposition 2 (l. 407–419), the Conjecture (l. 425–430) and
  Section IV A (l. 547–549). The conjecture environment is unnumbered; the
  equations are numbered in one sequence, so Eq. (6) is `\label{NRC}`.
