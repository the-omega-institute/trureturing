---
slug: andreadakis-2024-algebra-otoc-long-time-minimum
bibkey: andreadakis2024scrambling
doi: 10.1103/PhysRevA.109.052424
url: https://arxiv.org/abs/2312.13386v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.result
---

# The minimum of the long-time algebra OTOC

## Problem

F. Andreadakis, E. Dallas, P. Zanardi, *Long-time Quantum Scrambling and
Generalized Tensor Product Structures*, Phys. Rev. A 109, 052424 (2024),
arXiv:2312.13386v2, the Conjecture of Section IV:

> Let $H$ be an NRC Hamiltonian and $\mathcal{A}_f$ be the equivalence class of isomorphic algebras of the form $\mathcal{A}\cong \oplus_{J=1}^{d_\mathcal{Z}} \mathds{1}_{n_J} \otimes \mathcal{L}(\mathbb{C}^{d_J} )$. Then, the algebra corresponding to a gTPS (\cref{structure_H}) for which the Hamiltonian eigenstates have the form $\{\ket{\psi_J}\otimes\ket{\phi_J} \, \vert \, J=1,\dots d_\mathcal{Z}; \, \psi_J = 1,\dots, n_J; \, \phi_J = 1,\dots , d_J \}$ minimizes the $\mathcal{A}$-OTOC LTA over the family of isomorphic algebras. The minimum value is $\overline{G_{\mathcal{A}}}^{NRC}_{min}=1-\frac{1}{d} \left( \sum_J d_J + \sum_J n_J - d_\mathcal{Z} \right).$

The long-time average under the non-resonance condition (NRC) is Eq. (6)
(Proposition 1 (ii)): for the eigenbasis $\{\phi_k\}$ of $H$ and
$\Pi_k=|\phi_k\rangle\langle\phi_k|$,
$$\overline{G}^{NRC}=1-\frac1d\sum_{\mathcal X\in\{\mathcal A,\mathcal A'\}}
\Big(\operatorname{Tr}(R^{(0),\mathcal X}R^{(1),\mathcal X'})-\tfrac12
\operatorname{Tr}(R^{(0),\mathcal X}_DR^{(1),\mathcal X'}_D)\Big),$$
with $R^{(0),\mathcal X}_{lk}=\|\mathbb P_{\mathcal X}(|\phi_k\rangle
\langle\phi_l|)\|_2^2$, $R^{(1),\mathcal X}_{kl}=\langle\mathbb
P_{\mathcal X}(\Pi_k),\mathbb P_{\mathcal X}(\Pi_l)\rangle$,
$\mathbb P_{\mathcal A}=\oplus_J\frac{\mathbb 1_{n_J}}{n_J}\otimes
\operatorname{Tr}_{n_J}$ and $\mathbb P_{\mathcal A'}=\oplus_J
\operatorname{Tr}_{d_J}\otimes\frac{\mathbb 1_{d_J}}{d_J}$. The paper
proves the minimum for Hamiltonians that are block diagonal in the sectors,
and for $d_\mathcal Z=1$ over all NRC Hamiltonians (Proposition 2); its
Section IV A reports numerical evidence up to $d=40$.

## Motivation

The $\mathcal A$-OTOC measures how fast a unitary evolution scrambles
information between a subalgebra of observables and its commutant, for
generalized tensor product structures that include superselection sectors
and quantum reference frames. The conjecture identifies the least long-time
scrambling over all non-resonant Hamiltonians of a given algebra class, and
says it is achieved exactly by eigenstates without coherence across sectors
and without entanglement inside them. The frozen declaration
`D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.result` proves it.

## Gap

Issue #12247 classifies the conjecture as Tier 1 and records the checks
made before any Lean:

- arXiv:2312.13386 has versions v1 and v2, and v2 and the published
  version state the conjecture;
- the citing works found (arXiv:2509.13519, arXiv:2506.22218, a book
  chapter) and later work of the same group (arXiv:2510.06389, the
  bipartite case; arXiv:2606.29137, the $\mathbb Z_2$-symmetric case with
  $n_J=1$) do not prove the general mixed-block statement;
- an adversarial check of later papers of the group and of equivalent
  formulations (conditional expectations, Wedderburn blocks, noiseless
  subsystems, operator-space entanglement, coherence-generating power,
  frame potentials) found no proof or refutation.

These are orchestrator-reported readings and seat-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty. Step 2 of the Route extends the bipartite reduced-state Gram
method of Styliaris–Anand–Zanardi, PRL 126, 030601 (2021), Prop. 4, and
Proposition 2 of the paper; the new parts are the bound of the cross kernels
by the identity for an arbitrary eigenbasis, which mixes the sectors, and
the per-sector inequalities of steps 3–4.

## Route

Fix the algebra in its distinguished basis and let the columns $\phi_k$ of
a unitary $U$ be the eigenbasis (every orthonormal basis is the eigenbasis
of an NRC Hamiltonian, and by the duality of Section IV this is the family
of the conjecture). Write $C_{Jk}$ for the $n_J\times d_J$ block of
$\phi_k$, $q_{Jk}=\|C_{Jk}\|_F^2$, $p_{Jk}=\operatorname{tr}
[(C_{Jk}C_{Jk}^\dagger)^2]$, and $F=D(1-\overline G^{NRC})$ with
$D=\sum_Jn_Jd_J$.

1. $R^{(1),\mathcal A'}_{kl}=\sum_J\operatorname{tr}(\operatorname{Tr}_{d_J}
   \Pi_k\operatorname{Tr}_{d_J}\Pi_l)/d_J$. For coefficients $c_k$ the
   quadratic form $\sum_{kl}\bar c_kc_lR^{(1),\mathcal A'}_{kl}$ equals
   $\sum_J\|\operatorname{Tr}_{d_J}Y_J\|_F^2/d_J$ with
   $Y=U\operatorname{diag}(c)U^\dagger$; by Cauchy–Schwarz in each block it
   is at most $\|Y\|_F^2=\sum_k|c_k|^2$. So $R^{(1),\mathcal A'}\le I$, and
   likewise $R^{(1),\mathcal A}\le I$.
2. $R^{(0),\mathcal A}$ and $R^{(0),\mathcal A'}$ are sums of Gram
   matrices, so $\operatorname{Tr}(R^{(0),\mathcal X}R^{(1),\mathcal X'})
   \le\operatorname{Tr}R^{(0),\mathcal X}$; their diagonal entries are
   $\sum_Jp_{Jk}/n_J$ and $\sum_Jp_{Jk}/d_J$, at most
   $r_k=\sum_Jq_{Jk}^2/n_J\le1$ and $w_k=\sum_Jq_{Jk}^2/d_J\le1$.
3. $x+y-xy$ is increasing on $[0,1]^2$ and $r_kw_k\ge\sum_J
   q_{Jk}^4/(n_Jd_J)$, so with $\sum_Jq_{Jk}=1$ and $\sum_kq_{Jk}=n_Jd_J$,
   $F\le\sum_J\big((n_J+d_J)\sum_kq_{Jk}^2-\sum_kq_{Jk}^4\big)/(n_Jd_J)$.
4. For $M=n_J+d_J\ge3$, $(M-1)x-Mx^2+x^4=x(1-x)(M-1-x-x^2)\ge0$ on
   $[0,1]$, so the $J$ term is at most $n_J+d_J-1$; for $n_J=d_J=1$,
   $f(x)=2x^2-x^4$ satisfies $f(a+b)-f(a)-f(b)=ab(4-4(a+b)^2+2ab)\ge0$ for
   $a,b\ge0$, $a+b\le1$, so $\sum_kf(q_{Jk})\le f(1)=1$.
5. Hence $F\le\sum_J(n_J+d_J-1)$, the conjectured bound. At $U=1$ the
   kernels are indicators of equal first (respectively second) coordinates
   within a sector, scaled by $1/n_J$ or $1/d_J$; the cross traces are
   $\sum_Jd_J$ and $\sum_Jn_J$ and both diagonal traces are $r$, so $U=1$
   attains the bound.

## Falsifier

The kernel-checked `result` states, for every number of sectors $r$ and
all $n_J,d_J\ge1$, that $1-(\sum_Jd_J+\sum_Jn_J-r)/D$ is the least element
of the values of Eq. (6) over the unitary group of $\mathbb C^D$. It reads
Eq. (6) with a single minus sign before the diagonal term (the source
display prints one at the end of its first line and one at the start of
its second); with a plus sign the value at the product basis would lie
below the paper's own minimum of Proposition 2 by $2d_\mathcal Z/d$. It
fixes the sector type $(n_J,d_J)_J$, not only the abstract algebra:
$(I_2\otimes M_1)\oplus(I_2\otimes M_2)$ and $(I_4\otimes M_1)\oplus
(I_1\otimes M_2)$ are both $\mathbb C\oplus M_2$ but have minima $1/6$ and
$0$.

## Evidence

A NumPy recomputation of Eq. (6) from the definitions (Haar-random
unitaries) reproduces the conjectured value at $U=1$ for 9 sector types
with $D\le6$, and 300 random $U$ per type never go below it (worst margin
$-2.7\times10^{-15}$); for 15 random $U$ over 5 types the identity of
step 1 holds to $10^{-8}$ and the spectrum of $R^{(1),\mathcal A'}$ lies in
$[0,1]$ (issue #12247). An orthonormal basis of product vectors need not
attain the minimum: for $n=d=2$, $|00\rangle,|01\rangle,|1{+}\rangle,
|1{-}\rangle$ gives $3/8>1/4$.

The canonical source is
`D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.lean`. Its public
declarations are `Idx`, `projA`, `projAc`, `ketBra`, `R0`, `R1`, `term`,
`lta`, `claim` and `result`; the partial traces are the frozen
`D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft`
and `partialTraceRight`. The frozen module state has statement identity
`sha256:22574a5bd686430954b57d7948d7b3ac30ae6255c4193aeadfb5af4dc137a667`. The
result declaration has statement identity
`sha256:bfe216996a3a9c45ed2de65c8aa42644a70dae6df1ea0347403bccf4a4b6d32d`. The
Freeze event is
`sha256:365bcb825aa4ba33287220c61a49d7880c1c730157666e41f0d7d1462a636e59`; its
project-level frozen prerequisite is the Freeze event of
`D5/S3/Quantum/Information/PartialTraceMutualInformation`. The proof uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 published conjecture; resolution `Proved` by
`D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution` (issue
#12247). Utility kind `none` (a theorem about every sector type and every
eigenbasis).

### What the settlement shows

- **Proved by `result`:** for every sector type and every eigenbasis,
  $\overline G^{NRC}\ge1-(\sum_Jd_J+\sum_Jn_J-d_\mathcal Z)/d$, with
  equality for the distinguished product basis.
- **Proved inside the proof of `result`:** both cross kernels
  $R^{(1),\mathcal A}$ and $R^{(1),\mathcal A'}$ are bounded by the
  identity as quadratic forms, for every orthonormal eigenbasis; each
  cross trace $\operatorname{Tr}(R^{(0),\mathcal X}R^{(1),\mathcal X'})$
  is at most the trace of $R^{(0),\mathcal X}$; and
  $D(1-\overline G^{NRC})\le\sum_J\big((n_J+d_J)\sum_kq_{Jk}^2-
  \sum_kq_{Jk}^4\big)/(n_Jd_J)$ in terms of the sector weights alone.
- **Mechanism (read off the proof; not stated in Lean):** the bound is
  controlled by the sector weights $q_{Jk}$. The inequality of step 4 is
  strict for $0<q_{Jk}<1$ when $n_J+d_J\ge3$, and the superadditivity gap
  $ab(4-4(a+b)^2+2ab)$ is positive for $a,b>0$ with $a+b=1$, so weight
  spread over two sectors loses; within a sector the purity bound
  $p_{Jk}\le q_{Jk}^2$ is an equality only for product vectors. This is
  the coherence-and-entanglement picture the paper gives for the
  conjecture.
- **Follows from it (not stated in Lean):** when every $n_J=1$ (or every
  $d_J=1$) the minimum is $0$, recovering the abelian case of the paper;
  for $r=1$ it is Proposition 2 (ii).
- **Open here:** the characterization of all minimizers (the argument
  above forces $q_{Jk}\in\{0,1\}$ for sectors with $n_J+d_J\ge3$, but
  equality cases with $n_J=d_J=1$ sectors and in steps 1–2 were not
  analyzed), the analogous minimum under the weaker NRC$^+$ condition of
  Eq. (5), and finite-time versions.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority or absence of an
independent answer; the 2025 dissertation of F. Andreadakis was not read
(the USC repository returned HTTP 403 and no public full text was found).
The Lean kernel verifies the encoded statement and its axiom closure; its
correspondence to the paper, including the reading of the family of
isomorphic algebras as the unitary group acting on the eigenbasis and the
single minus sign of Eq. (6), is checked by reading the source and the
definitions.
