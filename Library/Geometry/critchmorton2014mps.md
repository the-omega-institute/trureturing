---
bibkey: critchmorton2014mps
authors: Critch, Andrew; Morton, Jason
year: 2014
title: "Algebraic geometry of matrix product states"
doi: 10.3842/SIGMA.2014.095
url: "https://arxiv.org/abs/1210.2812v4"
claim: "The paper studies the varieties of translation-invariant matrix product states with periodic and open boundary conditions, gives defining equations in small cases (among them the quartic hypersurface of open-boundary binary bond-dimension-two MPS on three sites), and states identifiability conjectures, including that each improper marginalization of open-boundary 2x2 binary MPS to three consecutive sites is a birational equivalence (Conjecture 8), and the corresponding three-site reduced-density phase recovery with a no-fewer clause (Conjecture 9)."
strata_touched:
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality
license: citation-only
triage: anchor
---

# Critch and Morton, Algebraic geometry of matrix product states

A. Critch and J. Morton, SIGMA 10 (2014), 095, DOI 10.3842/SIGMA.2014.095; arXiv:1210.2812v4 (10 September 2014). Quotations are from the arXiv v4 TeX source `sigma14-095.tex`; the author list is from the arXiv metadata.

With open boundary conditions the state is $\Psi=\sum_{i_1,\dots,i_N}b_0^TA_{i_1}\cdots A_{i_N}b_1|i_1\dots i_N\rangle$ for boundary vectors $b_0,b_1\in\mathbb C^D$ and $D\times D$ matrices $A_0,\dots,A_{d-1}$; $\mathrm{OB}(D,d,N)$ is the set of such states and $\overline{\mathrm{OB}}(D,d,N)$ its Zariski closure in $\mathbb C^{d^N}$ (Section 3, l. 344–364). Theorem 7 (l. 378–403) shows that $\overline{\mathrm{OB}}(2,2,3)$ is a quartic hypersurface in $\mathbb C^8$. The improper marginalization maps sum all indices outside three consecutive sites (l. 420–428), and the paper conjectures (l. 430–434):

> For $N\geq 4$, a~generic~$N$-qubit state can be recovered from its improper margina\-li\-zation to any three consecutive states.
> That is, each improper marginalization map $\overline\OB(2,2,N)\to\overline\OB(2,2,3)$ is
> a~birational equivalence of varieties.

Conjecture 9 concerns an actual Hermitian reduced density operator, rather than the coherent sum above:

> A generic N-qubit (D=d=2) translation invariant matrix product state Ψ with open boundary conditions is determined up to phase by a reduced density operator which traces out all but a chain of three adjacent states, but no fewer.

The displayed map immediately following it uses the prefix entries
$Q_k(\psi)_{u,v}=\sum_b\psi_{ub}\overline{\psi_{vb}}$.
On the unnormalized affine cone this is the raw partial trace, retaining the squared-norm scale. A normalized reading must normalize both states. The prefix interpretation does not itself establish a theorem for every interior window.

`OpenBoundaryMPSDensityRecovery.observable_chart_phase_recovery` supplies a conditional bridge: if some $t=Q_3(\psi)v$ lies in the existing coherent chart and the corresponding reconstructed complex linear transfer is injective, every actual free-boundary competitor with the same raw prefix density is a unit phase multiple of $\psi$. Its proof reuses the original three-site gauge reconstruction, without regularity assumptions on the competitor. Dense intrinsic real-algebraic genericity at every length remains an obligation; this conditional result does not resolve Conjecture 9. It asserts algebraic identifiability, with no positive recovery inverse, stability, dynamics or thermodynamic consequence.


`OpenBoundaryMPSTwoSiteMinimality` proves a local no-fewer result for every source length $N=3+m$ with $m\ge1$. Its canonical source has thirteen real coordinates, fixes the right boundary's first coordinate to be positive real, and retains the raw affine amplitude scale. The set `canonicalChart m` additionally requires the coherent triple chart, invertibility of $S=A_0+A_1$, and invertibility of the fixed leading $00,01$ principal block of $Q_2$. `canonicalChart_nonempty` proves this set nonempty uniformly in $m$; `isOpen_canonicalChart` proves it open. `open_subchart_collision` states that every nonempty open subset of this canonical chart has two actual free-boundary matrix-and-boundary states in its image with identical **entire** raw $Q_2$ and no unit phase relating them. Its Q2 complement has length $1+m$, while the coherent triple complement has length $m$.

The proof combines the real C1 dimension obstruction with the actual amplitude-column factorization through a two-dimensional bond. The Gram is Hermitian of rank at most two, and fixed-block Schur completion upgrades twelve-real-coordinate record equality to full density equality. `phase_rigidity` uses the existing coherent inverse and invertible $S^m$ to identify all canonical parameters from phase-equal full states. The canonical-core inverse argument is attributed to Haobo Ma and Wenlin Zhang, *Proof of Critch–Morton Conjecture 8* (3 November 2026), licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); it is reused C8 mathematics, rather than claimed as new C9 content.

The uniform witness starts from $A_0=\left(\begin{smallmatrix}1&2\\3&4\end{smallmatrix}\right)$, $A_1=\left(\begin{smallmatrix}5&6\\7&8\end{smallmatrix}\right)$, $l=(1,0)$ and $r=(1,2)^T$. An exact full-length gauge gives canonical $l=(-3,1)$, $A_0=\left(\begin{smallmatrix}1&1/2\\4&3/2\end{smallmatrix}\right)$, $A_1=\left(\begin{smallmatrix}-1/2&2\\-3/2&7\end{smallmatrix}\right)$, and $r_N=2^{N-1}(5,17)^T$. The original positive sum matrix preserves positive coherent boundaries, on which the exact chart factors do not vanish. The original tail Gram is positive definite after every positive iterate, and the fixed prefix row pair has determinant $-36$, so the fixed density block stays invertible. The canonical $\det S=-2$ is distinct from a transfer-operator determinant.

This parameter-open result does not establish a dense intrinsic real-algebraic open locus in the actual state image, its descent to phase classes, or phase saturation of arbitrary open state loci. Those are separate obligations for full C9 PREFIX generic minimality. No interior-window, normalized-state, dynamical or thermodynamic conclusion is inferred.

## Verified locator

- DOI: https://doi.org/10.3842/SIGMA.2014.095
- Source: https://arxiv.org/abs/1210.2812v4
