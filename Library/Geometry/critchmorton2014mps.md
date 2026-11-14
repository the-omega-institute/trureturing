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

`OpenBoundaryMPSDensityRecovery.observable_chart_phase_recovery` supplies a conditional bridge: if some $t=Q_3(\psi)v$ lies in the existing coherent chart and the corresponding reconstructed complex linear transfer is injective, every actual free-boundary competitor with the same raw prefix density is a unit phase multiple of $\psi$. Its proof reuses the original three-site gauge reconstruction, without regularity assumptions on the competitor. Nonempty dense intrinsic real-algebraic genericity at every length and generic two-site nonidentifiability remain obligations; this conditional result does not resolve Conjecture 9. It asserts algebraic identifiability, with no positive recovery inverse, stability, dynamics or thermodynamic consequence.

## Verified locator

- DOI: https://doi.org/10.3842/SIGMA.2014.095
- Source: https://arxiv.org/abs/1210.2812v4
