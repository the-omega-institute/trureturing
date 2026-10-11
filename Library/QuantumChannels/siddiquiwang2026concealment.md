---
bibkey: siddiquiwang2026concealment
authors: Mohd Asad Siddiqui; Zizhu Wang
year: 2026
title: "Operational Concealment of Measurement Incompatibility by Quantum Channels: Rank Loss versus Contraction"
doi: 10.48550/arXiv.2607.11762
url: https://arxiv.org/abs/2607.11762v2
claim: "For channels with a common output space, equality of adjoint kernels (restricted to Hermitian operators) implies equality of the sets of concealed POVM pairs; whether equality of adjoint kernels is also necessary for concealment-equivalence is stated as open."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation
license: citation-only
triage: anchor
---

# Siddiqui and Wang, operational concealment of measurement incompatibility

M. A. Siddiqui and Z. Wang, *Operational Concealment of Measurement Incompatibility by Quantum
Channels: Rank Loss versus Contraction*, arXiv:2607.11762v2 (quant-ph; v1 13 July 2026, v2 17 August
2026).

## Verified locator

DOI: 10.48550/arXiv.2607.11762.
Preprint: https://arxiv.org/abs/2607.11762v2 (the abstract page lists v1 and v2). The TeX source
`final_v2.tex` of the v2 e-print supplies the statements below.

## Source statements

Standing assumptions (Remark, Section II): finite-dimensional Hilbert spaces, finite-outcome POVMs,
exact tomography and tomographic completeness of the input family $\mathcal T$, that is
$\operatorname{span}_{\mathbb R}(\mathcal T)=\mathrm{Herm}(\mathcal H_{\mathrm{in}})$. The adjoint kernel
is restricted to Hermitian operators:
$\ker(\mathcal E^\dagger)=\{X\in\mathrm{Herm}(\mathcal H_{\mathrm{out}}):\mathcal E^\dagger(X)=0\}$.
Two POVMs are compatible if a joint POVM $\{J_{ab}\}$ has marginals $\sum_bJ_{ab}=M_a$ and
$\sum_aJ_{ab}=N_b$.

Definition (Operational concealment):

> Let $\mathcal{T} \subseteq \mathcal{S}(\mathcal{H}_{\mathrm{in}})$ be a set of input states. POVMs
> $\{M_a\},\{N_b\}$ are *concealed* by a quantum channel $\mathcal{E}$ relative to $\mathcal{T}$ if there
> exist compatible POVMs $\{F_a\},\{G_b\}$ such that for all $\rho \in \mathcal{T}$,
> $\mathrm{Tr}[F_a \mathcal{E}(\rho)] = \mathrm{Tr}[M_a \mathcal{E}(\rho)]$ and
> $\mathrm{Tr}[G_b \mathcal{E}(\rho)] = \mathrm{Tr}[N_b \mathcal{E}(\rho)]$.

Section III: "For fixed finite outcome sets $\Omega$ and $\Lambda$, let
$\mathcal C_{\mathcal E}^{\Omega,\Lambda}$ denote the set of POVM pairs concealed by $\mathcal E$." The
theorem "Kernel invariance of concealment" proves $\mathcal C_{\mathcal E_1}=\mathcal C_{\mathcal E_2}$ for
channels with a common output space and $\ker(\mathcal E_1^\dagger)=\ker(\mathcal E_2^\dagger)$, and is
followed by:

> Equality of adjoint kernels is sufficient for concealment-equivalence: channels with different
> dynamical realizations but identical adjoint kernels are indistinguishable with respect to
> concealment of POVM pairs. […] Whether equality of adjoint kernels is also necessary for
> concealment-equivalence remains open.

The introduction uses complete dephasing as the basic example of concealment: after dephasing, the
Pauli $X$ effects are operationally equivalent to $I/2$ while the Pauli $Z$ effects are unchanged.
