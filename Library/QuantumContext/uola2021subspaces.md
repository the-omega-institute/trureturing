---
bibkey: uola2021subspaces
authors: Roope Uola; Tristan Kraft; Sébastien Designolle; Nikolai Miklin; Armin Tavakoli; Juha-Pekka Pellonpää; Otfried Gühne; Nicolas Brunner
year: 2021
title: "Quantum measurement incompatibility in subspaces"
doi: 10.1103/PhysRevA.103.022203
url: https://arxiv.org/abs/2010.04048v2
claim: "The paper studies the joint measurability of POVM assemblages after compression to lower-dimensional subspaces, constructs incompatible qutrit assemblages compatible in every qubit subspace, and leaves open whether demanding compatibility under every Heisenberg channel to a smaller dimension gives a strictly smaller class than compatibility in every subspace."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence
license: citation-only
triage: anchor
---

# Quantum measurement incompatibility in subspaces

R. Uola, T. Kraft, S. Designolle, N. Miklin, A. Tavakoli, J.-P. Pellonpää, O. Gühne and N. Brunner, arXiv:2010.04048v2; Phys. Rev. A 103, 022203 (2021). Quotations are from the v2 TeX source.

Joint measurability:

> Formally, joint measurability of $\mathcal M$ is defined as the existence of a parent POVM $\{G_{\vec a}\}_{\vec a}$ such that
>   M_{a_x|x}=\sum_{\hb{a_i}{i\neq x}} G_{\vec a}.

Compression to a subspace:

> The truncation is modelled by a projection $P_n$ onto an $n$-dimensional subspace, i.e., we are interested in the compatibility properties of the measurement assemblage
>     \mathcal M_n^U=\{P_nU^\dagger M_{a_x|x}UP_n\}_{a_x|x},

> First, compatibility can be present in \textit{all} strict subspaces of dimension $n$, i.e., $\mathcal M_n^U$ being compatible for every unitary $U$ in the initial Hilbert space.

The question:

> It is worth mentioning that one can modify the concept of incompressible incompatibility by demanding that a measurement assemblage becomes compatible under every Heisenberg channel (a channel preserving identity, but not necessarily trace preserving) to a smaller dimensional system.
> Although we will leave open the question of whether this provides a strict subset of measurement assemblages that are compatible in every subspace, we note that the Peres conjecture technique also works in this scenario, see Appendix~\hyperref[app:peres]{A}.

Heisenberg channels:

> Namely, one can see the shared state in a steering experiment as a Heisenberg channel (i.e., completely positive identity-preserving map)

## Verified locator

Source: https://arxiv.org/abs/2010.04048v2
- URL: https://arxiv.org/abs/2010.04048v2 (source `main.tex`, md5 `6163cf1a820fa25c11e245db807f87ae`):
  - joint measurability, l. 141–147;
  - compression to subspaces, l. 163–174;
  - the question, l. 215–216;
  - Heisenberg channels, l. 585.
- DOI: 10.1103/PhysRevA.103.022203 (https://doi.org/10.1103/PhysRevA.103.022203).
