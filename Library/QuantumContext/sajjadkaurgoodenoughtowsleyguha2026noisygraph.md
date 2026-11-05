---
bibkey: sajjadkaurgoodenoughtowsleyguha2026noisygraph
authors: Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha
year: 2026
title: "Lower bounds on bipartite entanglement in noisy graph states"
doi: 10.22331/q-2026-05-21-2111
url: https://arxiv.org/abs/2404.09014v2
claim: "The paper computes the coherent information of graph states whose qubits are dephased before the CZ gates, in terms of the biadjacency matrix of a bipartition, and conjectures from its examples that the subsystem with more qubits always has the larger coherent information."
strata_touched:
  - D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation
license: citation-only
triage: anchor
---

# Lower bounds on bipartite entanglement in noisy graph states

A. Sajjad, E. Kaur, K. Goodenough, D. Towsley and S. Guha, arXiv:2404.09014v2 [quant-ph]; Quantum 10, 2111 (2026). Quotations are from the v2 TeX source.

The noise model (§2.2):

> For our noise model we consider depolarizing noise after the creation of the $n$ qubits in the $\ket{+}^{\otimes n}$ state prior to the application of the $\CZ$ gates. Note that depolarizing $\ket{+}$ states is equivalent to applying dephasing noise to them. Under such noise, each qubit remains in $\ket{+}$ with some probability $P$, and flips into $\ket{-}$ with probability $1-P$.

The coherent information (§2.3):

> Consider a mixed state $\rho_{AB}$ shared by Alice and Bob. The coherent information is given by $\sI_B = H(\rho_B) - H(\rho_{AB})$, where $\rho_B$ is the reduced density matrix for Bob, and $H(\rho)$ is the Von Neumann entropy function given by $H(\rho) = -\mathrm{Tr}\left(\rho \log_2\rho\right)$.

> A related quantity is the reverse coherent information \cite{Garc_a_Patr_n_2009}, defined by $\sI_A = H(\rho_A) - H(\rho_{AB})$

(the displayed equations are written inline here).

The conjecture (§5.4, "The subsystem with more qubits has higher coherent information?"):

> In all of the examples that we have considered, we have observed that the subsystem  with the most qubits has the largest coherent information regardless of the types of the two subsystems and their distributions. Therefore, we conjecture that this is generally true but are unable to make a definitive statement.

## Verified locator

Source: https://arxiv.org/abs/2404.09014v2
- URL: https://arxiv.org/abs/2404.09014v2 (source `main.tex`, md5 `230ee16b992b9567441d518d7471253e`):
  - graph states, l. 163–184;
  - the noise model, l. 186–187;
  - the coherent information, l. 197–213;
  - the conjecture, l. 948–951.
- DOI: 10.22331/q-2026-05-21-2111 (https://doi.org/10.22331/q-2026-05-21-2111; Crossref lists Quantum, volume 10, article 2111, published 21 May 2026).
