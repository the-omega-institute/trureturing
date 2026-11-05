---
bibkey: liuqiudahlstenvedral2025lighttouch
authors: Xiangjing Liu; Yixian Qiu; Oscar Dahlsten; Vlatko Vedral
year: 2025
title: "Quantum causal inference with extremely light touch"
doi: 10.1038/s41534-024-00956-0
url: https://arxiv.org/abs/2303.10544v4
claim: "For coarse-grained measurements at two times, the pseudo-density matrix of a channel with Choi-Jamiolkowski matrix M is the Jordan product R = (M rho + rho M)/2 with rho = rho_1 tensor identity, and the PDM negativity f(R) = ||R||_tr - 1 vanishes for every input when the bipartite channel does not signal from B to A. The paper conjectures that every channel signalling from B to A admits a pure product input state with f(R_{B1A2}) > 0, and proves this for two-qubit unitary evolutions."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity
license: citation-only
triage: anchor
---

# Liu, Qiu, Dahlsten and Vedral, Quantum causal inference with extremely light touch

X. Liu, Y. Qiu, O. Dahlsten and V. Vedral, arXiv:2303.10544v4 [quant-ph]; npj Quantum Information 11, 54 (2025). Quotations are from the v4 TeX source, with the source's macros `\Tr`, `\mathbbm{1}` and `\map` (trace, identity and calligraphic map) kept as written.

The causal monotone, Eq. (`eq: causmono`):

> $$f(R) :=||R||_{tr}-1 = \Tr \sqrt{ R R^\dag}-1.$$
> If $R$ has negativity, $f(R)>0$.

The Choi-Jamiolkowski matrix, Eq. (`eq: CHOI`):

> $$M_{12}:= \sum^{2^n-1}_{i ,j=0}\ket{i}\bra{j}^T \otimes  \mathcal{M}_{2|1} \left( \ket{i}\bra{j}  \right),$$

Theorem `thm: 2timesPDM`, the two-time pseudo-density matrix under coarse-grained measurements:

> $$R_{12} = \frac{1}{2}( M_{12} \, \rho  +\rho  \, M_{12}  ) ,$$
> where $\rho :=\rho_1 \otimes \mathbbm{1}_2$.

Theorem `thm:nullneg` (null PDM negativity for semicausal channels):

> If a quantum channel $\mathcal{P}$ does not allow signaling from $B$ to $A$, then, for any state $\rho_{A_1B_1}$ at time $t_1$,  the PDM $R_{B_1A_2} $ is positive semidefinite and the PDM negativity $f(R_{B_1A_2} )=0$.

The conjecture, after that theorem:

> We moreover conjecture that if the channel is signalling from B to A, we can always find a pure {\em product} input state such that $f(R_{B_1A_2} )> 0$. We prove this conjecture for a quite general case of 2-qubit unitary evolutions in the Supplementary Information.

## Verified locator

Source: https://arxiv.org/abs/2303.10544v4
- DOI: https://doi.org/10.1038/s41534-024-00956-0 (npj Quantum Information 11(1), article 54; published 29 March 2025; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2303.10544v4. The e-print member `arxiv.tex` has 852 lines and md5 `fa6102d805431c16f176e32895ce216c`. Locations:
  - Eq. `eq: causmono`, l. 143–145;
  - Eq. `eq: CHOI`, l. 161–164;
  - Theorem `thm: 2timesPDM`, l. 166–173;
  - the semicausal channels, l. 216;
  - Theorem `thm:nullneg`, l. 226–228;
  - the conjecture, l. 231.
- The arXiv record lists four versions (v1 posted 19 March 2023) and the journal reference "npj Quantum Information 11, 54 (2025)" (arXiv API metadata).
