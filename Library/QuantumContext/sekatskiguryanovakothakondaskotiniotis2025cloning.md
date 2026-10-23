---
bibkey: sekatskiguryanovakothakondaskotiniotis2025cloning
authors: Pavel Sekatski; Yelena Guryanova; Naga Bhavya Teja Kothakonda; Michalis Skotiniotis
year: 2025
title: "Cloning Quantum Channels"
doi: 10.48550/arXiv.2509.08059
url: https://arxiv.org/abs/2509.08059v1
claim: "The paper treats deterministic cloning of quantum channels with quantum processes, gives necessary conditions for super-replication, shows that amplitude-damping channels have at most linear cloning rate, compares coherent and measure-and-prepare processes, observes that a coherent process attains Choi fidelity one for amplitude-damping channels at N=M, and conjectures that no measure-and-prepare process does."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning
license: citation-only
triage: anchor
---

# Cloning Quantum Channels

P. Sekatski, Y. Guryanova, N. B. T. Kothakonda and M. Skotiniotis, arXiv:2509.08059v1 (2025). Quotations are from the v1 TeX source.

Measure-and-prepare processes:

> \textit{Measure-and-prepare} processes consist of two steps: (i) a measurement process $\{\proc{E}_\ell\}$ that consumes $N$ copies of the input channel to produce a classical outcome $\ell$ with probability $\proc{E}_\ell[\cE^{\times N}]$, and (ii) a global channel preparation $\widehat \cE_\ell^{(M)} \in \cL(\cH^{\otimes M}\tightto \cH^{\otimes M})$ conditioned on the value $\ell$. These processes have the general form $\proc{P}_{\rm M\& P}[\cE^{\times N}]=\sum_{\ell} \proc{E}_\ell[\cE^{\times N}] \widehat{\cE}_\ell^{(M)}$

The amplitude-damping family:

> $\ADset :=\{\cE_{\adp}| \adp\in[0,1]\}$ of qubit amplitude-damping (AD) channels $\cE_\adp[\,\cdot\,] := K_0(\adp) \cdot K_0^\dag(\adp) +K_1(\adp) \cdot K_1^\dag(\adp),\quad \text{with}\ K_0(\adp) = \left(\begin{array}{cc}1 & 0\\ 0& \sqrt{1-\gamma} \end{array}\right)$, $K_1(\adp) = \left(\begin{array}{cc} 0& \sqrt{\gamma}\\ 0& 0 \end{array}\right)$ in the computational basis.

The conjecture:

> In particular, it achieves ${\rm F}_{\rm CJ}^{\ADset|\rm coh}=1$ at $N=M$, which, for amplitude-damping channels, we conjecture to be impossible for any measure-and-prepare process.

## Verified locator

Source: https://arxiv.org/abs/2509.08059v1
- URL: https://arxiv.org/abs/2509.08059v1 (source `arxiv_v1.tex`, md5 `abcdd29ea99d1c5adf0206c6b9a9d211`):
  - measure-and-prepare processes, l. 1094–1100;
  - the amplitude-damping family, l. 1538–1553;
  - the conjecture, l. 1684–1685.
- DOI: 10.48550/arXiv.2509.08059 (https://doi.org/10.48550/arXiv.2509.08059; arXiv v1 is the only version).
