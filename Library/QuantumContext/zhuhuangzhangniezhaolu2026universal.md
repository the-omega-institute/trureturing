---
bibkey: zhuhuangzhangniezhaolu2026universal
authors: Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu
year: 2026
title: "Universal entanglement detection with geometrically optimal witnesses"
doi: 10.1103/82gn-78lv
url: https://arxiv.org/abs/2610.17592v1
claim: "The paper constructs entanglement witnesses from the Hilbert-Schmidt distance to the separable states, evaluates this distance numerically for several families, and conjectures for the noisy four-qubit Smolin state that the distance to the separable states of the partitions where it is entangled is 0 for p at most 1/3 and the distance to the noisy state at p = 1/3, equal to (√3/4)(p − 1/3), above it."
strata_touched:
  - D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance
license: citation-only
triage: anchor
---

# Universal entanglement detection with geometrically optimal witnesses

X. Zhu, K. Huang, C. Zhang, X. Nie, Q. Zhao and D. Lu, arXiv:2610.17592v1 [quant-ph]; Phys. Rev. A 114, 042409 (2026). Quotations are from the v1 TeX source.

The state and the measure (Appendix, "Four-qubit Smolin state"):

> \rho_S = \frac{1}{16} \left( I + \sigma_x^{\otimes 4} + \sigma_y^{\otimes 4} + \sigma_z^{\otimes 4} \right),

> The HS measure of a state under a specific partition $\mathcal{P}$ is defined as
> D(\rho) = \min_{\sigma \in \mathrm{SEP}(\mathcal{P})} \|\rho - \sigma\|,
> where $\mathrm{SEP}(\mathcal{P})$ denotes the set of separable states under the partition $\mathcal{P}$. Due to the symmetry of the Smolin state, it suffices to consider the bipartitions $\{1\}:\{2,3,4\}$ and $\{1,2\}:\{3,4\}$, the tripartition $\{1\}:\{2\}:\{3,4\}$, and the four-partition $\{1\}:\{2\}:\{3\}:\{4\}$.

The noisy state and the conjecture:

> \mathcal{N}_p(\rho_S) = p \rho_S + (1-p) \frac{I}{16}

> remains entangled for $p > \frac{1}{3}$ \cite{PhysRevA.74.010305}. A natural conjecture is that
> \begin{equation}
>     D(\mathcal{N}_p(\rho_S)) =
>     \begin{cases}
>         0, & p \in [0, \frac{1}{3}], \\
>         \|\mathcal{N}_p(\rho_S) - \mathcal{N}_{\frac{1}{3}}(\rho_S)\|, & p \in (\frac{1}{3}, 1],
>     \end{cases}
> \end{equation}
> which simplifies to
> \begin{equation}
>         D(\mathcal{N}_p(\rho_S)) =
>     \begin{cases}
>         0, & p \in [0, \frac{1}{3}], \\
>         \frac{\sqrt{3}}{4} \left( p - \frac{1}{3} \right), & p \in (\frac{1}{3}, 1].
>     \end{cases}
> \end{equation}

The text continues: "Our numerical results strongly support this conjecture".

## Verified locator

Source: https://arxiv.org/abs/2610.17592v1
- URL: https://arxiv.org/abs/2610.17592v1 (source `manuscript.tex`, md5 `db9c376c24127cc118b3e270cf74af42`):
  - the Smolin state, l. 657–661;
  - the measure and the partitions, l. 662–666;
  - the noisy state, l. 669–671;
  - the conjecture, l. 672–687.
- DOI: 10.1103/82gn-78lv (https://doi.org/10.1103/82gn-78lv); arXiv v1 is the only version.
