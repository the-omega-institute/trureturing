---
bibkey: barriga2026dftbosonic
authors: Edgar Barriga et al.
year: 2026
title: "N-dimensional discrete Fourier transform via bosonic Hamiltonian"
doi: null
url: https://arxiv.org/abs/2609.05644
claim: "A waveguide array with propagation constants beta_l and couplings C_jk evolves by U = exp(-i C z); it realizes the N-dimensional discrete Fourier transform F_N (entries omega^(xy)/sqrt N, omega = exp(-2 pi i/N)) when input and output phase shifters give Phi_out U Phi_in = F_N. The graph has the waveguides as vertices and the nonzero couplings as edges. Section III.D conjectures edge ranges for the solutions; for N = 10 the third conjecture, with l = 5, gives at least N l / 2 = 25 edges. Section II.B asks whether the polygonal model (zero-diagonal real circulant couplings with C_l = C_{N-l}) can always yield F_N."
strata_touched:
  - D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation
  - D5/S3/Quantum/Dynamics/PolygonalFourierCouplings
license: citation-only
triage: anchor
---

# N-dimensional discrete Fourier transform via bosonic Hamiltonian

arXiv:2609.05644v1 (primary quant-ph; v1 only). Section II models a waveguide
array by the single-particle coupling matrix $\mathcal C$ with the propagation
constants on the diagonal and the evanescent couplings off it, $U=e^{-i\mathcal
Cz}$, with $z$ absorbed into the coefficients. The target is

> $F_N = \frac{1}{\sqrt N}\left(\omega^{jk}\right)$, where $\omega=e^{-2i\pi/N}$,

reached after input and output phase shifters,
$\Phi^{\rm out}U\Phi^{\rm in}=F_N$.

Section II.B (the polygonal model) takes the circulant coupling matrix with rows
$(0,C_1,\dots,C_{N-1})$, each row rotated one place to the right of the previous
one, with "the evanescent coupling strength felt by the waveguides has symmetry
$C_l=C_{N-l}$", reports analytic solutions for $N=4,5,6$ and numerical ones up
to $N=31$, and ends:

> Whether the polygonal model can always yield solutions to obtain $F_N$ from
> Eq.~\eqref{eq:Coupling_polygon} or not is beyond our theoretical efforts.

The formal answer is `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.result`:
for every $N$ there are strictly positive polygonal couplings and diagonal
unimodular phases with $\Phi^{\rm out}e^{-i\mathcal C}\Phi^{\rm in}=F_N$. An
explicit choice, argued and checked numerically in #13954 but not formalized, is
$\mathcal C_{jk}=\pi/(2N\sin^2(\pi(j-k)/N))$ for $j\ne k$ and $\mathcal C_{jj}=0$;
at $N=4,5,6$ it gives the
paper's analytic solutions (the hexagon of Appendix B has $C_2=\pi/9$; the main
text's $\pi/6$ is a misprint). Section III.D ("Observations and
conjectures to continue") states three conjectures; the third reads:

> \textbullet\ Third, all the other possible solutions for non-prime $N$ are in
> the following range of edges
> $\lvert E(R_{\ell})\rvert \leq \lvert E\rvert < \lvert E(K_{N-1})\rvert-\ell,$
> where $R_{\ell}$ denotes $\ell$-regular graphs (same number of edges per
> vertex) and $\lvert E(R_{\ell})\rvert =N\ell/2$.

For $N=10$ the same section fixes $\ell$: "This strongly suggests that there
should be a $\ell$-regular graph for $N=10$ as well, and it should be
$\ell=5$." The authors report four 5-regular graphs (25 edges) realizing
$F_{10}$.

## Verified locator

- URL: https://arxiv.org/abs/2609.05644 (v1; source file `DFT.tex`, md5
  `f6ff1ec31c30e8afc4674b5ef3ebf3b3`).
