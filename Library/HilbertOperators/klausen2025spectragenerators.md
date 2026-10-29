---
bibkey: klausen2025spectragenerators
authors: Frederik Ravn Klausen
year: 2025
title: "Spectra of generators of Markovian evolution in the thermodynamic limit: From non-Hermitian to full evolution via tridiagonal Laurent matrices"
doi: null
url: https://arxiv.org/abs/2206.09879v3
claim: "A single-particle Lindbladian on the Hilbert-Schmidt operators over ℓ²(ℤ), with finite-range translation-invariant Hamiltonian and Lindblad operators, is a bounded operator and decomposes as a direct integral of finite-range Laurent operators with finite-range perturbations. Under the additional rank-one hypothesis the paper proves that if 0 lies in the spectrum then the Lindbladian is gapless or has an infinite-dimensional kernel, and lists as a further question whether 0 always lies in the spectrum."
strata_touched:
  - D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum
license: citation-only
triage: anchor
---

# Klausen, Spectra of generators of Markovian evolution in the thermodynamic limit

F. R. Klausen, arXiv:2206.09879v3 [math-ph] (version 3, 29 September 2025; version 1, June 2022, with A. H. Werner, under the title "Spectra of Lindbladians on the infinite line"). Quotations are from the v3 TeX source, with the source's macros `\Li` (a calligraphic L) and `\HS` (HS) expanded.

The Lindbladian (`section02.tex`): $\mathcal H=\ell^2(\mathbb Z)$ with position basis $\{|\delta_k\rangle\}$ and

> $$\mathcal{L}(\rho) = - i \lbrack H, \rho \rbrack + G \sum_{k} L_k \rho L_k^* - \frac{1}{2}(L_k^* L_k \rho  + \rho L_k^* L_k),$$

acting on $\mathrm{HS}(\mathcal H)$, with $H$ bounded self-adjoint, $G>0$ and $L_k\in\mathcal B(\mathcal H)$; the effective Hamiltonian $H_{\rm eff}=H-\frac{iG}2\sum_kL_k^*L_k$ shows that $G$ multiplies the whole dissipator. The assumptions are (Finite Range) $\langle\delta_y,L_k\delta_x\rangle=0=\langle\delta_y,H\delta_x\rangle$ whenever $\max\{|x-k|,|y-k|\}>r$, (TransInv) $S_1L_kS_{-1}=L_{k+1}$ and $H=S_1HS_1^*$, and (Rank 1) $\operatorname{Rank}(L_k)=1$; under the first two, $\mathcal L\in\mathcal B(\mathrm{HS}(\mathcal H))$, and the spectrum is taken there.

Theorem `thm:no_gap` (`section03.tex`): if $\mathcal L$ satisfies (Finite Range), (TransInv), (Rank 1) and $0\in\sigma(\mathcal L)$, then $\mathcal L$ is gapless or $\dim\ker\mathcal L=\infty$. The list of further questions (`section04.tex`) contains:

> Prove that if $\mathcal{L}$ is (Finite Range), (TransInv), and (Rank 1) then $0 \in \sigma(\mathcal{L})$, thereby strengthening Theorem (no gap).

## Verified locator

Source: https://arxiv.org/abs/2206.09879v3
- URL: https://arxiv.org/abs/2206.09879v3. The arXiv record has no journal reference. The e-print members `section02.tex` (258 lines, md5 `b5b553f1c8203d16c63a5b9330242407`), `section03.tex` (757 lines, md5 `a16eacc51b1bb4e77ceafb39b96fbb18`) and `section04.tex` (597 lines, md5 `227274cfa5a97ad104ecfdde8c5d4562`). Locations:
  - the Lindblad form, `section02.tex` l. 6–13; the effective Hamiltonian, l. 22;
  - the assumptions, l. 39–50; boundedness on the Hilbert-Schmidt operators, l. 54–57;
  - the vectorization, `section03.tex` l. 162–182; Theorem `thm:no_gap`, l. 506–509;
  - the question, `section04.tex` l. 574.
