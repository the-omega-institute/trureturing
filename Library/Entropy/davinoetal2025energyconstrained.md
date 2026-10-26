---
bibkey: davinoetal2025energyconstrained
authors: Raffaele D'Avino; Gabriel Senno; Mir Alimuddin; Antonio Acín
year: 2025
title: "Entanglement in the energy-constrained prepare-and-measure scenario: applications to randomness certification and channel discrimination"
doi: null
url: https://arxiv.org/abs/2510.27559v3
claim: "The paper studies energy-constrained prepare-and-measure behaviors with a shared state between the devices, shows that entanglement enlarges the set of behaviors compared with separable shared states, derives that separable devices deterministic on input 0 satisfy E_1 >= 2(1-2 omega)^2 - 1, and conjectures that for every positive energy bound some entangled behavior deterministic on input 0 violates this inequality."
strata_touched:
  - D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation
license: citation-only
triage: anchor
---

# Entanglement in the energy-constrained prepare-and-measure scenario

R. D'Avino, G. Senno, M. Alimuddin and A. Acín, arXiv:2510.27559v3 (15 January 2026; v1 31 October 2025). Quotations are from the v3 TeX source, with the macros `\Tr`, `\Qsep` and `\Qent` written as $\operatorname{Tr}$, $\mathcal Q_\omega^{\mathrm{sep}}$, $\mathcal Q_\omega^{\mathrm{ent}}$ and citations omitted.

Behaviors, for a shared state $\sigma_{PM}$, channels $\Lambda_x$ on $P$ and a POVM on $S\otimes M$:

> $p(b|x,y) = \operatorname{Tr}\left[ \Pi_{SM}^{b|y} (\Lambda_x \otimes \mathbb{1}_M)(\sigma_{PM}) \right].$

The paper uses two inputs $x\in\{0,1\}$ and one binary measurement $\{\Pi_{SM}^{b}\}_{b\in\{0,1\}}$.

The energy constraint:

> $\exists~H~ \text{s.t.} \operatorname{Tr}\left[ H\, \Lambda_x(\sigma_P) \right] \leq \omega_x,$ where $\omega_x\in[0,1/2)$ and $H$ is some hermitian operator (i.e., the Hamiltonian) with a non-degenerate ground state and a unit gap, i.e. $H=\sum_{i\geq 0}E_i\ket{E_i}\bra{E_i}$ with $E_0=0$ and $E_i\geq1$ for all $i\geq1.$

The paper then sets $\omega_0=\omega_1=\omega$. It denotes by $\mathcal Q_\omega^{\mathrm{sep}}$ the behaviors with separable $\sigma_{PM}$ and by $\mathcal Q_\omega^{\mathrm{ent}}$ those "when entanglement is allowed"; the correlators are $E_x=p(0|x)-p(1|x)$.

The inequality for separable devices deterministic on input 0:

> $E_1\geq 2(1-2\omega)^2-1=:I_\mathrm{det}^{\omega,\mathrm{sep}}$ … for all $\mathbf{p}\in\mathcal Q_\omega^{\mathrm{sep}}$.

The conjecture:

> Numerically, we find that for all tested positive values of $\omega$, there exist behaviors $\mathbf{p} \in \mathcal Q_\omega^{\mathrm{ent}}$ that are deterministic for input $x = 0$ but violate Eq.~(eq:deterministic-ineq-for-fixed-input-0). We conjecture that this holds for all $\omega > 0$.

## Verified locator

Source: https://arxiv.org/abs/2510.27559v3
- URL: https://arxiv.org/abs/2510.27559v3 (the e-print is a tar archive; member `paper_Quantum.tex`, 849 lines, md5 `012a72f4d8cfd30e14dc3813eda8f546`):
  - behaviors, l. 137–139;
  - two inputs and one binary measurement, l. 148;
  - the energy constraint, l. 151–154;
  - the sets of behaviors, l. 158;
  - the correlators, l. 165–166;
  - the inequality, l. 266–270;
  - the conjecture, l. 284.
- Crossref lists no journal version; the author list is from the TeX `\author` fields and the arXiv metadata.
