---
bibkey: perito2026bell
authors: I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín, R. Augusiak
year: 2026
title: "Bell inequalities tailored to optimal global randomness certification"
doi: 10.48550/arXiv.2606.21362
url: https://arxiv.org/abs/2606.21362v3
claim: "Conjecture 1: the Tsirelson bound of the d-outcome Bell functional I_d = (1/2)Σ_{x<2}Σ_{y<d} ω^{xy} A_x⊗B_y + h.c. is 2/sin(π/(2d)) and is attained by A_0 = Z, A_1 = X, the maximally entangled state and B_y = Σ_k λ_{y,k} X^{k+1}Z^k; the appendix proves that these B_y are unitary with d-th-root-of-unity eigenvalues, and the bound is checked by NPA for d ≤ 6."
strata_touched:
  - D5/S3/QuantumBounds/PeritoTsirelson
license: citation-only
triage: anchor
---

# Perito et al., Bell inequalities for optimal global randomness certification

I. Perito, R. D'Avino, M. Jung, P. Mironowicz, A. Acín and R. Augusiak, *Bell inequalities
tailored to optimal global randomness certification*, arXiv:2606.21362v3 (21 July 2026; quant-ph;
v1 19 June 2026, v2 24 June 2026).

## Verified locator

DOI: 10.48550/arXiv.2606.21362.
Primary version: https://arxiv.org/abs/2606.21362v3.
The TeX source `main.tex` of v3 supplies §II (the unitary notation $A_x=\sum_a\omega^a\Pi_{a|x}$,
$\omega=e^{2\pi i/d}$), §III.2 (the functional `eq:red_ineq_gen`, the strategy `eq:optbob`, the value
`eq:tsir_bound` and Conjecture 1, label `conj:i`), Appendix `app:ibounds` (the bound
$\beta_\mathcal Q(d)\le d\sqrt2$, `eq:qbound`), Appendix `app:numericalbounds` (NPA bounds for
$d\le6$) and Appendix `app:optimalconstruction` (the coefficients `eq:optcoeffs` and the validity
proof of $B_y$).

## Source statements

Functional (§III.2): "$\mathcal{I}_d \equiv \frac{1}{2}\sum_{x=0}^1\sum_{y=0}^{d-1} \omega^{xy}A_x \otimes B_y + \text{h.c.,}$".

Strategy (§III.2): "$A_0 = Z = \sum_k^{d-1} \omega ^ k \ket{k}\!\!\bra{k} , \; A_1 = X = \sum_k^{d-1} \ket{k+1}\!\!\bra{k}$",
"$B_y = \sum_{k=0}^{d-1} \lambda_{y,k} X^{k+1} Z^k$", with (Appendix, `eq:optcoeffs`)
"$\lambda_{y,k} = \frac{(-1)^k\omega^{\frac{k(k+1)}{2}}\omega^{-y(1+k)}}{d\sin\left(\frac{\pi}{d} (k+\frac{1}2{}) \right)}$",
and "this strategy gives: $\mathcal{I}_d = 2 \left[ \sin \left(\frac{\pi}{2d} \right) \right] ^{-1}$".

Conjecture 1: "The Tsirelson bound of $\mathcal{I}_d$ is given by Eq.~\eqref{eq:tsir_bound} … and is
attained by taking $A_0=Z$, $A_1=X$; the state $\ket{\psi_d} = \frac{1}{\sqrt d} \sum_k \ket{kk}$; and
$B_y$ defined by Eq. \eqref{eq:optbob}."

Evidence (§III.2): "Using NPA, we can numerically see that the conjecture holds for $d=4,5,6$ …
which explains why we could not go beyond $d=6$."

Appendix `app:ibounds`: "$\beta_\mathcal{Q}(d) \leq d\sqrt{2}$ … This upper bound is, in general, not
tight."

Appendix `app:optimalconstruction`: "we show that $B_y$ defined in \eqref{eq:optbob} with coefficients
\eqref{eq:optcoeffs} are proper observables, i.e. that they are unitary and with eigenvalues equal to
$d$-th roots of unity. To this end we write $B_y$ as a product of $X$ and a polynomial of $XZ$".

## Scope

The validity of $B_y$ and the attained value $2/\sin(\pi/(2d))$ are proved in the paper. The open
part of Conjecture 1 is the upper bound for every $d$; the paper's analytic bound $d\sqrt2$ coincides
with it only at $d=2$ (CHSH).
