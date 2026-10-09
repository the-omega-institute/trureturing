---
bibkey: bluhm2025inclusion
authors: A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita
year: 2025
title: "Inclusion constants for free spectrahedra with applications to quantum incompatibility"
doi: 10.48550/arXiv.2512.17706
url: https://arxiv.org/abs/2512.17706v1
claim: "For γ = 4/(1+√3) and every θ ∈ [0, π/2] the feasibility SDP (37) at X(θ) has a solution (Theorem 5.6, by a two-piece construction split at π/8); Appendix A.1 conjectures that one explicit single-formula tuple (C₁, C₂ given, C₃–C₆ by Eq. (47)) is feasible on the whole interval."
strata_touched:
  - D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness
license: citation-only
triage: anchor
---

# Bluhm, Evert, Klep, Magron and Nechita, inclusion constants for free spectrahedra

A. Bluhm, E. Evert, I. Klep, V. Magron and I. Nechita, *Inclusion constants for free spectrahedra
with applications to quantum incompatibility*, arXiv:2512.17706v1 (19 December 2025; quant-ph,
cross-listed math-ph).

## Verified locator

DOI: 10.48550/arXiv.2512.17706.
Primary version: https://arxiv.org/abs/2512.17706v1 (the only arXiv version).
The TeX source `draft.tex` of v1 supplies the feasibility SDP (37) (`eq:XMinBallSDP`, §5.1.2),
Proposition 5.4 (the extreme points $X(\theta)$), Theorem 5.6 and its proof in Appendix A
(Eq. (47), `eq:CiEquations`), and the conjecture of Appendix A.1.

## Source statements

SDP (37): $(C_1,\dots,C_6)\in\mathfrak D_{\gamma,X}$ iff $\oplus_{i=1}^6C_i\succeq0$,
$C_1-2C_2+C_3+C_4-2C_5+C_6=X_1$, $C_1+C_2-2C_3+C_4+C_5-2C_6=X_2$,
$C_1+C_2+C_3-C_4-C_5-C_6=X_3$ and $\sum_iC_i=\gamma I$, for $C_i\in SM_2(\mathbb C)$.

Proposition 5.4: $X(\theta)=\left(\operatorname{diag}(1,-2),\operatorname{diag}(-2,1),
\begin{pmatrix}\cos\theta&\sin\theta\\ \sin\theta&-\cos\theta\end{pmatrix}\right)$.

Theorem 5.6: "Set $\gamma:= \frac{4}{1+\sqrt{3}}$. Then $\mathfrak D_{\gamma,X(\theta)}$ is nonempty for
all $\theta \in [0,\pi/2]$."

Eq. (47): $C_3=-C_1-C_2+X_3(\theta)/2+\gamma I/2$, $C_4=-C_1+X_1/3+X_2/3+\gamma I/3$,
$C_5=-C_2-X_1/3+\gamma I/3$, $C_6=C_1+C_2-X_2/3-X_3(\theta)/2-\gamma I/6$.

Appendix A.1: "We conjecture that if one instead takes
$C_1 = \left(\frac{1}{\sqrt{3}}-\frac{1}{2}\right) \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$ and
$C_2=\frac{1}{12} \left(\begin{array}{cc} 3 \cos (\theta)+8 \sqrt{3}-9-\beta & 3 \sin (\theta)-2 \sqrt{3}+3 \\ 3 \sin (\theta)-2 \sqrt{3}+3 & -3 \cos (\theta)+8 \sqrt{3}-3 - \beta \end{array}\right)$
where $\beta = \sqrt{3} \sqrt{\left(6-4 \sqrt{3}\right) \sin (\theta)+6 \cos (\theta)-4 \sqrt{3}+13}$,
then the resulting point is feasible for $\theta \in [0,\pi/2]$". The text names proving
$\det(C_2)\ge0$ as the obstacle.

## Scope

Theorem 5.6 is proved with a different construction on $[0,\pi/8]$ and $[\pi/8,\pi/2]$; the
Appendix A.1 tuple is stated as a conjecture.
