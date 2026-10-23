---
bibkey: castelnovo2005stochasticmatrixform
authors: Claudio Castelnovo; Claudio Chamon; Christopher Mudry; Pierre Pujol
year: 2005
title: From quantum mechanics to classical statistical physics — Generalized Rokhsar–Kivelson Hamiltonians and the Stochastic Matrix Form decomposition
doi: 10.1016/j.aop.2005.01.006
url: https://arxiv.org/abs/cond-mat/0502068v1
claim: A stochastic-matrix-form Hamiltonian and its detailed-balance classical generator are related by a positive diagonal transform, with quantum energies equal to classical decay rates in the specified normalization.
strata_touched: []
license: citation-only
triage: anchor
---

# Stochastic-matrix-form correspondence and its clock convention

The primary source is Castelnovo–Chamon–Mudry–Pujol,
*Annals of Physics* 318, 316–344,
[DOI:10.1016/j.aop.2005.01.006](https://doi.org/10.1016/j.aop.2005.01.006),
[arXiv:cond-mat/0502068v1](https://arxiv.org/pdf/cond-mat/0502068v1),
§3.1, equations (19b), (22a–e), (26a–c).
This note cites the source without redistributing its text or PDF.

For the paper's preferred configuration basis, a real symmetric
stochastic-matrix-form Hamiltonian $H$ has positive ground amplitudes
proportional to $e^{-KE_C/2}$. Its column-probability generator is

$$
W_{CC'}=-e^{-K(E_C-E_{C'})/2}H_{CC'}.
$$

Writing $D=\operatorname{diag}(e^{-KE_C/2})$, this is
$W=-DHD^{-1}$. Off-diagonal rates are nonnegative, columns sum to
zero, and detailed balance holds for $p_C\propto e^{-KE_C}$.
Equations (26a–c) identify the corresponding eigenvalues by
$\lambda_n(W)=-\varepsilon_n(H)$ and give the weighted left and right
eigenvectors. In function-generator convention $\mathscr L=W^{\mathsf T}$,
the same real symmetric Hamiltonian satisfies
$H=-D\mathscr L D^{-1}$.

The FIB phase-parent and joint-occupation design volume §1 uses $K=1$,
$E_u=-\log p_u$ on a finite positive support and the unit-per-site
conditional-resampling rates
$r_{uv}=p_v/(p_u+p_v)$ along legal single-bit edges.
The symmetric coefficient multiplying the paper's
$e^{-(E_u-E_v)/2}$ in the off-diagonal column rate is
$\sqrt{p_up_v}/(p_u+p_v)$.
The corresponding quantum edge term is

$$
\frac{
(\sqrt{p_v}|u\rangle-\sqrt{p_u}|v\rangle)
(\sqrt{p_v}\langle u|-\sqrt{p_u}\langle v|)
}{p_u+p_v}.
$$

This is the established transform, rather than a new general
correspondence. The FIB application combines it with the volume's
specified phase experiment and the positive-activity local parent.
The site sampling distribution, tensor locality and calibrated
information formulas are separate conclusions of that application.

The transform compares classical decay rates with Hamiltonian energies
after choosing their units. Its semigroup relation uses imaginary time.
It does not identify classical stochastic motion with real-time unitary
evolution. Zero masses require restricting the positive support;
disconnected support has multiple zero modes. A diagonal transform by
itself supplies neither a tensor-local decomposition for an arbitrary
law nor a physical preparation or dissipative implementation.
