---
bibkey: carmeliheinosaaritoigo2025postponing
authors: Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo
year: 2025
title: "Postponing the choice: advantage of deferred measurements in quantum information processing"
doi: 10.1088/1367-2630/adf87c
url: https://arxiv.org/abs/2502.19871v1
claim: "The paper determines the compatibility region of a noisy sharp meter Q_s and a depolarizing channel I_t, describes the joint instruments attaining its boundary, shows that on the upper boundary the instrument tilde-J^(t) is the unique W-covariant joint instrument, and asks whether other joint instruments exist there."
strata_touched:
  - D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness
license: citation-only
triage: anchor
---

# Postponing the choice: advantage of deferred measurements in quantum information processing

C. Carmeli, T. Heinosaari and A. Toigo, arXiv:2502.19871v1 (2025-02-27); New J. Phys. 27, 094501 (2025). Quotations are from the v1 TeX source.

The noisy meters (`eq:QsPt`):

> \Qo_s(x) = s\,\kb{\varphi_x}{\varphi_x} + (1-s)\tfrac{1}{d}\id \,,\qquad \Po_t(y) = t\,\kb{\psi_y}{\psi_y} + (1-t)\tfrac{1}{d}\id\,,

The depolarizing channel (`eq:Ir`):

> I_r = r I + (1-r)\tfrac{1}{d}\id{\rm tr}

The coefficients (`eq:ab_bis`):

> a_k(r) = \frac{1}{\sqrt{d^k}}\left[\sqrt{r(d^k-1)+1} - \sqrt{1-r}\right]\,,\qquad b(r) = \sqrt{1-r}\,.

Joint instruments (`eq:joint_J`):

> \ii^\dag(\cdot,\id) = \Qo_s\,,\qquad \sum_x \ii(x,\cdot) = I_t

> An instrument $\ii$ which satisfies \eqref{eq:joint_J} is a {\em joint instrument} for $\Qo_s$ and $I_t$

The compatibility region (`thm:main_neg`, `eq:QI_comp_neg`), upper boundary:

> d^2 s \leq (d^2 - 2) (1 - t) + 2\sqrt{(1 - d^2) t^2 + (d^2 - 2) t + 1}

The upper-boundary instrument (`eq:tildeJ`):

> \tilde{\ii}^{(t)}(x,\rhoo) = \frac{1}{d} \big\{ b(t)^2 \tr{(\rhoo\Qo(x))} \id + a_2(t)b(t) (\rhoo\Qo(x) + \Qo(x)\rhoo) + a_2(t)^2 \rhoo \big\}

The question:

> We conclude that, when the point $(s,t)$ attains the second equality in \eqref{eq:QI_comp_neg}, the instrument $\tilde{\ii}^{(t)}$ is actually the unique $W$-covariant joint instrument for $\Qo_s$ and $I_t$. It is an open question whether in this case there exist other (necessarily not $W$-covariant) joint instruments.

## Verified locator

Source: https://arxiv.org/abs/2502.19871v1
- URL: https://arxiv.org/abs/2502.19871v1 (source `CHT_postponing_choice.tex`, md5 `260d15a3cfb6a4b474b99d950e675b89`):
  - the noisy meters, l. 622–623;
  - the depolarizing channel, l. 656–657;
  - the coefficients, l. 738–739;
  - joint instruments, l. 813–816;
  - the compatibility theorem, l. 1039–1046;
  - the instrument, l. 1198–1203;
  - the question, l. 1532.
- DOI: 10.1088/1367-2630/adf87c (https://doi.org/10.1088/1367-2630/adf87c).
