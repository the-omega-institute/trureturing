---
bibkey: graydon2022stochastic
authors: Matthew A. Graydon and Joshua Skanes-Norman and Joel J. Wallman
year: 2022
title: Designing Stochastic Channels
doi: null
url: https://arxiv.org/abs/2201.07156v1
claim: "Section II asks whether all stochastic channels are unital for d = 3; Eq. (11) defines stochasticity by a positive identity-vector eigenvalue of the normalized Choi state, and Appendix A proves qubit unitality."
strata_touched:
  - D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation
license: citation-only
triage: anchor
---

# Stochastic channels and qutrit unitality

## Verified locator

Source: https://arxiv.org/abs/2201.07156v1

The arXiv preprint has no journal DOI. Section II, p. 2, defines the normalized
Choi state in Eq. (2), $J(\Phi)=d^{-1}(\Phi\otimes\mathrm{id}_d)
(\operatorname{col}(1_d)\operatorname{col}(1_d)^\dagger)$.

The stochastic-channel definition, Section II, p. 2, is:

> A stochastic channel is a CPTP map $\Phi\in B(B(\mathbb C^d))$ such
> that for some $0<\lambda\leq1$
> $J(\Phi)\operatorname{col}(1_d)=\lambda\operatorname{col}(1_d).$ (11)

The qutrit question, Section II, p. 2, is:

> We leave open the question of whether or not all stochastic channels are unital for d = 3.

The source's construction in Eqs. (14)–(17) gives a nonunital stochastic channel
in dimension four and extends to every even dimension greater than two.
Appendix A, pp. 5–6, proves that every stochastic qubit channel is unital:

> Theorem 5. Let $\Xi\in B(B(\mathbb C^2))$ be a stochastic quantum
> channel. Then $\Xi$ is unital.

The qutrit instance uses zero-based `Fin 3` indices and output-first Choi
coordinates. Its four Kraus matrices are $I_3/\sqrt2$,
$\operatorname{diag}(1,-1/2,-1/2)/\sqrt2$, $\sqrt{3/8}E_{01}$ and
$\sqrt{3/8}E_{02}$. The associated channel has normalized Choi eigenvalue
$1/2$ along the identity vector and sends $I_3$ to
$\operatorname{diag}(7/4,5/8,5/8)$.
