---
bibkey: milne2014fullyentangledfraction
authors: Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph
year: 2014
title: "Quantum correlations of two-qubit states with one maximally mixed marginal"
doi: 10.1103/PhysRevA.90.024302
url: https://arxiv.org/abs/1404.3951v2
claim: "Let rho be a general two-qubit state with steering ellipsoid centred at c. The fully entangled fraction is tightly bounded as f(rho) <= 1 - c/2 (Conjecture 2, Section V; c is the length of the centre vector)."
strata_touched:
  - D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction
license: citation-only
triage: anchor
---

# Quantum correlations of two-qubit states with one maximally mixed marginal

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.90.024302

Source: https://arxiv.org/abs/1404.3951v2

Physical Review A 90, 024302 (2014). The arXiv v2 (29 August 2014,
"Published version") replaces v1 (15 April 2014, titled "Quantum
correlations of maximally obese states"); the conjecture text is the
same in both versions.

Section V, Conjecture 2:

> Let $\rho$ be a general two-qubit state with $\mathcal{E}$ centred at $\vec c$. The fully entangled fraction is tightly bounded as $f(\rho)\leq 1-c/2$.

Section III defines the fully entangled fraction:

> The fully entangled fraction of a bipartite state $\rho$ is defined by $f(\rho)=\max_{|\phi\rangle} \langle \phi| \rho |\phi\rangle$, where the maximum is taken over all maximally entangled states $|\phi\rangle$.

Section I describes the steering ellipsoid: "Given all possible
measurements by Bob, the set of Bloch vectors to which Alice can be
steered forms her steering ellipsoid $\mathcal{E}$ inside the Bloch
sphere. $\mathcal{E}$ is described by its centre $\vec c$ and a real,
symmetric $3\times 3$ matrix $Q$." For a canonical state
$(\mathbb 1\otimes(2\rho_B)^{-1/2})\rho(\mathbb 1\otimes(2\rho_B)^{-1/2})$
Alice's Bloch vector coincides with $\vec c$. The scalar $c$ in the
conjecture is the length $|\vec c|$. Theorem 3 of the paper proves
$f(\tilde\rho)\le(1+\sqrt{1-c})^2/4$ for canonical states only; Section V
states that the fully entangled fraction "do[es] not transform
straightforwardly under local filtering operations", which is why the
general bound was left open.

## Centre of the steering ellipsoid

The closed formula for the centre is in the companion paper S. Jevtic,
M. Pusey, D. Jennings and T. Rudolph, "Quantum steering ellipsoids",
Physical Review Letters 113, 020402 (2014),
https://arxiv.org/abs/1303.4724v2. With
$\Theta_{\mu\nu}=\operatorname{tr}(\rho\,\sigma_\mu\otimes\sigma_\nu)$,
first index Alice, $\boldsymbol a$ and $\boldsymbol b$ the local Bloch
vectors and $T$ the correlation matrix:

> This gives a steering ellipsoid centred at $\boldsymbol{c}_A = \frac{\boldsymbol{a}-T\boldsymbol{b}}{1-b^{2}}$

and

> If $b=1$ then $\rho$ is a product state in which case there is no steering and the steering ellipsoid is the single point $\boldsymbol a$.

The repository formalization uses exactly these conventions:
$\vec c=(\boldsymbol a-T\boldsymbol b)/(1-|\boldsymbol b|^2)$ when
$|\boldsymbol b|\ne1$ and $\vec c=\boldsymbol a$ when $|\boldsymbol b|=1$,
with the Euclidean length on $\mathbb R^3$.
