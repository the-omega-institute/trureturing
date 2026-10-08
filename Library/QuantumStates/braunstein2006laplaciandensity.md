---
bibkey: braunstein2006laplaciandensity
authors: Samuel L. Braunstein; Sibasish Ghosh; Simone Severini
year: 2006
title: "The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states"
doi: 10.1007/s00026-006-0289-3
url: https://arxiv.org/abs/quant-ph/0406165v2
claim: "Conjecture 6.7 asserts that the star maximizes entanglement of formation among connected graph density matrices."
strata_touched:
  - D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds
  - D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds
  - D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/s00026-006-0289-3

Source: https://arxiv.org/abs/quant-ph/0406165v2

## Statement and scope

Definition 2.2, p. 3: “The density matrix of a graph $G$ is the matrix”
$$\sigma(G) \stackrel{\mathrm{def}}{=} \frac{1}{d_G}L(G).$$
The degree-sum on p. 2 is $d_G=\sum_{i=1}^n d_G(v_i)$.

Section 2.3, p. 4: “The von Neumann entropy of an $n\times n$ density matrix $\rho$ is $S(\rho)=-\sum_{i=1}^n\lambda_i(\rho)\log_2\lambda_i(\rho)$.” The convention is $0\log_2 0=0$.

The paragraph before the conjectures, p. 18: “Let $\rho_{AB}$ be a density matrix acting on $\mathbb C_A^p\otimes\mathbb C_B^q$, where $pq=n$.” It then defines
$$S_\rho=\left\{\{p_i,|\psi_i\rangle:i=1,2,\ldots,N\}:\rho_{AB}=\sum_i p_i|\psi_i\rangle_{AB}\langle\psi_i|,\ |\psi_i\rangle_{AB}\in\mathbb C_A^p\otimes\mathbb C_B^q,\ 0\le p_i\le1,\ \sum_i p_i=1\right\},$$
The next sentence is: “The entanglement of formation of $\rho_{AB}$ is denoted and defined by”
$$E_F(\rho_{AB})=\inf_{\{p_i,|\psi_i\rangle:i=1,2,\ldots,N\}\in S_\rho}\sum_{i=1}^N p_iS(\operatorname{tr}_X(|\psi_i\rangle_{AB}\langle\psi_i|)),\qquad X=A\text{ or }B.$$
The sentence ends “where $X=A$ or $X=B$.”
The state vectors are Euclidean unit vectors. The source's displayed reconstruction has an $n$ upper index while the ensemble has $N$ terms; the ensemble convention reads the reconstruction as the sum over those $N$ terms.

Conjecture 6.7, p. 18 (the final conjecture):

“Let $\mathcal{G}_{n}^{c}$ be the set of all connected graphs on $n$ vertices. Let $G\in\mathcal{G}_{n}^{c}$ ($|V|=pq$). Then $\max_{\mathcal{G}_{n}^{c}}E_{F}(\sigma(G))=E_{F}(\sigma(K_{1,n-1}))$.”

The product labeling is $i=sq+s'$ (Section 3.1); the star root is $v_1$. Lean uses zero-based pairs $(a,b)\in\operatorname{Fin}(p)\times\operatorname{Fin}(q)$, with root $(0,0)$, and connected simple graphs with a nonempty edge set. Loops do not affect the Laplacian. The bit-entropy ensemble infimum uses the literal partial trace over the second factor.
