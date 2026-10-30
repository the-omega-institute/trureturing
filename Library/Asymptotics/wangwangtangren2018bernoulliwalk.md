---
bibkey: wangwangtangren2018bernoulliwalk
authors: Caishi Wang; Ce Wang; Yuling Tang; Suling Ren
year: 2018
title: "Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise"
doi: 10.1155/2018/2507265
url: https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265
claim: "The paper studies the quantum walk on the integers whose coin space is the space of square-integrable Bernoulli functionals, driven by the annihilation and creation operators of quantum Bernoulli noise. It links the moments of the walk's distribution to these operators, proves the Gaussian limit for the localized initial states built from the vacuum and one excited coordinate, derives a quantum central limit theorem, and conjectures that every localized initial state has the classical random walk's limit distribution."
strata_touched:
  - D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit
license: citation-only
triage: anchor
---

# Wang, Wang, Tang and Ren, quantum walk in terms of quantum Bernoulli noise

C. Wang, C. Wang, Y. Tang and S. Ren, Advances in Mathematical Physics 2018, Article 2507265 (open access, CC BY 4.0). There is no arXiv version. Formulas are read from the publisher's formula images.

The space $h$ of square-integrable Bernoulli functionals has the orthonormal basis $\{Z_\sigma\mid\sigma\in\Gamma\}$, where $\Gamma$ is the set of finite subsets of $\mathbb N$. The annihilation and creation operators act by $\partial_kZ_\sigma=\mathbf 1_\sigma(k)Z_{\sigma\setminus k}$ and $\partial_k^*Z_\sigma=[1-\mathbf 1_\sigma(k)]Z_{\sigma\cup k}$ (Lemmas 1–2). With $R_n=\frac12(\partial_n^*+\partial_n+I)$ and $L_n=\frac12(\partial_n^*+\partial_n-I)$ (Lemma 5), the QBN-based walk evolves by

$$\Phi_{n+1}(x)=R_n\Phi_n(x-1)+L_n\Phi_n(x+1),\qquad x\in\mathbb Z,\ n\ge0$$

(Definition 6), and its distribution at time $n$ is $x\mapsto\|\Phi_n(x)\|^2$. A localized initial state is $\Phi_0(0)=\varphi$, $\Phi_0(x)=0$ for $x\ne0$, with $\|\varphi\|=1$. Theorem 21 proves weak convergence to $N(0,1)$ for $\varphi=\alpha Z_\emptyset+\beta Z_{\{0\}}$. The Conclusion Remarks state:

> However, only for some special localized initial states, have we obtained the walk's limit probability distributions. It is still unclear whether or not the walk has a limit probability distribution for a general localized initial state. […] Thus we conjecture that, for a general localized initial state, the QBN-based walk might still have the same limit probability distribution as the classical random walk.

## Verified locator

Source: https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265
- DOI: https://doi.org/10.1155/2018/2507265 (Advances in Mathematical Physics 2018, Article 2507265; title, author list and journal from Crossref).
- URL: https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265, the publisher's HTML. Locations:
  - the basis and the operators, Section 2, Eqs. (7)–(9) and Lemma 5;
  - the walk, Section 3, Definition 6, Eq. (16);
  - the localized initial state, Eq. (53); the limit theorem, Theorem 21, Eq. (68);
  - the conjecture, Section 6 (Conclusion Remarks).
