---
bibkey: kubota2025evenperiodic
authors: S. Kubota, H. Sekido and K. Yoshino
year: 2025
title: "Regular graphs to induce even periodic Grover walks"
doi: 10.1016/j.disc.2024.114345
url: https://arxiv.org/abs/2307.13227v1
claim: "Question 4.11 asks whether 2l-periodic 3-regular graphs exist when l is an odd multiple of 3."
strata_touched:
  - D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod
license: citation-only
triage: anchor
---

# Regular graphs to induce even periodic Grover walks

S. Kubota, H. Sekido and K. Yoshino, *Regular graphs to induce even periodic Grover walks*,
arXiv:2307.13227v1 (2023); Discrete Mathematics 348 (2025) 114345.

The source defines the directed-edge set in §2.1 as follows:

> Let G = (V, E) be a finite, simple, connected, and undirected graph … A = A(G) as the set {xy, yx | {x, y} ∈ E}. … Let a^{−1} denote the directed edge yx. Let o(a) and t(a) be the origin x and terminus y of a.

Section 2.2 defines the Grover walk verbatim:

> the time evolution matrix U = U(G) ∈ C^{A×A} of the Grover walk over G is defined by U_{a,b} = 2/deg_G t(b) − 1 if a = b^{−1}; 2/deg_G t(b) if t(b) = o(a) and a ≠ b^{−1}; 0 if t(b) ≠ o(a). … If there exists τ ∈ N such that U^τ = I_A, then we say that the graph G is periodic and the minimum τ is period. Such a graph is also called a τ-periodic graph.

After Theorem 4.10, Question 4.11 is printed as:

> Let l be an odd integer that is a multiple of 3. Do 2l-periodic 3-regular graphs exist?

The formal settlement proves the negative answer for every odd l, so the divisibility-by-3 premise is unnecessary for the obstruction.

## Verified locator

DOI: `10.1016/j.disc.2024.114345` identifies *Regular graphs to induce even
periodic Grover walks* by S. Kubota, H. Sekido and K. Yoshino, published in
Discrete Mathematics 348 (2025), article 114345. The version at
https://arxiv.org/abs/2307.13227v1 supplies the definitions in §§2.1–2.2,
Theorem 4.10 and the quoted Question 4.11.
