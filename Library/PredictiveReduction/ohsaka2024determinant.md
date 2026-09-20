---
bibkey: ohsaka2024determinant
authors: Naoto Ohsaka
year: 2024
title: On the Parameterized Intractability of Determinant Maximization
doi: 10.1007/s00453-023-01205-0
url: https://arxiv.org/abs/2209.12519v3
claim: Maximum principal-determinant selection has strong complexity barriers, including arrowhead support; this does not establish a minimum-determinant claim by a sign change.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Determinantal selection: preserve the optimization direction

The arXiv record identifies v3, revised 18 February 2024, and the Algorithmica DOI above; a preliminary version appeared at ISAAC 2022. The retained Section 14 source reading checked the abstract and parsed full-text Section 3/Theorem 3.1 on determinant maximization for rational positive semidefinite principal submatrices and the arrowhead/star-support restriction. A requested PDF screenshot failed, so this note does not attest visual page inspection.

The source is prior art for complexity and sparsity limits in determinantal subset selection. Its maximization objective differs from the minimum average posterior-recovery KL in unified theory Section 14. The latter section therefore gives its own rational graph reduction with a polynomially controlled log-series gap, inside a well-conditioned Gaussian experiment with nonresonant Hamiltonian modes.

No inference is made that every tree-supported minimum problem is hard or easy. Section 14 exactly minimizes only a pairwise surrogate on forests and certifies an additive error for the actual log determinant. The rounded-Schur continuation separately controls the original objective through precision perturbations. Neither claims a generic exact determinant optimizer, a proof that P differs from NP, or a constant-accuracy hardness theorem.

This citation is contextual to observable closure and representation selection. It contributes no new Lean declaration, no external-open-problem resolution claim, and no machine certification of the paper's complexity results. Global priority of the repository combinations is not established.
