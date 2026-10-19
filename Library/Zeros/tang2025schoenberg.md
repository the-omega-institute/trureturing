---
bibkey: tang2025schoenberg
authors: Q. Tang, T. Zhang
year: 2025
title: "Sharp Schoenberg type inequalities and the de Bruin–Sharma problem"
doi: 10.48550/arXiv.2508.10341
url: https://arxiv.org/abs/2508.10341v3
claim: Section 1.3, Conjecture 1.13 states the real-order reciprocal critical-point moment inequality and its equality criterion; Section 6, Conjecture 6.3 states the sharp order −2 critical-point inequality (6.9) and its collinear sufficient equality condition; Proposition 6.4 proves the n=2 case.
strata_touched:
  - D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo
  - D5/S3/Zeros/CriticalPoints/TangZhangRealOrder
license: citation-only
triage: anchor
---

# Sharp Schoenberg type inequalities and the de Bruin–Sharma problem

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2508.10341
- Version: https://arxiv.org/abs/2508.10341v3 (5 Dec 2025).
- Location: arXiv:2508.10341v3, §1.3, Conjecture 1.13.
- Location: §6, p. 31, Conjecture 6.3, equation (6.9), and Proposition 6.4.

## Source and scope

Q. Tang, T. Zhang, "Sharp Schoenberg type inequalities and the de Bruin–Sharma problem", arXiv:2508.10341v3 (5 Dec 2025), §6, p. 31.

> The identity (5.2) leads us to the following conjectural refinements of Theorem 6.1 in the case of order −2.

> Conjecture 6.3. Let P(z) = z ∏_{j=1}^n (z − z_j), z_j ∈ C \ {0}, and let w_1, …, w_n denote the zeros of P′(z). Then Σ_{k=1}^n 1/|w_k|² ≤ 3 Σ_{j=1}^n 1/|z_j|² + |Σ_{j=1}^n 1/z_j|². (6.9) Moreover, equality in (6.9) holds whenever z_1, …, z_n all lie on the same line passing through the origin.

> In the case n = 2 we can verify Conjecture 6.3 by an explicit computation.

The last sentence introduces Proposition 6.4. Theorem 6.1 gives the weaker
right side (n+3) Σ_j 1/|z_j|². Section 7's order −4 inequality concerns a
higher moment and is outside the formal result's scope.

The polynomial definition and the conjecture are attributed to this source.
The general-degree proof and necessity of collinearity in the equality
case are derived in the repository. The Schur–Frobenius inequality used in
the proof is classical; its formal proof does not constitute a claim that
the source originated that matrix inequality.

## Real-order conjecture

Q. Tang, T. Zhang, "Sharp Schoenberg type inequalities and the de Bruin–Sharma problem", arXiv:2508.10341v3, §1.3, Conjecture 1.13.

> Conjecture 1.13. Let P(z) = z ∏_{j=1}^n (z − z_j), z_j ∈ C \ {0}, and let w_1, …, w_n be the zeros of P′(z). Then for every real number p ≥ 1 we have Σ_{k=1}^n 1/|w_k|^p ≤ ((n+1)^p + n − 1)/n · Σ_{j=1}^n 1/|z_j|^p. Moreover, equality holds if and only if z_1 = ⋯ = z_n.

The paper establishes the $p=1$ bound in Corollary 5.4 and the positive even orders; Theorem 1.14 gives non-sharp bounds at other orders by complex interpolation.

`TangZhangRealOrder.result` proves the sharp inequality for all real $p≥1$ and proves equality if and only if all nonzero roots coincide when $p>1$. It also refutes Conjecture 1.13 as stated: at $p=1$, $n=2$ and $(z_1,z_2)=(1,2)$ give equality although the roots differ. The replacement endpoint characterization by a common ray from zero remains unproved in these modules.

## Literature boundary

The exact quotation, version and page locator are supplied source evidence.
No independent current publication-absence check is asserted here, and no
worldwide priority claim follows from the source's conjecture label.
The named assertion is distinguished from the source's established n=2 case,
the weaker Theorem 6.1 bound, and the higher-order questions.

## License and formalization boundary

This citation-only note contains the mathematical statement and its locator.
It incorporates no source software. The order −2 Lean result covers all n≥1 and
nonzero complex z_j, with derivative roots counted with multiplicity, and
proves equality if and only if all z_j lie on a line through the origin.
The real-order result has the scope and endpoint exception stated above.
