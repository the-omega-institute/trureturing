---
bibkey: angelinos2022narain
authors: Nikolay Angelinos; Debarghya Chakraborty; Anatoly Dymarsky
year: 2022
title: "Optimal Narain CFTs from codes"
doi: 10.48550/arXiv.2206.14825
url: https://arxiv.org/abs/2206.14825v1
claim: "For prime p, the full enumerator polynomial of the code with generating matrix (I | B^T), evaluated at x_ab = t_a t_b with t_a = t_-a and averaged over the p^(c(c-1)/2) antisymmetric matrices B with zero diagonal, is conjectured to equal t_0^(2c) + (sum_k (sum_(a,b) cos(2 pi k a b / p) t_a t_b)^c - p t_0^c (sum_a t_a)^c) / p^c (eq. barP)."
strata_touched:
  - D5/S3/Quantum/Information/BFormCodeAveragedEnumerator
license: citation-only
triage: anchor
---

# Optimal Narain CFTs from codes

N. Angelinos, D. Chakraborty and A. Dymarsky, arXiv:2206.14825 (v1
2022-06-29, the only version); JHEP 11 (2022) 118. Subject: hep-th.

The paper builds Narain conformal field theories from codes over `F_p × F_p`.
For prime `p` a code of length `c` has a generating matrix that "can always be
brought to the form `G = (I | B^T)`, where `B` is an integer valued
antisymmetric `c × c` matrix defined mod `p`, `B^T = −B mod p`, and
`B_ii = 0`". Its codewords are `(r, B^T r)` with `r ∈ Z_p^c`, and its full
enumerator polynomial is `P_C({x_g}) = Σ_{(g_1, …, g_c) ∈ C} ∏_i x_{g_i}` with
`g_i = (a_i, b_i)`. Averaging over the `p^{c(c−1)/2}` matrices `B` at
`x_ab = t_a t_b`, `t_a = t_{−a}`, the authors write:

> We conjecture the form of corresponding averaged enumerator polynomial based
> on invariance under MacWilliams identity and explicit checks for
> sufficiently small n and prime p

followed by eq. (barP):
`P̄({t_a t_b}) = t_0^{2c} + (Σ_{k=0}^{p−1} (Σ_{a,b} cos(2πkab/p) t_a t_b)^c − p t_0^c (Σ_a t_a)^c) / p^c`
(the printed upper limit `p=1` is read as `p − 1`).

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2206.14825
- URL: https://arxiv.org/abs/2206.14825v1 (source of v1 retrieved 2026-09-30).
- Location: the section on codes over `F_p × F_p` for prime `p`, for the
  B-form of the generating matrix, the enumerator polynomial and eq. (barP).
