---
bibkey: cullinanyoung2026krawtchouk
authors: J. Cullinan and E. Young
year: 2026
title: "The Gibbs phenomenon for the Krawtchouk polynomials"
doi: 10.1007/s10958-026-08499-9
url: https://arxiv.org/abs/2603.05408v1
claim: "Remark 8 states that numerical experimentation suggests the leading coefficient of the even Krawtchouk sign interpolant I_N is (-1)^((N-2)/2) C((N-2)/2)/(N-1)!."
strata_touched:
  - D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk
license: citation-only
triage: anchor
---

# Cullinan--Young Krawtchouk sign interpolant

J. Cullinan and E. Young, “The Gibbs phenomenon for the Krawtchouk polynomials,” arXiv:2603.05408v1 [math-ph] (5 March 2026). The journal version is “On the Krawtchouk expansion of the sign function,” J. Math. Sci. (2026), DOI 10.1007/s10958-026-08499-9.

Section 2, page 6: “Let I_N(x) be the Lagrange form of the interpolating polynomial of the points of P_N. Then I_N(x) = Σ_{i=0}^{N} sgn(i − N/2) ℓ_i(x), where ℓ_i(x) = Π_{j=0,j≠i}^{N} (x − (j − N/2))/(i − j).” The nodes and Lagrange basis are
`ℓ_i(x) = Π_{j=0, j≠i}^{N} (x − (j − N/2))/(i − j)` and
`I_N(x) = Σ_{i=0}^{N} sgn(i − N/2) ℓ_i(x)`.

Page 6, Remark 8: “Numerical experimentation suggests that the leading coefficient of I_N(x) (and, therefore, F_N(x)) is given by (−1)^{(N−2)/2}/(N−1)! · C((N−2)/2), where C(n) is the nth Catalan number.” The paper takes `N` even.

## Verified locator

DOI: https://doi.org/10.1007/s10958-026-08499-9

Source: https://arxiv.org/abs/2603.05408v1
