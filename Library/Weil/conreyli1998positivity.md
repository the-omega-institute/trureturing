---
bibkey: conreyli1998positivity
authors: J. B. Conrey, Xian-Jin Li
year: 1998
title: A note on some positivity conditions related to zeta and L-functions
doi: null
url: https://arxiv.org/abs/math/9812166v1
claim: Two specified global imaginary-translation positivity conditions for reproducing-kernel function spaces associated with the completed zeta function fail. The source records numerical witnesses and a nonnumerical argument for the reciprocal-generator condition; this does not decide positivity on selected physical sources or the complete Weil form.
strata_touched: []
license: citation-only
triage: anchor
---

# Existing limits of imaginary-translation positivity

The inspected primary source is [arXiv:math/9812166v1](https://arxiv.org/abs/math/9812166v1), 3 December 1998. Its [ten-page PDF](https://arxiv.org/pdf/math/9812166v1) has SHA-256 `bdb68ede69e41939be0c2b740cbe1955da8b24940e30eb8c8f4554878dfb4568`. The source statements and the accompanying argument below are literature inputs. No independent proof audit, numerical reproduction or Lean verification is asserted.

## Preserve the two different spaces and domains

The source uses the normalization

$$
\xi_0(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad E(z)=\xi_0(1-iz),\qquad W(z)=1/E(z).
$$

The omitted conventional factor $1/2$ has no effect on the ratios below. The source's $H(E)$ is its de Branges space, including the reproducing-kernel condition in equation (2.1), rather than an arbitrary weighted $L^2$ space. Its $\mathcal F(W)$ is the analytic-function space defined on printed p.3, with the boundary and growth conditions stated there.

| Source locator | Proposed positive supplier and its consequence | Reported limitation |
|---|---|---|
| Theorem 1, printed pp.2–3; section 3.1, equation (3.1), p.6 | For an entire $E$ with no real zeros, the stated Hermite–Biehler inequality, $E^\#(z)=\epsilon E(z-i)$ with $|\epsilon|=1$, and strictly increasing $y\mapsto|E(x+iy)|$ for $y>0$, positivity of $\Re\langle h,h(\cdot+i)\rangle_{H(E)}$ for every $h$ for which both functions belong to $H(E)$ forces the zeros onto $\operatorname{Im}z=-1/2$ and an additional sign condition at each zero. | Section 3.1, equation (3.2), reports a negative zero-derivative witness for this additional condition for $E(z)=\xi_0(1-iz)$. |
| Theorem 2, printed pp.4–5; section 3.1, equation (3.3), pp.6–7 | For zero-free analytic $W$ in the upper half-plane, an everywhere-defined linear map $T:\mathcal F(W)\to\mathcal F(W)$ sending each kernel $K(w,\cdot)$ to $K(w+i,\cdot)$ and satisfying $\Re\langle h,Th\rangle_{\mathcal F(W)}\ge0$ would give analytic continuation of $W$ to $\operatorname{Im}z>-1/2$ and $\Re[W(z)/W(z+i)]\ge0$ there. | Section 3.1, equation (3.4), reports a negative ratio witness. The section 4 Remark, printed p.9, records Sarnak's nonnumerical argument against condition (3.3). |

Here $E^\#(z)=\overline{E(\bar z)}$. For this $E$, the source verifies the other hypotheses of Theorem 1 before testing equation (3.1). The negative witnesses are source-reported Mathematica calculations; reading them does not certify their values. The nonnumerical Remark applies to the reciprocal-generator condition (3.3), not an independent nonnumerical verification of equation (3.2).

## Keep the ratio orientation in the parameter map

With $s=1-iz$,

$$
\frac{W(z)}{W(z+i)}=\frac{\xi_0(s+1)}{\xi_0(s)}.
$$

Equation (3.4) computes the reciprocal ratio at $s=1+282i$ and reports real part $-0.000131957$. A nonzero complex number and its reciprocal have real parts of the same sign, so this orientation agrees with the proposed obstruction. The section 4 argument uses values in $\operatorname{Re}s>1/2$, corresponding to $\operatorname{Im}z>-1/2$. These are the source's specific ratio and half-plane; no exclusion of all comparisons between two vertical lines follows.

## Relation to the actual-source program

The [complete-source account](suzuki2026screw.md) retains a nonnegative logarithmic-derivative reserve on $\operatorname{Re}s=1$ and a separate, unpaid joint signed debit in (W362). A positive scalar logarithmic-derivative weight does not supply either of the imaginary-translation forms above. Applying either source theorem would require a map from the actual theta source into its stated Hilbert space, the required translation-domain membership, and the particular positivity assumption.

The [selected-source construction](hernandezsantamaria2025optimal.md) adds an actual variational null equation and reciprocal constraints. The reported failure on the entire source spaces does not determine the sign on that constrained class. It also does not invalidate the complete Weil criterion, Suzuki's real spectral shift, other operators with explicit correction terms, or other norms and domains. Those comparisons need their own interfaces.

This source is reused to avoid proposing conditions (3.1) or (3.3) as an available unconditional global supplier. It supplies no payment of the actual joint debit, no strict all-integer Robin bound, and no proof or disproof of RH.
