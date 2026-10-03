---
bibkey: rolfes2026peano
authors: Julian Rolfes, Luke Schleef, Philipp Svinger, Paul Niessner, Florian Grube
year: 2026
title: Peano Existence Theorem
doi: null
url: https://github.com/philipp-svinger/mathlib4/blob/a6c8f2f1ae84638491c3f1635c9f8448bda1e727/Mathlib/Analysis/ODE/Peano.lean
claim: "IsPeanoODE.exists_eq_forall_mem_Icc_eq_integral: a continuous bounded field on a finite-dimensional cylinder has an integral solution on the prescribed interval, remaining in the closed ball."
strata_touched:
  - D5/S3/Geometry/ODE/QuantitativePeano
license: Apache-2.0
triage: anchor
---

# Quantitative Peano existence on a closed cylinder

**Theorem 1.1 (quantitative Peano integral solution).** Let $E$ be a finite-dimensional real normed vector space, including dimension zero. Let $f:\mathbb R\times E\to E$, $t_{\min}\le t_0\le t_{\max}$, $x_0\in E$, and $r,L\ge0$. Assume that $f$ is jointly continuous on the cylinder $[t_{\min},t_{\max}]\times\overline B(x_0,r)$, that $\|f(t,x)\|\le L$ throughout that cylinder, and that

$$
L\max(t_{\max}-t_0,t_0-t_{\min})\le r.
$$

Then there exists a curve $\alpha:\mathbb R\to E$, continuous on $[t_{\min},t_{\max}]$, whose values on that interval lie in $\overline B(x_0,r)$ and which satisfies, for every $t\in[t_{\min},t_{\max}]$,

$$
\alpha(t)=x_0+\int_{t_0}^{t}f(s,\alpha(s))\,ds.
$$

In particular $\alpha(t_0)=x_0$. No spatial Lipschitz condition is required, and uniqueness is not asserted. The curve outside the prescribed interval is unrestricted. The radius, bound and interval may be degenerate.

The source proof constructs delayed Tonelli integral approximations. A common speed bound controls their ranges and gives equicontinuity. Compactness of the finite-dimensional closed ball and Arzela–Ascoli yield a uniformly convergent subsequence. Vanishing delays and dominated convergence pass the actual approximation equations to the limiting integral equation. Time reflection gives the backward solution, and the two solutions are joined at their common value $x_0$ at $t_0$.

The source is Julian Rolfes, Luke Schleef, Philipp Svinger, Paul Niessner and Florian Grube, *Peano Existence Theorem*, in [philipp-svinger/mathlib4 at a6c8f2f1ae84638491c3f1635c9f8448bda1e727](https://github.com/philipp-svinger/mathlib4/blob/a6c8f2f1ae84638491c3f1635c9f8448bda1e727/Mathlib/Analysis/ODE/Peano.lean#L543). This is an existing source theorem; no mathematical originality is claimed.

The exact immutable locator is `Mathlib/Analysis/ODE/Peano.lean`, `IsPeanoODE.exists_eq_forall_mem_Icc_eq_integral`, lines 541–574, with its declaration beginning on line 543. The hypotheses are collected in `IsPeanoODE`. The source file has 30,549 bytes and SHA-256 `7c8a83bd188c97e1eb4aae0436e0ffbd0c334ead91bd3e9a282b6f334f3ebf4b`.

The notice reads “Copyright (c) 2026 Julian Rolfes. All rights reserved.” and names all five authors above. It releases the file under Apache 2.0. The applicable [LICENSE at the same revision](https://github.com/philipp-svinger/mathlib4/blob/a6c8f2f1ae84638491c3f1635c9f8448bda1e727/LICENSE) has 11,357 bytes and SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.

The native declaration is `D5.S3.Geometry.ODE.QuantitativePeano.IsPeanoODE.exists_eq_forall_mem_Icc_eq_integral`. Its parameters use the same finite-dimensional real normed space, field, time endpoints, initial time and value, and nonnegative radius and bound. Its conclusion is a function on the real line with continuity, ball containment and the integral equation restricted to the prescribed closed interval. The delayed-integral construction is adapted under Lean 4.33.0 and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`; the original author and copyright notices and Apache license are retained.

This theorem establishes analytic existence. It does not establish CFMP geometric realization, metric-domain invariance, face gluing, a volume or co-volume identity, uniqueness, flat-block elimination or convergence.
