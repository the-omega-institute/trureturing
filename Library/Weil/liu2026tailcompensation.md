---
bibkey: liu2026tailcompensation
authors: Vincent Liu
year: 2026
title: "Certified Weil Positivity Beyond the Unit Window: Source-Exact Block-Schur and Tail-Compensation Bounds for the Riemann Zeta Function"
doi: null
url: https://github.com/luciferyu666/certified-weil-positivity/releases/tag/v1.0-mcom-submission
claim: The author-submitted manuscript states full complex Weil-form coercivity at physical half-widths 1 and 17/16 and retains a positive rank-two Fourier-tail correction in its finite sign test. These fixed-window statements do not cover the first new FIB cutoff c=9 or supply cofinal positivity.
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed-window positivity and retained tail compensation

The primary source is the author's release [v1.0-mcom-submission](https://github.com/luciferyu666/certified-weil-positivity/releases/tag/v1.0-mcom-submission), submitted to *Mathematics of Computation* on 14 September 2026. The inspected source is pinned to commit `b6cd2183c1e79c6c27a34267812a7b2d73ed1b59`: [manuscript TeX](https://github.com/luciferyu666/certified-weil-positivity/blob/b6cd2183c1e79c6c27a34267812a7b2d73ed1b59/frozen-source/publication/manuscript.tex) and [submitted PDF](https://github.com/luciferyu666/certified-weil-positivity/blob/b6cd2183c1e79c6c27a34267812a7b2d73ed1b59/manuscript.pdf). The downloaded PDF has SHA-256 `91126eee6ceb5315a4a40a4d4b2f34d058a71432ae18a8aaf47146f71abf418e`, matching the pinned README's submitted-original hash. This is an author-posted submission; journal acceptance, a DOI and external human reproduction are not asserted by the release.

The theorem statements and analytic interfaces below were inspected in the pinned source. The numerical package was not executed, and the source's historical verification labels are not independent evidence supplied by this note. The complete package is the separately attached `w200-frozen-artifact.zip`, rather than GitHub's automatic source archive. The [rights statement](https://github.com/luciferyu666/certified-weil-positivity/blob/b6cd2183c1e79c6c27a34267812a7b2d73ed1b59/RIGHTS.md) grants no blanket open-source license; this note provides citations and mathematical applications, without copying its implementation or certificates.

## Source normalization and support

In section 2, equations (1)–(2), the legal domain is $\mathcal D_a=C_c^\infty((-a,a);\mathbb C)$, with

$$
F_f(z)=\int_{\mathbb R}f(u)e^{-izu}\,du,
\qquad H_f(x)=\Re\int_{\mathbb R}f(v+x)\overline{f(v)}\,dv.
$$

Writing $A(t)=\Re\psi(1/4+it/2)-\log\pi$, the complete form is

$$
Q(f)=2\Re\bigl(F_f(i/2)\overline{F_f(-i/2)}\bigr)
+\frac1{2\pi}\int_{\mathbb R}A(t)|F_f(t)|^2\,dt
-\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}H_f(\log n).
$$

Both poles, Gamma and every contributing prime power are retained. There is no imposed Mellin-vanishing condition, parity restriction or RH hypothesis. For a smooth test with this support, only $\log n<2a$ contributes. The minus sign in $F_f$ reverses the project's plus-sign Fourier variable; the even Gamma bracket and the paired poles retain the same quadratic normalization. For even tests, $F_f(i/2)=F_f(-i/2)$ and the pole term is $2|F_f(i/2)|^2$.

Theorem A, section 3, equation (3), states

$$
Q(f)\ge2^{-151}\|f\|_2^2\quad(f\in\mathcal D_1).
$$

Theorem B, section 4, equation (6), states

$$
Q(f)\ge2^{-49162}\|f\|_2^2\quad(f\in\mathcal D_{17/16}).
$$

The bounded-operator proof covers both parity sectors and the entire orthogonal complement, then applies its conclusion to the original smooth domain. These are the manuscript's full-form claims, rather than claims about a positive finite compression alone. Their computer-assisted certificates have not been independently reproduced here. The comparison with [Zhu's versioned half-width $0.8$ result](suzuki2026screw.md) concerns support range, not a stronger coercivity constant.

## The positive tail remains in the retained matrix

At the source's fixed half-width $a=17/16$ and Fourier-band cutoff $\Omega=256$, equations (7)–(9) write

$$
Q(f)=\langle f,(M+K)f\rangle+T_{\rm tail}(f),
\qquad
T_{\rm tail}(f)=\frac1{2\pi}\int_{|t|>256}
\bigl(A(t)-7/2\bigr)|F_f(t)|^2\,dt.
$$

Here $M$ retains all paired prime shifts for $n\in\{2,3,4,5,7,8\}$, and $K$ retains the pole kernel and the central Gamma band. The source proves the quantitative tail input

$$
T_{\rm tail}(f)\ge2^{-49162}\|f\|_2^2+\langle f,Uf\rangle,
\qquad
U=81|h_0\rangle\langle h_0|+27|h_1\rangle\langle h_1|.
$$

If $B_{256}$ is the sinc-kernel band operator and $v_0,v_1$ are the first two normalized Legendre modes, these retained vectors are

$$
h_j=(I-B_{256}-2^{-49158}I)v_j.
$$

They are **tail-filtered** vectors. Replacing them by $v_j$ would change the estimate. The compression of $U$ enters the source-error finite sign test in section 6, equation (22). Its two integer matrices cover the two 224-dimensional parity sectors, with the complement and coupling charged separately. This is a reusable positive-tail mechanism, not a new general Schur principle. The numerical constants and certified matrices belong to the specified support and band parameters.

Reflection commutes with $B_{256}$, so $h_0$ is even and $h_1$ is odd. On even tests the second rank-one contribution vanishes and the retained contribution is $81|\langle h_0,f\rangle|^2$. This is a restriction of the source's estimate at $17/16$, not a positivity statement at a larger support.

## Matching the first new FIB window

In the project's Fourier convention the interval has length $\ell=\log c$ and physical half-width $a=\ell/2$. For $c_0=c_1=3$ and $c_{r+2}=c_{r+1}c_r$, the first new cutoff is $c_2=9$. Consequently

$$
a_9=\log3>17/16,
\qquad e^{17/8}\approx8.3729<9,
\qquad a_9-17/16\approx0.0361123.
$$

Theorem B does not cover this window. At the exact $c=9$ endpoint, the shift $\log9=2a_9$ has zero overlap, so the same prime-power list $\{2,3,4,5,7,8\}$ applies. The missing step is an estimate for the enlarged interval's actual operator, retained matrix and infinite complement. An unchanged prime list does not transport the old certificate or its tiny margin. The next FIB cutoff $c_3=27$, with $a_{27}=3\log3/2$, also lies outside the stated range.

The [existing same-symbol coupling allowance](../Fourier/montgomery1978largesieve.md) keeps a common signed cross interval, every middle mode and the second-jet remainder. A sufficient consumer still needs the actual retained form to dominate their complete Schur cost. The source's positive-tail correction suggests retaining an available arithmetic-compatible positive contribution in that form; it does not establish that domination at $c=9$, an induction step or cofinal support positivity. Failure of a particular upper allowance to fit would not refute positivity or RH.
