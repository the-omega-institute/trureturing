---
bibkey: liu2026tailcompensation
authors: Vincent Liu
year: 2026
title: "Certified Weil Positivity Beyond the Unit Window: Source-Exact Block-Schur and Tail-Compensation Bounds for the Riemann Zeta Function"
doi: null
url: https://github.com/luciferyu666/certified-weil-positivity/releases/tag/v1.0-mcom-submission
claim: The author-submitted manuscript states full complex Weil-form coercivity at physical half-widths 1 and 17/16 and retains a positive Fourier-tail correction. A weighted-Schur application gives a 4/5 lower bound for the actual prime comparison block at c=9; the complete retained sign and cofinal positivity remain unproved.
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

## A source-formula application to the actual prime block at $c=9$

The source's weighted Schur formula in Appendix B.4, “Weighted Schur bound including prime power eight,” can be reused without its old support-dependent constants. At the new physical half-width $a=\log3$, let $I=(-a,a)$, $\mathcal H=L^2(I;\mathbb C)$ and

$$
(S_df)(u)=\mathbf1_I(u+d)f(u+d),\qquad
C_{\rm p}=\sum_{n\in\{2,3,4,5,7,8\}}w_n(S_{\log n}+S_{-\log n}),
\qquad w_n=\frac{\Lambda(n)}{\sqrt n}.
$$

These are the actual compressed translations on the whole Hilbert space, with $S_d^*=S_{-d}$. The $n=9$ endpoint translation is zero almost everywhere. Put $M_9=(7/2)I-C_{\rm p}$. The following application gives a lower bound for this **prime comparison block**, not for $Q$.

Choose $q(u)=1+(5/8)(u/a)^2$. The source formula bounds the absolute quadratic form by the weighted row sum:

$$
|\langle f,C_{\rm p}f\rangle|
\le\int_I r_q(u)|f(u)|^2\,du,
\qquad
r_q(u)=\sum_nw_n
\frac{\mathbf1_I(u+\log n)q(u+\log n)
+\mathbf1_I(u-\log n)q(u-\log n)}{q(u)}.
\tag{A1}
$$

This formula uses complex weighted Young and translation of the adjoint term; its validity does not require the source's $17/16$ width, finite-dimensional tests or RH. The function $r_q$ is even. New outward support cells and rational bounds are required at $a=\log3$.

Use the source's logarithm grid endpoints $l_p^-<\log p<l_p^+$ and root lower endpoints $k_n/10^6\le\sqrt n$:

| $p$ | $10^6l_p^-$ | $10^6l_p^+$ |
|---|---:|---:|
| $2$ | $693147$ | $693148$ |
| $3$ | $1098612$ | $1098613$ |
| $5$ | $1609437$ | $1609438$ |
| $7$ | $1945910$ | $1945911$ |

For $n=2,3,4,5,7,8$, the respective $k_n$ are $1414213,1732050,2000000,2236067,2645751,2828427$. For $n=p^j$, define

$$
w_n^+=\frac{l_p^+}{k_n/10^6},\qquad
t_n^-=\frac{j l_p^-}{l_3^+},\qquad
t_n^+=\frac{j l_p^+}{l_3^-}.
$$

Set $t_3^-=t_3^+=1$ instead: this shift equals the actual half-width exactly. The weight remains $\log3/\sqrt3$. Define

$$
x_1=t_4^--1,\quad x_2=1-t_2^-,\quad
x_3=t_5^--1,\quad x_4=t_7^--1,\quad x_5=t_8^--1.
$$

They are, respectively, $287681/1098613$, $405466/1098613$, $510824/1098613$, $847297/1098613$, $980828/1098613$, in increasing order inside $(0,1)$. On $x=u/a\in[0,1]$, the following outward lists activate negative shifts early and retain positive shifts late:

| Cell | Negative shifts | Positive shifts | Lower bound for the quadratic minimum |
|---|---|---|---:|
| $[0,x_1]$ | $2,3$ | $2$ | $2/5$ |
| $[x_1,x_2]$ | $2,3,4$ | $2$ | $13/100$ |
| $[x_2,x_3]$ | $2,3,4$ | none | $11/10$ |
| $[x_3,x_4]$ | $2,3,4,5$ | none | $4/25$ |
| $[x_4,x_5]$ | $2,3,4,5,7$ | none | $1/50$ |
| $[x_5,1]$ | $2,3,4,5,7,8$ | none | $4/25$ |

The positive $n=3$ shift is present only at the single endpoint $x=0$ under a closed-interval convention, hence contributes nothing to the $L^2$ integral. The rows cover every other support switch; no prime-power weight is deleted.

For each row, with $b=5/8$ and $R=27/10$, sum its listed terms with multiplicity to form

$$
W=\sum w_n^+,\quad
B=\sum_{\rm negative}w_n^+t_n^--\sum_{\rm positive}w_n^+t_n^+,
\quad D=\sum w_n^+(t_n^+)^2.
$$

Then, on that whole cell,

$$
(1+bx^2)(R-r_q(ax))\ge
P(x):=b(R-W)x^2+2bBx+(R-W-bD).
\tag{A2}
$$

The listed quadratic-minimum bounds were evaluated using exact fractions, at both endpoints and any interior vertex of a convex quadratic. Each minimum strictly exceeds $1/50$. Since $1+bx^2\le13/8$, (A1)–(A2) give

$$
|\langle f,C_{\rm p}f\rangle|
\le\left(\frac{27}{10}-\frac4{325}\right)\|f\|^2,
\qquad
\boxed{\frac45 I\preceq M_9\preceq\frac{31}{5}I.}
\tag{A3}
$$

The bound applies to the complete complex Hilbert space, and therefore its even subspace. This is a paper application of an existing weighted Schur formula with a new exact scalar parameter calculation; it is not a new kernel theorem, reproduction of a fixed-window certificate or claim of priority. The pole and Gamma band are still in $K$, and the positive exterior-frequency contribution remains in $T_{\rm tail}$. Neither $M_9\succ0$ nor its invertibility establishes positivity of $M_9+K+U$ or $Q$.

The following independent scalar replay produces the six quadratic minima using only exact fractions. The logarithm and root enclosures are the cited analytic inputs; this program verifies their downstream rational comparison, not the source's full analytic proof or a complete Weil certificate.

```python
from fractions import Fraction as F

beta, target = F(5, 8), F(27, 10)
log_lo = {2: 693147, 3: 1098612, 5: 1609437, 7: 1945910}
log_hi = {2: 693148, 3: 1098613, 5: 1609438, 7: 1945911}
root_lo = {2: 1414213, 3: 1732050, 4: 2000000,
           5: 2236067, 7: 2645751, 8: 2828427}
powers = {2: (2, 1), 3: (3, 1), 4: (2, 2),
          5: (5, 1), 7: (7, 1), 8: (2, 3)}
weight = {n: F(log_hi[p], root_lo[n])
          for n, (p, j) in powers.items()}
shift_lo = {n: F(1) if n == 3 else F(j * log_lo[p], log_hi[3])
            for n, (p, j) in powers.items()}
shift_hi = {n: F(1) if n == 3 else F(j * log_hi[p], log_lo[3])
            for n, (p, j) in powers.items()}
ends = [F(0), shift_lo[4] - 1, 1 - shift_lo[2],
        shift_lo[5] - 1, shift_lo[7] - 1, shift_lo[8] - 1, F(1)]
assert all(left < right for left, right in zip(ends, ends[1:]))
negative = [[2, 3], [2, 3, 4], [2, 3, 4], [2, 3, 4, 5],
            [2, 3, 4, 5, 7], [2, 3, 4, 5, 7, 8]]
positive = [[2], [2], [], [], [], []]
floors = [F(2, 5), F(13, 100), F(11, 10),
          F(4, 25), F(1, 50), F(4, 25)]

for i, (left, right) in enumerate(zip(ends, ends[1:])):
    neg, pos = negative[i], positive[i]
    W = sum((weight[n] for n in neg + pos), F(0))
    B = (sum((weight[n] * shift_lo[n] for n in neg), F(0))
         - sum((weight[n] * shift_hi[n] for n in pos), F(0)))
    D = sum((weight[n] * shift_hi[n] ** 2 for n in neg + pos), F(0))
    A, E, C = beta * (target - W), 2 * beta * B, target - W - beta * D
    points = [left, right]
    if A > 0 and left < -E / (2 * A) < right:
        points.append(-E / (2 * A))
    minimum = min(A * x * x + E * x + C for x in points)
    assert minimum > floors[i] >= F(1, 50)
    print(i + 1, minimum)
```

## The remaining retained-matrix consumer at $c=9$

The source's Certification Theorem, section 6, equations (17)–(22), now has a legitimate prime-block input $m=4/5$, $b=31/5$ at this new window. In particular $M_9$ is boundedly invertible and $\|M_9^{-1}\|\le5/4$. This removes the need to assume a positive floor for this block; it leaves the complete form's sign undecided.

Use the same actual interval, orthonormal retained embedding $E$ and projection $P=EE^*$ throughout. Reflection invariance permits choosing the even Hilbert space and an even retained dictionary for the existing RH route. If a new-window tail estimate supplies

$$
T_{{\rm tail},9}(f)\ge\tau_9\|f\|^2+\langle f,U_9f\rangle,
\qquad\tau_9\ge0,
$$

with $U_9$ bounded self-adjoint, put $V_9=K_9+U_9$, $J_9=E^*V_9E$, $R_9=V_9-EJ_9E^*$ and

$$
G_9=E^*M_9^{-1}E,\qquad
D_9=E^*M_9^2E-(E^*M_9E)^2.
$$

Suppose the actual new-window blocks satisfy $\|(R_9)_{10}\|\le e$, $(R_9)_{11}\succeq-nI$, $\|(R_9)_{11}\|\le h$, with $0\le n<4/5$. For $\theta,\chi>0$, direct parameter substitution in the existing source theorem makes the following a sufficient target:

$$
G_9^{-1}+J_9\succeq
\left(e\theta+\frac{(1+\chi)e^2}{4/5-n}\right)I
+\frac{25}{16}\left(e/\theta+n+
\frac{(1+\chi^{-1})h^2}{4/5-n}\right)D_9.
\tag{A4}
$$

This condition would imply $M_9+V_9\succeq0$ and hence the needed nonnegativity of $Q$ on its legal tests in this window. It is an application of the published block criterion, not an established inequality (A4). The new $K_9$, tail-filtered vectors, source intervals, projection errors, inverse-compression bound and finite sign test remain payable. None of the $17/16$ certificate's retained matrices, tail constants or errors has been transported to $\log3$ by (A3). Using another retained basis also requires identifying the same form and transporting all these objects together. Even a completed $c=9$ sign test would still leave the subsequent cofinal support layers required for RH.
