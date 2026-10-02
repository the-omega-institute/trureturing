---
bibkey: liu2026tailcompensation
authors: Vincent Liu
year: 2026
title: "Certified Weil Positivity Beyond the Unit Window: Source-Exact Block-Schur and Tail-Compensation Bounds for the Riemann Zeta Function"
doi: null
url: https://github.com/luciferyu666/certified-weil-positivity/releases/tag/v1.0-mcom-submission
claim: The author-submitted manuscript states full complex Weil-form coercivity at physical half-widths 1 and 17/16. Source-proof parameter applications supply a 4/5 prime-block floor, an actual positive Fourier-tail correction and even-space complement/coupling bounds at c=9; the retained sign and cofinal positivity remain unproved.
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

## The actual band complement at $a=\log3$

Appendix B fixes $L=17/16$, $\Omega=256$ and $\Omega L=272$ at its outset. Its band-complement and tail statements therefore cannot simply be instantiated at another width. The following application checks the width dependencies in B.1–B.3 and constructs the new operators; it does not use the old finite sign certificate.

Keep $a=\log3$ and the full complex space $\mathcal H=L^2((-a,a);\mathbb C)$. Write $c_{\rm band}=256a$, distinct from the arithmetic cutoff $c=9$. The cited logarithm enclosure gives

$$
272<c_{\rm band}<282,\qquad a<11/10.
$$

Define the actual band operator and its exterior Fourier energy by

$$
(B_9f)(u)=\int_{-a}^a
\frac{\sin(256(u-v))}{\pi(u-v)}f(v)\,dv,
\qquad
\mathcal E_9(f)=\frac1{2\pi}\int_{|t|>256}|F_f(t)|^2\,dt,
$$

with kernel value $256/\pi$ on the diagonal. Plancherel gives $0\preceq B_9\preceq I$ and $\mathcal E_9(f)=\langle f,(I-B_9)f\rangle$ for every $f\in\mathcal H$.

In B.1, the Fourier-derivative bound for a unit vector becomes $|F_f^{(j)}(t)|\le a^j\sqrt{2a}<2a^j$. It differentiates $F_f$ in frequency; it requires no derivatives of $f$. The fixed frequency band, the $N=4096$ exterior nodes with spacing $h=1/32$, their distance bound $768$, and the Lagrange basis sum $<2^{24570}$ do not depend on the support width. The changed interpolation remainder is controlled by

$$
\frac{3\cdot768a}{4096}<\frac{99}{160}<\frac58,
\qquad
\frac{2(768a)^{4096}}{4096!}
<2(5/8)^{4096}<2^{-2047}<1/32.
$$

The middle power bound uses $(5/8)^2<1/2$. Thus the source's real-phase interpolation argument still gives, when $\mathcal E_9(f)<1/2$,

$$
\frac1{16}<16\sqrt{\mathcal E_9(f)}\,2^{24570}+\frac1{32},
\qquad
\sqrt{\mathcal E_9(f)}>2^{-24579}.
$$

The other energy case is immediate. Consequently this source-proof application supplies the actual new-window bounded-operator input

$$
I-B_9\succeq\delta I,\qquad
\delta=2^{-49158},\qquad
S_9=I-B_9-\delta I,\qquad 0\preceq S_9\preceq I.
\tag{A5}
$$

This conclusion covers the entire complex Hilbert space. The exterior Gamma-weighted form used below is finite on the original smooth legal domain; its bounded comparison (A5) does not assert finiteness of that weighted integral for arbitrary $L^2$ vectors. This is an application of the inspected proof with a new remainder comparison, not a new uncertainty principle or a kernel-verified declaration.

## Positive tail compensation at the new width

At this same $a=\log3$, define the newly normalized modes and filtered vectors

$$
v_{0,9}(u)=(2a)^{-1/2},\qquad
v_{1,9}(u)=\sqrt{3/(2a)}\,u/a,\qquad
h_{j,9}=S_9v_{j,9},\qquad
e_j=\langle v_{j,9},(I-B_9)v_{j,9}\rangle.
$$

The exterior-weight estimate in B.2 uses only $|t|\ge256$ and the background $7/2$, so it supplies $T_{{\rm tail},9}(f)\ge C\mathcal E_9(f)$ with $C=123/1280>1/16$. This is the source's actual exterior integral, with all poles, contributing prime powers and the central Gamma band retained elsewhere in $Q$.

B.3's normalized Fourier integrals, evaluated with $c_{\rm band}=256a$, supply independent lower and upper bounds:

$$
\frac{c_{\rm band}-1}{\pi c_{\rm band}^2}\le e_0
\le\frac{c_{\rm band}+1}{\pi c_{\rm band}^2},\qquad
\frac{3(c_{\rm band}-2)}{\pi c_{\rm band}^2}\le e_1
\le\frac{3/c_{\rm band}+6/c_{\rm band}^2+2/c_{\rm band}^3}{\pi}.
$$

All four envelopes decrease on $[272,282]$. Using the source's $157/50<\pi<22/7$, the lower envelopes at $282$ and upper envelopes at $272$ give

| Direction | Lower bound for $e_j$ | Upper bound for $e_j$ | Required upper comparison |
|---|---:|---:|---|
| $j=0$ | $1967/1749528$ | $6825/5807744$ | $81e_0<C$ |
| $j=1$ | $245/72897$ | $2794825/789853184$ | $27e_1<C$ |

Both lower bounds exceed $2^{-11}>\delta$. Thus $e_j-\delta>0$ is established independently of the upper estimates. Reflection commutes with $S_9$, making $h_{0,9}$ even, $h_{1,9}$ odd and $\langle v_{0,9},S_9v_{1,9}\rangle=0$. The source's complex square completion in the positive form of $S_9$ therefore applies:

$$
\langle f,S_9f\rangle\ge
\sum_{j=0}^1\frac{|\langle h_{j,9},f\rangle|^2}{e_j-\delta}.
$$

Since $C/(e_0-\delta)>81$, $C/(e_1-\delta)>27$ and $C\delta>\delta/16$, this gives the actual new-window tail input

$$
\boxed{
T_{{\rm tail},9}(f)\ge\tau_9\|f\|^2+\langle f,U_9f\rangle,
\quad
\tau_9=2^{-49162},\quad
U_9=81|h_{0,9}\rangle\langle h_{0,9}|
+27|h_{1,9}\rangle\langle h_{1,9}|,
}
\tag{A6}
$$

for every $f\in C_c^\infty((-a,a);\mathbb C)$. On even tests the odd contribution vanishes. The displayed constants match the old calibration because the new parameter bounds justify them, while $B_9$, the modes and both filtered vectors are new-width objects. This is a paper application of the inspected analytic proof, independently reviewed; it is not a reproduced numerical certificate, a new kernel theorem or positivity of the complete form.

The same upper envelopes give $\|h_{0,9}\|<1/29$ and $\|h_{1,9}\|<3/50$, since $S_9^2\preceq S_9$ implies $\|h_{j,9}\|^2\le e_j-\delta$. These norm bounds do not provide finite-column approximation errors for the new vectors.

This exact scalar replay checks only the new parameter comparisons. Its logarithm and $\pi$ enclosures are the cited analytic inputs; it does not reexecute the original finite matrices or prove the analytic interpolation and square-completion suppliers.

```python
from fractions import Fraction as F

log3_lo, log3_hi = F(1098612, 10**6), F(1098613, 10**6)
assert F(17, 16) < log3_lo < log3_hi < F(11, 10)
assert F(272) < 256 * log3_lo < 256 * log3_hi < F(282)
ratio = F(3 * 768, 4096) * F(11, 10)
assert ratio == F(99, 160) < F(5, 8)
assert F(5, 8)**2 < F(1, 2)

band_lo, band_hi = F(272), F(282)
pi_lo, pi_hi, C = F(157, 50), F(22, 7), F(123, 1280)
lower = [(band_hi - 1) / (pi_hi * band_hi**2),
         3 * (band_hi - 2) / (pi_hi * band_hi**2)]
upper = [(band_lo + 1) / (pi_lo * band_lo**2),
         (3 / band_lo + 6 / band_lo**2 + 2 / band_lo**3) / pi_lo]
assert lower == [F(1967, 1749528), F(245, 72897)]
assert upper == [F(6825, 5807744), F(2794825, 789853184)]
assert all(value > F(1, 2**11) for value in lower)
assert 49158 > 11
assert C > F(1, 16)
assert 81 * upper[0] < C and 27 * upper[1] < C
assert upper[0] < F(1, 29**2) and upper[1] < F(9, 50**2)
for j in range(2):
    print(j, lower[j], upper[j])
```

## The actual even projection at $c=9$

The existing Appendix C projection and block-error formulas can be applied at the new width after checking their parameter dependencies. This supplies explicit projection, cross and complementary-block inputs for (A4); the retained sign still requires proof.

Let $P_N$ be the full complex Legendre projection onto degrees below $N=448$. On the even Hilbert space take its restriction $P$ and the orthonormal embedding $E$ with columns

$$
E_j(u)=\sqrt{\frac{4j+1}{2a}}P_{2j}(u/a),\qquad 0\le j<224,
\qquad a=\log3,
$$

where $P_{2j}$ is the standard Legendre polynomial. Thus $P=EE^*$ is the actual even projection. The same ellipse of radius $3/2$ has imaginary semiaxis $5/12$. Appendix C's Chebyshev and best-approximation estimate, with the new width, gives

$$
\sup_{|t|\le256}\|(I-P_N)e^{itu}\|^2
\le72a\exp((640/3)a)(2/3)^{896}
<\frac{396}{5}(68/25)^{235}(2/3)^{896}<2^{-178}.
\tag{A8}
$$

Here $a<11/10$, $(640/3)(11/10)=704/3<235$ and the source's $e<68/25$ justify the outward comparison; the last step is exact rational arithmetic. Use $r=2^{-89}$, rather than the old-width $2^{-95}$. On the even space the band vectors are $w_t=\Pi_{\rm even}e^{itu}=\cos(tu)$, so

$$
\|(I-P)w_t\|\le\|(I-P_N)e^{itu}\|<r,
\qquad \|w_t\|\le\sqrt{2a}<3/2.
$$

This does not assert a small residual for $e^{itu}$ under the even projection on the full Hilbert space.

The source pole estimate also has explicit width conditions. They remain valid: $a/2<1$, $e^{a/2}<2$ and $\sqrt{2a}<3/2$. Degree-$447$ Taylor approximation of $a_\pm(u)=e^{\pm u/2}$ gives $\|(I-P_N)a_\pm\|<3/448!$ and $\|a_\pm\|<3$. The same rank-one difference estimate therefore yields

$$
\|K_{\rm pole}-P_NK_{\rm pole}P_N\|
<36/448!\le36/2^{447}<2^{-440}=:p.
$$

Restriction gives this upper allowance on the even space. Its pole operator is $2|\cosh(u/2)\rangle\langle\cosh(u/2)|$, hence positive there. The pole allowance $p$ is an upper-error input, not a negative-complement charge.

For the actual $V_9=K_9+U_9$, put $R_9=V_9-PV_9P$. The source's support-independent band-weight input is

$$
\kappa=\frac1{2\pi}\int_{-256}^{256}|A(t)-7/2|\,dt<896.
$$

The rank-one band integral and (A8) bound its cross block by $1344r$ and its complementary norm by $896r^2$. Since $v_{0,9}\in\operatorname{ran}P$, the source's Cauchy--Schwarz and Plancherel estimate gives $\|(I-P)h_{0,9}\|<10r$. Thus the actual even tail cross block is bounded by $(810/29)r<28r$, and its complementary norm by $8100r^2$. The pole and tail complementary blocks are both positive. Consequently the following source-proof application pays the actual even blocks:

$$
\|(R_9)_{10}\|<1372r+p,\qquad
(R_9)_{11}\succeq-896r^2I,\qquad
\|(R_9)_{11}\|<8996r^2+p.
\tag{A9}
$$

The positivity of the even pole is used only in the lower complementary bound. Its upper allowance remains in the cross and norm bounds. These bounds cover the entire complement inside the even Hilbert space; they do not assert an odd-sector result or supply the finite sign in (A4).

For this common embedding, (A4) can use $e=1372r+p$, $n=896r^2$ and $h=8996r^2+p$, with $n<1/2<4/5$. The source's sharper prime input $m_*=264/325$, $b_*=2011/325$ can also be used directly in its general equations (18)--(22). The actual finite $J_9,D_9$, an upper matrix bound for $G_9$, their directed source errors, and the resulting finite sign test remain unpaid. The ordinary compression $E^*M_9E$ is an upper bound for $G_9^{-1}$, so it cannot replace a lower bound for that inverse compression. The prime-coupling term $D_9$ does not vanish merely because the retained space is finite-dimensional. A positive floating compression would not discharge these obligations.

The following exact scalar replay checks the new ellipse, width and coefficient comparisons. It uses the source analytic suppliers above and does not prove those suppliers or reconstruct a numerical certificate.

```python
from fractions import Fraction as F

assert F(396, 5) * F(68, 25)**235 * F(2, 3)**896 < F(1, 2**178)
assert F(68, 25)**11 < 2**20  # e^(a/2) < 2 for a < 11/10
assert F(22, 10) < F(9, 4)   # sqrt(2a) < 3/2
assert F(810, 29) < 28
r, p, m = F(1, 2**89), F(1, 2**440), F(264, 325)
e, n, h = 1372*r+p, 896*r*r, 8996*r*r+p
assert 896 + 8100 == 8996
assert 1344 + 28 == 1372
assert n < F(1, 2) < F(4, 5) < m
print('new-width band, even block and pole parameter comparisons passed')
```

## Reusing the support-independent Gamma moments

Appendix C.1 supplies the scalar moments

$$
\vartheta_q=\frac{256}{\pi}\int_0^1x^{2q}(A(256x)-7/2)\,dx,
\qquad 0\le q\le1023.
$$

Their definition contains no support half-width. The release packet `w200-pub-2026-09-14/reproduction/release-run/certificates/moments.json` has SHA-256 `f8cb5c681a22755b980d2e98d781353fe9ce058fe33eb8a7753585e2c52b2f93`, matching the pinned `frozen-manifest.json`. Its 1,024 ordered rows all have `hi-lo=3` on the $2^{-1024}$ grid. Thus the packet midpoints are $\widehat\vartheta_q=(\mathrm{lo}_q+\mathrm{hi}_q)/2^{1025}$. The packet records the common band $256$ and background $7/2$; its metadata also records the original $L=17/16$, which is absent from the moment formula and is not a width to retain in the new kernel.

The small [reviewer-materials archive](https://github.com/luciferyu666/certified-weil-positivity/releases/download/v1.0-mcom-submission/w201-reviewer-materials.zip) has SHA-256 `e5547b885d3df9113895877032ba861235adb159cd5b816c9d9f6080d22fbf41` and contains that manifest. Member size and SHA-256 were checked after selective retrieval of the moment packet; the full large archive hash was not checked. These are data-identity and format checks. The mathematical premise that every interval contains its moment, and hence $|\vartheta_q-\widehat\vartheta_q|<2^{-1023}$, is the author's Appendix C.1 claim. Its producer and oracle were not reexecuted here. The packet is read-only research input and is not redistributed in this repository.

## A new-width kernel from the same scalar input

Assuming the moment containment just specified, Appendix C.2 applies with the actual $a=\log3$. Put $z=512a<563$ and define

$$
k_{0,9}(2ay)=\sum_{q=0}^{1023}
\frac{2a^{2q}+(-1)^qz^{2q}\widehat\vartheta_q}{(2q)!}y^{2q}.
\tag{A10}
$$

This constructs a new kernel; it does not rescale the author's old matrix. On $|y|\le1$, the moment replacement costs less than $2^{-1023}\cosh563<2^{-210}$, because $(68/25)^{563}<2^{813}$ and $e<68/25$. The band absolute-weight input $\kappa<896$ and $2\cosh a=10/3<4$ bound the exact-moment Taylor remainder by

$$
914\frac{563^{2048}}{2048!}<2^{-758}.
$$

Indeed $(68/25)563/2048<3/4$, so the same factorial argument as Appendix C.2 applies. Consequently the full kernel and convolution operators obey the conditional bounds

$$
\sup_{|x|\le2a}|k(x)-k_{0,9}(x)|<2^{-209},
\qquad \|K_9-K_{0,9}\|<2a\,2^{-209}<2^{-207}.
\tag{A11}
$$

These bounds are independent of retained dimension. The source Binet remainder is already paid inside its moment intervals and is not subtracted again.

For the actual band operator, use its new-width polynomial

$$
b_{0,9}(2ay)=\frac{256}{\pi}\sum_{q=0}^{1023}
\frac{(-1)^qz^{2q}}{(2q+1)!}y^{2q}.
$$

The sinc remainder and the same outward comparison give

$$
\|B_9-B_{0,9}\|
\le\frac{z^{2049}}{\pi\,2049!}<2^{-768}.
\tag{A12}
$$

Thus $h_{0,9}^{(0)}=(I-B_{0,9}-\delta I)v_{0,9}$ approximates the actual filtered vector with norm error less than $2^{-768}$. Since $\|h_{0,9}\|<1/29$, its rank-one update error is at most $81(2\|h_{0,9}\|2^{-768}+2^{-1536})<2^{-765}$. Together with (A11), a matrix assembled from $K_{0,9}+81|h_{0,9}^{(0)}\rangle\langle h_{0,9}^{(0)}|$ has analytic operator error less than $2^{-206}$, before paying its own directed arithmetic and center rounding. This is conditional source-input reuse and new-width assembly, not a reproduced author certificate, a finite sign test or a kernel-verified result.

The needed scalar comparisons can be replayed without regenerating any moment:

```python
from fractions import Fraction as F

assert 512 * F(1098613, 10**6) < 563
assert F(68, 25)**563 < 2**813
assert F(68, 25) * 563 / 2048 < F(3, 4)
assert F(68, 25) * 563 / 2049 < F(3, 4)
assert F(3, 4)**4 < F(1, 3)
assert 3**512 > 2**768 and 914 < 2**10
assert F(11, 5) * F(1, 2**209) < F(1, 2**207)
assert 81 * (F(2, 29) * F(1, 2**768) + F(1, 2**1536)) < F(1, 2**765)
print('new-width kernel and actual filtered-band allowances passed')
```

## The remaining retained-matrix consumer at $c=9$

The source's Certification Theorem, section 6, equations (17)–(22), now has a legitimate prime-block input $m=4/5$, $b=31/5$ at this new window. In particular $M_9$ is boundedly invertible and $\|M_9^{-1}\|\le5/4$. The same already evaluated bound (A3), before rounding, also permits $m_*=264/325$, $b_*=2011/325$ and $\|M_9^{-1}\|\le325/264$; these are parameter substitutions, not another prime-block calculation. The conservative parameters below suffice to state the remaining obligation.

On the actual interval $(-\log3,\log3)$, the compact self-adjoint operator $K_9$ has the source's kernel

$$
k(u-v)=2\cosh((u-v)/2)
+\frac1{2\pi}\int_{-256}^{256}(A(t)-7/2)e^{it(u-v)}\,dt.
$$

Together with the prime-block decomposition and the now supplied tail input (A6), this gives

$$
Q(f)\ge2^{-49162}\|f\|^2+
\langle f,(M_9+K_9+U_9)f\rangle
\quad\bigl(f\in C_c^\infty((-\log3,\log3);\mathbb C)\bigr).
\tag{A7}
$$

The sign of the bounded term in (A7) is not established. Use the same actual interval, orthonormal retained embedding $E$ and projection $P=EE^*$ throughout. Reflection invariance permits restricting **all** operators, norms and complements to the even Hilbert space for the existing even-test RH route. In that space $U_9=81|h_{0,9}\rangle\langle h_{0,9}|$; the even pole contribution is also nonnegative, but the central Gamma band remains payable. Put $V_9=K_9+U_9$, $J_9=E^*V_9E$, $R_9=V_9-EJ_9E^*$ and

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

This condition would imply $M_9+V_9\succeq0$, and (A7) would then give $Q(f)\ge2^{-49162}\|f\|^2$ on the legal even tests in this window when all objects are restricted to the even space. It is an application of the published block criterion, not an established inequality (A4). The actual entries of $K_9$ and the filtered-vector columns, their directed source errors, the inverse-compression bound and the finite sign test remain payable. The tail input is supplied by (A5)–(A6), and the explicit even embedding has its cross and complementary-block allowances in (A8)–(A9). No retained matrix or approximation error from the $17/16$ certificate has been transported to $\log3$; the matching tail numbers have their separate parameter proof above. Using another retained basis requires identifying the same form and transporting all these objects together. Even a completed $c=9$ sign test would still leave the subsequent cofinal support layers required for RH.

## A common 256-mode consumer

For an actual assembly using 256 even Legendre columns, take $E_j(u)=\sqrt{(4j+1)/(2a)}P_{2j}(u/a)$, $0\le j<256$, and redefine $P,J,R,A,B,G,D$ together with this embedding. This is distinct from the 224-mode instance above. The kernel bounds (A10)–(A12) are dimension-independent and remain applicable; its projection allowances must be calculated for the new space.

The Bernstein ellipse of parameter $2$ has imaginary semiaxis $3/4$. Degree-$511$ Chebyshev truncation of $\cos(tax)$ is even, so its degree is at most $510$ and it belongs to this retained space. The coefficient tail gives

$$
r:=\sup_{|t|\le256}\|(I-P)\cos(tu)\|
\le\sqrt{2a}\,e^{192a}2^{-510}<2^{-200}.
$$

Here $\sqrt{2a}<3/2$ and $(3/2)(68/25)^{212}<2^{310}$ prove the last outward comparison. Taylor truncation of $\cosh(u/2)$ through degree $510$ gives $p_\perp:=\|(I-P)\cosh(u/2)\|<3/512!<2^{-509}$. Using $\|h_{0,9}\|<1$, the same band, pole and tail estimates as (A9) give

$$
\|R_{10}\|<2154r+4p_\perp,
\qquad R_{11}\succeq-896r^2I,
\qquad \|R_{11}\|<8996r^2+2p_\perp^2.
$$

Thus $e=2^{-188}$, $n=2^{-390}$ and $h=2^{-386}$ are valid conservative allowances for this common embedding. With $m=264/325$ and $\theta=\chi=1$, the source's coefficients satisfy $\alpha<2^{-187}$ and $\beta<2^{-186}$. This is another source-proof parameter application, with no finite sign inferred from the smaller projection error.

Section 4, equation (11), supplies the inverse-compression upper bound without knowing the target sign. For any trial matrix $X$, choose $\mu=4/5<m$ and put

$$
\mathcal W_\mu(A,B;X)
=X+X^*-X^*AX+\mu^{-1}(I-AX-X^*A+X^*BX).
$$

The source residual identity gives $\mathcal W_\mu(A,B;X)\succeq G$. If $\|X\|\le s$ and Hermitian centers have errors $\varepsilon_A,\varepsilon_B$, then

$$
W=\mathcal W_\mu(A_0,B_0;X)
+\left[(s^2+2s/\mu)\varepsilon_A+(s^2/\mu)\varepsilon_B\right]I
\succeq G\succ0.
$$

Consequently $W^{-1}\preceq G^{-1}$. In particular, the direction is suitable for a sufficient lower comparison. With $D_0=B_0-A_0^2$, $b=2011/325$ and $\varepsilon_D=\varepsilon_B+(2b+\varepsilon_A)\varepsilon_A$, the new finite target is

$$
W^{-1}+J_0-\varepsilon_JI-2^{-187}I
-2^{-186}(D_0+\varepsilon_DI)\succeq0.
\tag{A13}
$$

This condition is not established. All three centers and their errors must belong to the same actual 256-mode embedding. In particular, $B_0$ must approximate $E^*M_9^2E$, rather than $A_0^2$; clipping occurs before composing the shifts. The kernel analytic allowance $2^{-206}$ above contributes to $\varepsilon_J$ only under the stated author-moment premise, and arithmetic error must still be added. Source positivity of the original window does not settle (A13).

```python
from fractions import Fraction as F

assert F(3, 2) * F(68, 25)**212 < 2**310
r, p = F(1, 2**200), F(1, 2**509)
e, n, h = F(1, 2**188), F(1, 2**390), F(1, 2**386)
assert 2154*r + 4*p < e
assert 896*r*r < n and 8996*r*r + 2*p*p < h
m = F(264, 325)
assert e + 2*e*e/(m-n) < F(1, 2**187)
assert (e+n)/m**2 + 2*h*h/(m**2*(m-n)) < F(1, 2**186)
print('common256-mode projection and consumer allowances passed')
```
