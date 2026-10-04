# Fixed-test limits and the pole-cancelled window

The [original weighted metric](weighted-window-metric.md) gives a
sufficient relative window estimate. Its scalar conversion loses the
omitted probability mass. That loss belongs to the conversion; it is
not a necessary error rate for the RH target. A fixed-test limit can
avoid the conversion entirely. The published constrained Weil criterion
also permits a smaller test family, with an explicit parameter map to
the original theta mean.

This note reuses Suzuki's derivative pairing, the original complete
theta form, Connes--Consani's constrained criterion and the existing
minimal-domain cutoffs. It supplies no arithmetic positivity estimate,
new general criterion, priority claim or Lean certification.

## Take the limit on the same fixed test

Keep the original operators $\mathcal G_L,B_L,K_L,R_L$ of
(WM2)--(WM5). Another sufficient obligation is

$$
L_j\longrightarrow\infty,\quad r_j\ge0,\quad r_j\longrightarrow0,
\qquad
\langle\mathcal G_{L_j}u,u\rangle
\ge-r_j\langle K_{L_j}u,u\rangle
\quad\text{for every odd }u\in L^2(-L_j,L_j). \tag{CW1}
$$

Fix one even compact smooth $f=\Phi h$. Once its support lies strictly
inside $(-L_j,L_j)$, its zero-extended derivative $u=f'$ is the same
source at every later stage, and

$$
\langle K_{L_j}u,u\rangle=\|f\|_2^2,\qquad
Q_W(f)=\langle\mathcal G_{L_j}u,u\rangle
\ge-r_j\|f\|_2^2. \tag{CW2}
$$

The norm on the right is fixed. Taking $j\to\infty$ gives $Q_W(f)\ge0$.
Equivalently, the unchanged (WM1) gives
$D(h)\ge\operatorname{Var}_\nu(h)/2$ on compact smooth tests, with
extension to the original even minimal domain by its existing closure.
The original even Weil identification then gives the RH-strength target.
Equation (CW1) remains unproved.

No division by the vanishing scalar $\beta_L$ occurs. The ratio
$r_L/\beta_L\to0$ in (WM8) would supply a vanishing *uniform relative
window allowance*. It is sufficient for that construction; it is not
necessary for the fixed-test conclusion (CW2). Absolute $r_j\to0$
in the actual lower comparison (CW1) already suffices. An approximation
error without the actual lower comparison or its sign does not suffice.

The same distinction holds for a fixed-test error seminorm: a valid
lower comparison $Q_W(f)\ge-r_j S(f)$ with $S(f)<\infty$ fixed for each
admissible $f$ also permits this limit. A changing approximation family
must first supply that comparison for the same test. A finite positive
matrix does not supply it for an omitted infinite complement.

## The published pole constraint is the original theta mean

In the odd Hilbert space, the original adjoint functional is

$$
\eta_L=R_L^*\ell=-4\sinh(x/2),\qquad \ell=2\cosh(x/2). \tag{CW3}
$$

Indeed Fubini gives
$\int\ell R_Lu=4\sinh(L/2)\int u-4\int\sinh(t/2)u(t)dt$;
the first term vanishes because $u$ is odd. Define the codimension-one
space

$$
\mathcal C_L=\left\{u:\int_{-L}^L\ell(x)R_Lu(x)dx=0\right\}
=\eta_L^\perp. \tag{CW4}
$$

For an actual test $f=\Phi h$ this is precisely
$\int h\,d\nu=0$. With the unnormalized transform
$F_f(z)=\int f(x)e^{-izx}dx$, evenness gives

$$
\int\ell f=2F_f(i/2)=2F_f(-i/2).
$$

For the multiplicative test $k(t)=t^{-1/2}f(\log t)$, its usual Mellin
transform is

$$
\widetilde k(z)=\int_0^\infty k(t)t^z\,d^*t
=F_f(i(z-1/2)). \tag{CW5}
$$

Thus the original mean-zero constraint is exactly the pole pair
$\widetilde k(0)=\widetilde k(1)=0$.
The [retained Connes--Consani source](../../../Library/Weil/connesconsani2021archimedean.md#vanishing-constraints-and-the-remaining-semilocal-comparison),
Appendix C, Proposition C.1 of arXiv:2006.13771v1, already supplies a
Weil criterion with these fixed Mellin zeros over all compact supports.
It uses its stated Mellin involution and local-distribution sign.
The following theta application uses the already normalized complete
(WM1)--(WM5), rather than importing its archimedean-only estimate.

On $\mathcal C_L$ the original mean subtraction vanishes *because of
this constraint*, and

$$
\langle B_Lu,u\rangle
=\int_{-L}^L\frac{\ell}{\Phi}|R_Lu|^2
\ge w_*\langle K_Lu,u\rangle,
\qquad w_*:=\frac2{\sup_{\mathbb R}\Phi}>0. \tag{CW6}
$$

The constant is independent of $L$. Zero Lebesgue mean of an odd
$u$ alone would not imply (CW4), or remove the original rank-one term.

## Mean-zero core transport keeps the endpoint target

It is enough to supply the actual comparison in (CW1) only for
$u\in\mathcal C_{L_j}$. For each fixed mean-zero compact smooth $h$,
(CW2) still applies. On this family (CW6) additionally gives the
finite-stage original-variance estimate

$$
D(h)\ge(1/2-r_j/w_*)\|h\|_{L^2(\nu)}^2. \tag{CW7}
$$

The endpoint conclusion extends to the entire centered minimal domain.
To check this domain step, let $h_n$ be even compact smooth approximants
to a centered $h$ in the original form norm. Use the
[existing constant cutoffs](../../../Library/Weil/fukushima2011dirichlet.md#minimal-closure-constants-and-the-even-restriction)
$\chi_R\to1$ in that same norm and choose $R_n\to\infty$. Put

$$
\widehat h_n=h_n-
\frac{\nu(h_n)}{\nu(\chi_{R_n})}\chi_{R_n}. \tag{CW8}
$$

For large $n$, the denominator tends to one, $\nu(h_n)\to0$ and the
cutoff form norms are bounded. Hence $\widehat h_n\to h$ in the form
norm, while every $\widehat h_n$ is compact smooth, even and exactly
centered. The endpoint inequality passes through the closed form.
For arbitrary $h$, apply it to $h-\nu(h)$. Constants belong to this
minimal domain with zero energy, so its energy is $D(h)$ and its
squared norm is $\operatorname{Var}_\nu(h)$.

This does not assume equality with a maximal domain or discard jumps
across a support boundary. A FIB sequence such as
$L_j=\log F_{3j+3}$ exhausts compact supports; its five-pattern addresses
do not supply the outstanding signed comparison on $\mathcal C_{L_j}$.
The inherited high-band supplier (WF6) also remains available, but it
does not estimate this low/whole-window arithmetic form.

## Pole cancellation does not turn an error envelope into a form bound

The stable constant in (CW6) does not make a generic pointwise
exponential error harmless. Consider the real even *generic* kernel

$$
\kappa(t)=\cos(\pi t)\cosh(t/2),\qquad
|\kappa(t)|\le e^{|t|/2}. \tag{CW9}
$$

It is not the actual screw kernel or an approximation asserted for it.
Let $b=1/8$, $\beta(x)=(1-|x|/b)_+$ and $z=\pi+i/2$. Its transform
and norm are

$$
\mathcal B(z)=\frac{2(1-\cos(bz))}{bz^2}\ne0,
\qquad \|\beta\|_2^2=2b/3.
$$

For $r>2$ use the four disjoint translated tents

$$
\begin{aligned}
a_r&=\frac{\cosh(r/2)}{\cosh((r-1)/2)},\\
f_r(x)&=\beta(x-r)+\beta(x+r)
-a_r\bigl(\beta(x-r+1)+\beta(x+r-1)\bigr). \tag{CW10}
\end{aligned}
$$

They are real even compact $H_0^1$ primitives. Exact moment cancellation
gives $F_{f_r}(i/2)=F_{f_r}(-i/2)=0$; their derivatives $u_r=f_r'$ are
odd and lie in $\mathcal C_L$ for $L>r+b$. Disjointness gives
$\langle K_Lu_r,u_r\rangle=2(1+a_r^2)\|\beta\|_2^2$.
The four exponential modes of (CW9) give

$$
\langle\kappa*u_r,u_r\rangle
=\operatorname{Re}\bigl(z^2F_{f_r}(z)^2\bigr),\quad
F_{f_r}(z)=2\mathcal B(z)
\bigl(\cos(zr)-a_r\cos(z(r-1))\bigr). \tag{CW11}
$$

This is a signed real part, not an absolute square. As $r\to\infty$,
$a_r=e^{1/2}+O(e^{-r})$ and
$F_{f_r}(z)=2\mathcal B(z)e^{r/2}e^{-i\pi r}+O(e^{-r/2})$.
Consequently a fixed phase in $r_j=j+\tau$ can make

$$
\frac{\langle\kappa*u_{r_j},u_{r_j}\rangle}
{\langle K_Lu_{r_j},u_{r_j}\rangle}\longrightarrow-\infty. \tag{CW12}
$$

An opposite phase gives positive divergence. Nonzero
$z^2\mathcal B(z)^2$ guarantees both phase choices. Even nonnegative
smooth bumps sufficiently close to the tent give the same nonzero
leading coefficient; the exact ratio in (CW10) still cancels their
pole moments. Thus the obstruction also has compact smooth witnesses.

The [directed producer](centered_envelope.py) and
[saved result](centered-envelope-result.json) select the exact phase
$\tau=35/64$ and check five negative examples and five positive controls
at 192 bits, without a theta, Gamma, prime or old matrix computation.
Some outward enclosures of the negative quotient are

| $r$ | Enclosure of the quotient in (CW12) |
|---|---:|
| $227/64$ | $[-31.80327,-31.80325]$ |
| $419/64$ | $[-691.00178,-691.00175]$ |
| $803/64$ | $[-279871.5540,-279871.5538]$ |

These finite checks support the implementation; the exponential-moment
calculation supplies the unbounded-family argument. Scaling $\kappa$
by any fixed positive error allowance preserves the obstruction.
It invalidates a universal transfer from that pointwise envelope to a
bounded or vanishing negative $K_L$ allowance, even after pole
cancellation. It is not a negative direction of the arithmetic kernel,
a failure of the true weighted relative bound, or an RH counterexample.
The original $B_L$ weights on far-tail witnesses are different from
this unweighted denominator.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/centered_envelope.py
```

The program is project-authored and uses python-flint/FLINT. Invalid
precision or phases, nonfinite enclosures and uncertified example signs
reject. The actual signed arithmetic estimate, cofinal original-form
positivity, RH and full Robin remain unresolved. The known criteria and
Fourier-mode methods are reused; no literature priority is claimed.

The [signed arithmetic application](signed-discrepancy-window.md) keeps
the actual prime-minus-continuum measure and its cross terms. Its
fixed-row tail and finite-head band allowances are more specific inputs
to a coupling budget, with the original all-test sign and common
cofinal estimate still unproved.
