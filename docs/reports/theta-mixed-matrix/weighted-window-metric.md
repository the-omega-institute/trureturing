# The original variance metric in the screw-kernel coordinates

The [theta ground-transform identity](../../../Library/Weil/lagarias2004li.md#mixed-nullity-and-the-theta-weighted-even-weil-interface)
and Suzuki's derivative pairing already supply the change of variables.
The remaining estimate must retain the original variance, including its
mean subtraction. This note gives that parameter map and a sufficient
cofinal target. It supplies neither the target estimate nor an additional
numerical margin.

## Reuse the source representation

Let $\Phi$ be the original positive even theta kernel, and retain

$$
d\nu(x)=\rho(x)\,dx,
\qquad \rho(x)=2\Phi(x)\cosh(x/2),\qquad \nu(\mathbb R)=1.
$$

Write $D=E_\Gamma+E_{\rm prime}$ for the original jump form. The cited
ground-transform application, with its mixed-nullity and cutoff premises,
gives for even complex $h\in C_c^\infty(\mathbb R)$

$$
Q_W(\Phi h)=D(h)-\tfrac12\operatorname{Var}_\nu(h). \tag{WM1}
$$

Suzuki, [arXiv:2206.03682v4](https://arxiv.org/html/2206.03682v4),
Proposition 3.1, equation (3.8), supplies
$Q_W(f)=\langle G_g f',f'\rangle$ on compact smooth tests.
Here the source's real continuous even $g$ has screw kernel

$$
G_g(x,y)=g(x-y)-g(x)-g(-y)+g(0).
$$

The derivative has zero Lebesgue integral, so the last three terms
vanish in the quadratic pairing. Define $\mathcal G_L$ as convolution
by this same $g$, restricted to $(-L,L)$ and compressed to odd
$L^2(-L,L;dx)$ functions. No positivity assumption is made about it.
For even $f\in C_c^\infty(-L,L)$ the source identity becomes

$$
Q_W(f)=\langle\mathcal G_L f',f'\rangle. \tag{WM2}
$$

The version history dates v4 to 30 May 2023; the served versioned HTML
also displays a manuscript date of 24 August 2026. The numbered locator
above refers to that inspected HTML. This note reuses the identity and
does not independently reprove Suzuki's source theorem.

## Transport the variance without changing the ground subtraction

On the odd space define

$$
(R_Lu)(x)=\int_{-L}^x u(t)\,dt,
\qquad
w(x)=\frac{2\cosh(x/2)}{\Phi(x)},
\qquad \ell(x)=2\cosh(x/2).
$$

An odd $u$ has zero integral; $R_Lu$ is even and belongs to
$H_0^1(-L,L)$. For the actual test $f=\Phi h$ put $u=f'$.
Then $R_Lu=f$, and direct substitution in the original variance gives

$$
\begin{aligned}
b_L(u)&=\int_{-L}^L w(x)|R_Lu(x)|^2\,dx
-\left|\int_{-L}^L\ell(x)R_Lu(x)\,dx\right|^2\\
&=\operatorname{Var}_\nu(h). \tag{WM3}
\end{aligned}
$$

Equivalently, with $\eta_L=R_L^*\ell$, its bounded self-adjoint
operator on the odd space is

$$
B_L=R_L^*M_wR_L-|\eta_L\rangle\langle\eta_L|. \tag{WM4}
$$

All weights are bounded on a fixed window, and $R_L$ is bounded
from $L^2$ to $H_0^1$. The rank-one term is the exact original
$\nu$-mean subtraction; zero Lebesgue mean of $u$ does not remove it.
Combining (WM1)--(WM3) gives, on the original compact smooth tests,

$$
D(h)-c\operatorname{Var}_\nu(h)
=\left\langle
\left[\mathcal G_L+(\tfrac12-c)B_L\right]u,u
\right\rangle. \tag{WM5}
$$

This uses zero extension of the compact test, rather than periodization.
The full prime, Gamma and pole contributions remain jointly represented
by $\mathcal G_L$. The long jump edges outside the support, already
accounted for in (WM1), are not deleted.

## The estimate that would reach one-half

A sufficient remaining obligation is to produce

$$
L_j\longrightarrow\infty,\qquad \varepsilon_j\ge0,
\quad\varepsilon_j\longrightarrow0,
\qquad
\mathcal G_{L_j}+\varepsilon_j B_{L_j}\succeq0
\quad\hbox{on all odd }L^2(-L_j,L_j). \tag{WM6}
$$

For each fixed even compact smooth $h$, its support lies in every
sufficiently large window. Applying (WM5) there and taking the limit
would give $D(h)\ge\operatorname{Var}_\nu(h)/2$. The existing minimal
form closure and bounded variance then extend that inequality to the
unchanged original domain. With the existing even Weil identification,
this is the RH-strength endpoint; (WM6) remains unproved.

A FIB support resolution may choose
$L_j=\log F_{3j+3}$, with $F_1=F_2=1$. These windows exhaust compact
supports. The five-pattern address rules do not supply the relative
operator inequality in (WM6), or replace the actual $\nu$ by interval
length weights.

The [fixed whole-form bound at $c=0.42$](actual-coupling.md) is another
estimate for this original model. Window exhaustion in (WM6) and a
fixed global subtraction parameter have different quantified scopes;
neither is silently substituted for the other.

## Diagnose loss from an unweighted scalar transfer

Let $m_L=\nu((-L,L))<1$. For $h=R_Lu/\Phi$, Cauchy--Schwarz in the
same restricted measure gives

$$
b_L(u)\ge(1-m_L)\int_{-L}^Lw(x)|R_Lu(x)|^2\,dx.
$$

On zero-mean functions let $K_L=(-\Delta_N)^{-1}$ denote the Neumann
inverse. Integration of $-v''=u$ with $v'(\pm L)=0$ gives
$v'=-R_Lu$, hence
$\langle K_Lu,u\rangle=\|R_Lu\|_2^2$. Therefore

$$
B_L\succeq\beta_LK_L,
\qquad
\beta_L=(1-m_L)\min_{|x|\le L}w(x)>0. \tag{WM7}
$$

If an independently justified bound supplies
$\mathcal G_L\succeq-r_LK_L$ with $r_L\ge0$, then (WM7) gives

$$
\mathcal G_L+(r_L/\beta_L)B_L\succeq0. \tag{WM8}
$$

This scalar construction of a uniform relative window allowance requires
$r_{L_j}/\beta_{L_j}\to0$. Absolute $r_{L_j}\to0$ alone does not
guarantee that converted allowance tends to zero, since
$\beta_L\le(1-m_L)w(0)$ and the denominator itself tends to zero.
Failure of this scalar sufficient bound does not refute (WM6).
Keeping the exact rank-one-corrected $B_L$ leaves room for a stronger
relative comparison without that scalar loss.

This ratio is not necessary for the RH target. The
[fixed-test limit and pole-cancelled window](centered-window.md) explain
why an actual absolute lower comparison with $r_{L_j}\to0$ already
suffices on every fixed compact test, without the scalar conversion.
The same note transports the published pole-pair constraint to the
original theta mean; its constrained metric has a uniform scalar floor.
Neither argument supplies the outstanding arithmetic lower comparison.

## Even the optimal scalar transfer vanishes

The loss in (WM7) is structural. For actual compact primitives $f=R_Lu$,
the best scalar comparison $B_L\succeq\beta K_L$ is the infimum of

$$
\frac{\displaystyle\int_{-L}^Lw|f|^2
-\left|\int_{-L}^L\ell f\right|^2}
{\displaystyle\int_{-L}^L|f|^2}. \tag{WM9}
$$

Every even compact smooth $f$ is an actual test $f=\Phi h$, since
$\Phi$ is smooth and positive. These primitives are dense in even
$L^2(-L,L)$, and the numerator is a bounded form on each fixed window.
Thus (WM9) has the same infimum as $M_w-|\ell\rangle\langle\ell|$
on that even space. Density suffices; the primitive map need not be
onto all of $L^2$.

Apply the standard rank-one multiplication secular formula to these
specific weights. With $w_{\min}=\min_{[-L,L]}w>0$, the optimal
constant is the unique $\beta_L^*\in(0,w_{\min})$ satisfying

$$
\int_{-L}^L\frac{\ell(x)^2}{w(x)-\beta_L^*}\,dx=1. \tag{WM10}
$$

The left side at zero is the original mass $m_L<1$. It increases
strictly and diverges as $\beta\uparrow w_{\min}$: positivity of
$\ell$ and smoothness of $w$ give a logarithmically divergent lower
integral near a minimum, including a minimum at an endpoint.
The minimizing $L^2$ eigenfunction is proportional to
$\ell/(w-\beta_L^*)$. Its nonzero endpoint traces prevent compact
attainment, but compact smooth $L^2$ approximation preserves the
infimum. No new general spectral theorem is claimed here.

Put $\Delta_L=1-m_L$ and $I_L=\int_{-L}^L\Phi(x)^2\,dx$.
Subtracting the zero-parameter integral in (WM10) gives the exact
parameter identity

$$
\Delta_L=\beta_L^*
\int_{-L}^L\frac{\Phi(x)^2}{1-\beta_L^*/w(x)}\,dx.
$$

Since $w\ge w_{\min}$, it follows that

$$
\frac{\Delta_L}{I_L+\Delta_L/w_{\min}}
\le\beta_L^*\le\frac{\Delta_L}{I_L}. \tag{WM11}
$$

The independent root characterization gives $\beta_L^*<w_{\min}$
even if the displayed upper estimate exceeds that minimum. Original
theta boundedness and decay give
$I_L\to\|\Phi\|_2^2\in(0,\infty)$ and
$w_{\min}\ge2/\sup_{\mathbb R}\Phi>0$, while $\Delta_L\to0$.
Hence

$$
\frac{\beta_L^*}{\Delta_L}\longrightarrow\frac1{\|\Phi\|_2^2},
\qquad\beta_L^*\longrightarrow0. \tag{WM12}
$$

There is also an actual-test witness: choose the existing admissible
even compact cutoffs $\chi_L$ supported inside exhausting windows,
with $0\le\chi_L\le1$ and $\chi_L\to1$. For
$f_L=\chi_L\Phi$, $u_L=f_L'$,

$$
b_L(u_L)=\operatorname{Var}_\nu(\chi_L)\longrightarrow0,
\qquad
\langle K_Lu_L,u_L\rangle
=\|\chi_L\Phi\|_2^2\longrightarrow\|\Phi\|_2^2>0.
$$

Thus a uniform positive scalar $B_L\succeq\beta K_L$ over unbounded
windows is unavailable even with the optimal constant. This does not
disprove the joint relative estimate (WM6). It supplies no arithmetic
rate for $\mathcal G_L$, cofinal positivity, RH or Robin conclusion.
The derivation reuses the original metric and the standard rank-one
framework; literature priority is not established, and no numerical
theta integral or new Lean declaration is supplied.

The [Suzuki source note](../../../Library/Weil/suzuki2026screw.md) retains
the existing small-window and spectral-limit boundaries. The
[Shi finite-pencil note](../../../Library/Weil/shi2026finitepencils.md)
records a related relative-metric obligation in a different finite model.
Neither supplies (WM6). All identities and implications here are paper
applications with their named premises, without a new general criterion,
priority claim, numerical certificate, Lean result, RH or full Robin proof.
