# Two actual midpoint residual columns

This conditional computation acquires a full-space simultaneous Gram
for two left-piece columns of
[the original J4/J5 interface](../../../Library/Dynamics/clason2021regularization.md#pay-the-finite-remainder-with-the-existing-common-source-certificate).
It retains the original probability measure, physical unitary, negative-edge
metric $\mathcal B=UBU^{-1}$ and source space $N_c$. The
[existing actual-action and derivative transport](theta-common-residual-bounds.md)
are reused on fresh sources. The previously acquired quadratic-input rows
are unused. There is no new generic Gram theorem, Lean certification or
originality claim.

The [producer](theta_profile_residual_gram.py) and
[directed result](theta-profile-residual-gram-result.json) use

$$
G(y)=e^{5y/2-(\pi/2)e^{2y}},\qquad
R_1=0,\quad R_2=\tfrac12,\quad \Delta_1=\Delta_2=\tfrac12,
$$

$$
e_i=\sqrt{\Delta_i}\,Q_0[G(|x|-R_i)],\qquad
\eta_i=0\in N_c,\quad\omega_i=0\in N_c^\perp,\quad
b_i=\mathcal B e_i.
$$

The corresponding coefficient cells are $[-1/4,1/4]$ and $[1/4,3/4]$.
They form a two-column subblock of a possible J4 mesh. Both physical
columns have the inherited original form-domain membership. Zero
witnesses define a baseline; they supply no fitted critical correction.
The complete growing column family, common coefficient map cost,
infinite principal contribution and required signs remain unpaid.

Under the inherited actual-model and numerical-supplier premises, the
result encloses the original cross Gram and constructs one positive
Hermitian upper matrix $G_b$ satisfying

$$
\left\|z_1b_1+z_2b_2\right\|_2^2\le z^*G_bz
\qquad(z\in\mathbb C^2),\qquad
\|G_b\|<0.001698.
$$

The approximate matrix display is

$$
G_b\approx
\begin{pmatrix}
0.0010965052274&-0.0000041913147\\
-0.0000041913147&0.0016973410123
\end{pmatrix}.
$$

The certificate uses the exact dyadic entries in the result, rather than
these rounded displays. Its directed largest-eigenvalue upper allowance
is approximately $0.0016973702487$; both LDL pivots are strictly positive.
The exterior Gram norm allowance is below $1.046\times10^{-73}$.
The interior error norm allowance is approximately $0.0010964206817$
and dominates the enclosure inflation. With the existing $b_0=1/100$,
the J5 conversion for this subblock has coefficient
$b_0^{-1}\sqrt{\|G_b\|}<4.121$ times its coefficient-map norm. This is
a coarse baseline and supplies no vanishing full-family residual,
original half-bound, Robin or RH conclusion.

## Source and real-piece square root

Write $v_0=\sqrt{2\Phi\cosh(x/2)}$, $Uh=v_0h$ and
$h_R(x)=G(|x|-R)/v_0(x)$. Since $B1=0$,

$$
\mathcal BQ_0[G(|x|-R)]=UBh_R.
$$

Thus the action can use the uncentered representative while preserving
the exact centered physical column. On the right radial chart the
existing theta jet supplier gives

$$
\Phi(z)=e^{5z/2-\pi e^{2z}}D_0(z),\qquad
s(z)=e^{5z/4-(\pi/2)e^{2z}}
       \sqrt{\frac{D_0(z)}{2\cosh(z/2)}},\qquad
\Phi h_R=sG(z-R).
$$

The exponential factor is transported before taking the square root.
The slow factor must have strictly positive real part on each accepted
complex box; its principal root agrees with the positive root on the
real line. The original action is split at $s=0$. Each piece fixes the
radial sign of its analytic continuation, and the theta overlap chart
$\Re z>-1/8$ is checked. Invalid boxes return a nonfinite callback and
are subdivided by the existing quadrature. Returned balls contain its
error; the nominal tolerance is not an error certificate.

For the real source evaluation, cancel the shared exponentials first:

$$
h_R(r)=\frac{
\exp\{5r/4-5R/2+(\pi/2)(1-e^{-2R})e^{2r}\}
}{\sqrt{2\cosh(r/2)D_0(r)}}.
$$

The inherited odd jet supplies $\Phi'/\Phi$. The right derivative is

$$
h'_R(r)=h_R(r)
\left[\frac52-\pi e^{2(r-R)}
-\frac{\Phi'(r)}{2\Phi(r)}-\frac14\tanh(r/2)\right].
$$

This right derivative is used on the exact nonnegative real cells.
The even physical column may have a derivative cusp at zero.

## Complete action and spatial tails

Reuse the supplied $C_0$ with
$\Phi(r)\le C_0e^{9r/2-\pi e^{2r}}$ for $r\ge0$. Since
$2\cosh(r/2)\ge e^{r/2}$ and $\cosh(r/2)\le e^{r/2}$,

$$
|\Phi(r)h_R(r)|\cosh(r/2)
\le\sqrt{C_0}e^{-5R/2}e^{5r-\kappa_Re^{2r}},\qquad
\kappa_R=\frac\pi2(1+e^{-2R}).
$$

Let $T_2(a,S)$ be the existing `exponential_integral_upper(2,a,exp(2S))`.
It bounds $\int_S^\infty e^{5r-ae^{2r}}dr$ for $S\ge0$.
For action cutoff $L=5$ and a retained radial point $r<L$, put
$S=L-r$. Both omitted shifted directions are paid by

$$
2\left[|h_R(r)|C_0T_2(\pi,S)
+\sqrt{C_0}e^{-5R/2}T_2(\kappa_R,S)\right].
$$

The whole $M_{1,R}\ge\|h_R\|_{L^1(\nu)}$ uses interval upper sums
of $4|\Phi h_R|\cosh(r/2)$ on $[0,S_x]$, $S_x=5/2$, and four times
the weighted-source tail just displayed. The factor four is the original
folded probability density.

For the full physical exterior, $|Bh_R|\le(|h_R|+M_{1,R})/2$ gives

$$
\int_{|x|>S_x}|Bh_R|^2d\nu
\le e^{-5R}T_2(\pi e^{-2R},S_x)
+\frac{M_{1,R}^2}{2}\,4C_0T_2(\pi,S_x).
$$

The first term uses $|h_R|^2d\nu=G(|x|-R)^2dx$ and
$(a+b)^2\le2a^2+2b^2$. Multiply each column's exterior bound by
$\Delta_i$. The exterior cross Gram is positive and is bounded in
operator order by the sum of these diagonal bounds times identity.

## Joint interior matrix

The original support-gap supplier and derivative bound give, on each
real cell and with $g$ a strictly positive common gap lower bound,

$$
|(Bh_R)'|\le\tfrac12
\left[|h'_R|+\coth(g)(|h_R|+M_{1,R})\right].
$$

A fresh midpoint action ball plus cell half-width times this allowance
encloses the entire cell. The program integrates signed products of
these simultaneous scaled residual balls against
$4\Phi(r)\cosh(r/2)$, retaining the off-diagonal cross entries. A wide
theta exponential ball can cross zero; its density enclosure is
intersected with the known nonnegative real density range.

Let $A$ be the exact symmetric matrix of the interior Gram-ball
midpoints. If $\varepsilon$ is the maximum absolute radius row sum,
the Hermitian error has norm at most $\varepsilon$. If $\tau$ is the
whole exterior trace allowance, then

$$
G_{\rm true}\le A+(\varepsilon+\tau)I.
$$

The result rounds each diagonal addition upward to an exact point dyadic,
checks positive LDL pivots and evaluates the two-by-two largest eigenvalue
formula outward. These steps retain a single common complex coefficient
vector throughout. They do not replace the inherited actual-model,
quadrature, derivative or tail premises.

## Reproduction and scope

The retained result uses Python 3.13.12, python-flint 0.9.0, 192-bit
arithmetic, 128 radial cells and 128 source-L1 cells:

```sh
uv run --offline --no-project --python 3.13 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/theta_profile_residual_gram.py --output /tmp/theta-profile-residual-gram.json
```

The declared runtime must be installed or cached for the offline command.
Source and supplier hashes are recorded in the result. Only existing
polynomial definitions are loaded; older derivative, matrix and
quadratic-input grid producers are not executed.

The default columns and their full-space joint Gram do not certify a
complete J4/A3 family. The
[shared correction report](theta-shared-witness-correction.md) supplies
nonzero primal/dual witnesses for this two-column subblock with a
matching zero control. Convergence of the required growing family and
signs on one common cofinal sequence remain unresolved. The original
infinite principal synthesis is retained.
