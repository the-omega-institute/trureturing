# A full-Gamma periodization allowance on the same high family

The specified trial vectors remain $Z=QH_{1024,64}EB$ and $g=Qv_0$.
This supplier concerns the full Gamma symbol acting on
$f=su$, $u=(g,Z)a$, after those vectors are defined. It reuses the
original jump series in
[fukushima2011dirichlet.md](../../../Library/Weil/fukushima2011dirichlet.md),
the [strip supplier](strip-root.md), weighted Plancherel, Fourier
inversion and exponential kernels. It is a model application, not a
new general theorem, evaluated action or Lean certification.

The full logarithmic symbol is unbounded. The divergent full-series
analogue of the finite $M_J$ cannot be substituted into the
[finite-trial action allowance](local-high.md).

## Weighted real envelopes from the existing strip

Keep $\delta=1/8$, and let $U_\delta$ be (SR13) for the same five
coefficients. The two line bounds give
$\int e^{2\delta|\xi|}|\widehat u(\xi)|^2d\xi
\le2U_\delta^2\|a\|^2$. Fourier inversion and Cauchy–Schwarz yield

$$
\|u^{(r)}\|_\infty\le L_r\|a\|,
\qquad L_r=U_\delta
\sqrt{\frac{2(2r)!}{\pi(2\delta)^{2r+1}}},\quad r=0,1,2.
\tag{FG1}
$$

Use the saved real (WC2) envelopes
$|s^{(j)}(x)|\le K_je^{-be^{2|x|}}$, $b=3/8$, $j=0,1,2$.
For coefficient norm1, Leibniz gives
$|f''(x)|\le K_{f,2}e^{-be^{2|x|}}$ with
$K_{f,2}=K_2L_0+2K_1L_1+K_0L_2$.
Since $1/(4b)<1$, the weighted supremum of this exponential is
$e^{-b}$, and substitution $t=e^{2|x|}$ gives

$$
\begin{aligned}
\|e^{|x|/2}f\|_\infty&\le F_0:=K_0L_0e^{-b},\\
\|e^{|x|/2}f''\|_\infty&\le F_2:=K_{f,2}e^{-b},\\
\|e^{|x|/2}f\|_1&\le W_1:=K_0L_0e^{-b}/b.
\end{aligned} \tag{FG2}
$$

The last integral uses $t^{-3/4}\le1$ on $[1,\infty)$.
These bounds are uniform on one coefficient unit ball; separate
maxima are not assumed simultaneously attained.

## Preserve cancellation in the full paired jump

For $a_k=2k+1/2$, the original positive symbol is the limit of

$$
m(\mathsf D)f(x)=\sum_{k\ge0}\int_0^\infty e^{-a_kt}
 [2f(x)-f(x+t)-f(x-t)]dt. \tag{FG3}
$$

Split each integral at1. The near paired second difference is bounded
by $t^2\sup_{|y-x|\le1}|f''(y)|$. The integral comparison gives
$2\sum_k a_k^{-3}\le18$. Its contribution is at most
$18e^{1/2}F_2e^{-|x|/2}$.

The far local term costs
$4e^{-1/2}|f(x)|/(1-e^{-2})$. On $t\ge1$,
$\sum_k e^{-a_kt}\le e^{-t/2}/(1-e^{-2})$. Together with the weighted
$L^1$ bound in (FG2), this bounds the far shifted terms. Consequently

$$
|m(\mathsf D)f(x)|\le C_m e^{-|x|/2},\quad
C_m=18e^{1/2}F_2+
       \frac{4e^{-1/2}F_0+W_1}{1-e^{-2}}. \tag{FG4}
$$

The same estimates imply pointwise and $L^1$ absolute convergence.
Passing the finite Fourier identities to the limit identifies the
paired series with the full original symbol. Cancellation in the
near paired jump pays the infinite sum; no infinite local
multiplication constant is introduced.

## Periodization, folding and omitted physical samples

Take $R=128$, $h=1/256$, $X=4$, $\Delta=2\pi/R$ and $\nu=\pi/h$.
Absolute periodization of (FG4) gives a continuous function whose
Fourier coefficients are those of the full periodic action on the
periodized $f$. Those coefficients are absolutely summable by the
existing strip decay. At local outputs $|x|\le X$, the periodization
difference is at most

$$
q_{\rm per}=C_m\frac{2e^{-(R-X)/2}}{1-e^{-R/2}}. \tag{FG5}
$$

The nonunitary input coefficients satisfy
$|\int f(x)e^{-i\xi x}dx|\le B_\delta U_\delta e^{-\delta|\xi|}$.
On folded frequencies, the multiplier difference costs
$2G(|\xi|)$, where $G(t)=4+\tfrac12\log(1+4t^2)$ is (SR14).
Because $G'/G\le1/(4t)$ and $\nu\ge1/(2\delta)$,
$G(t)e^{-\delta t}$ decreases at least at rate $\delta/2$ for
$t\ge\nu$. Thus all folded periodic modes contribute at most

$$
q_{\rm fold}=\frac{4B_\delta U_\delta}R
 \frac{G(\nu)e^{-\delta\nu}}{1-e^{-\delta\Delta/2}}. \tag{FG6}
$$

The finite DFT multiplier has entries bounded by $G(\nu)$, so every
discrete convolution matrix entry has this same bound. For
$U_X=e^{2X}$, monotone physical and omitted lattice $L^1$ tails of $f$
are bounded by $J_f=K_0L_0e^{-bU_X}/(bU_X)$. Deleting all samples
outside $[-X,X]$ from the full periodized input costs at most

$$
q_{\rm del}=G(\nu)J_f/h \tag{FG7}
$$

at lattice outputs. The combined Gamma error, after the outer real
$s$ multiplication, is $A_0(q_{\rm per}+q_{\rm fold}+q_{\rm del})$.
At the saved parameters it is below $6.796\cdot10^{-12}$ on the same
five-generator coefficient unit ball. Numerical input and arithmetic
errors remain separate; this constant does not enclose them.

The [directed program](full_gamma_periodic_bounds.py) records the
suppliers and exact upper dyadics in
[full-gamma-periodic-result.json](full-gamma-periodic-result.json).
This coefficient supplier alone does not supply numerical full actions,
off-lattice $g/Z$ values, mean/prime transport, whole-line output tails
or action/cross blocks. The complete common residual Gram,
projected-ground direction and restricted sign remain unpaid.
No cofinal, Robin, RH or Lean conclusion follows.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/full_gamma_periodic_bounds.py
```

The program is project-authored, uses python-flint/FLINT and copies no
third-party implementation code.

The [off-grid/action interface](off-grid-action.md) transports the
additional prime, mean and continuous projection inputs. The
[actual high-action producer](high-full-action.md) then applies this
full-Gamma allowance to the four saved $Z$ columns and encloses their
whole-line action matrices. It does not supply the low/mixed/common
residual blocks or restricted Schur sign.
