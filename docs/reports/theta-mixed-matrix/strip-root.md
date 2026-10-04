# Original-kernel strip, coherent root and Fourier action tails

This note supplies an original-series input for finite-frequency evaluation
of the [fixed whole-line high trials](high-trials.md). It reuses the source
kernel and evenness in [Romik's equations (1.8)–(1.9)](../../../Library/Analytic/romik2021orthogonal.md)
and classical strip-to-Fourier transport. The explicit relative margin,
root factorization and coefficient bounds below are repository deductions
for this model, with no originality or Lean certification claim.

The retained high vectors remain $Z=QH_{1024,64}EB$ and $g=Qv_0$.
Using the full Gamma symbol in a subsequent action does not change the
finite-$J$ definition of $Z$. The saved periodic screen is not a supplier
of these whole-line vectors or their certified Gram matrices.

## Relative nonvanishing with an overlap

The original kernel, normally convergent on compact subsets of
$|\operatorname{Im}z|<\pi/4$, is

$$
\Phi(z)=\sum_{n\ge1}
 (4\pi^2n^4e^{9z/2}-6\pi n^2e^{5z/2})e^{-\pi n^2e^{2z}}.
$$

Factor its first summand as

$$
\begin{aligned}
L(z)&=2\pi e^{5z/2}(2\pi e^{2z}-3)e^{-\pi e^{2z}},\\
\Phi(z)&=L(z)(1+R(z)),\\
R(z)&=\sum_{n\ge2}n^2
  \frac{2\pi n^2e^{2z}-3}{2\pi e^{2z}-3}
  e^{-\pi(n^2-1)e^{2z}}.
\end{aligned} \tag{SR1}
$$

For $u=e^{2\operatorname{Re}z}\ge u_*>3/(2\pi)$ and
$|\operatorname{Im}z|\le\delta<\pi/4$, the reverse triangle inequality
gives $|2\pi e^{2z}-3|\ge2\pi u-3$. Both
$(2\pi n^2u+3)/(2\pi u-3)$ and the exponential majorant decrease in $u$.
Consequently

$$
|R(z)|\le q(u_*,\delta):=
\sum_{n\ge2}n^2\frac{2\pi n^2u_*+3}{2\pi u_*-3}
 e^{-\pi u_*(n^2-1)\cos(2\delta)}. \tag{SR2}
$$

Take $u_*=e^{-1/4}$ and $\delta_*=1/6$. The elementary bounds
$u_*>3/4$, $\pi>3$ and $\cos(1/3)\ge17/18$ imply
$\pi u_*\cos(1/3)>17/8>2$. Writing $A=2\pi u_*>9/2$, for $n\ge2$,

$$
n^2\frac{An^2+3}{A-3}<3n^4+2n^2\le\frac72n^4.
$$

For $t_n=n^4e^{-2(n^2-1)}$,

$$
\frac{t_{n+1}}{t_n}
\le(3/2)^4e^{-10}<1/1000.
$$

Indeed $e^2>7$ gives $e^6>343$, $e^{10}>16807$, and
$81/(16\cdot16807)<1/1000$. Thus, without a fitted constant,

$$
q(e^{-1/4},1/6)
<\frac{56}{343}\frac{1000}{999}
=\frac{56000}{342657}<\frac16. \tag{SR3}
$$

This proves $|\Phi(z)|\ge(5/6)|L(z)|>0$ when
$\operatorname{Re}z\ge-1/8$ and $|\operatorname{Im}z|\le1/6$.
Normal convergence and real evenness give $\Phi(-z)=\Phi(z)$ throughout
the larger analytic strip by the identity theorem. Reflection therefore
proves nonvanishing on the whole closed strip
$|\operatorname{Im}z|\le1/6$. This is a relative margin; the kernel still
tends to zero along the real tails.

If $R_P$ retains $2\le n\le P$, $P\ge1$, the same ratio proves

$$
|R-R_P|\le\eta_P:=
\frac72\frac{(P+1)^4e^{-2((P+1)^2-1)}}{1-1/1000} \tag{SR4}
$$

on that entire overlap strip. A callback can use this relative enclosure
without dividing two exponentially small absolute kernel values.

## A root branch on the complete physical strip

On $U_R=\{\operatorname{Re}z>-1/8,\ |\operatorname{Im}z|<1/6\}$ put

$$
s_R(z)=\sqrt\pi\,e^{5z/4-\pi e^{2z}/2}
 \frac{\sqrt{2\pi e^{2z}-3}\sqrt{1+R(z)}}{\sqrt{\cosh(z/2)}}.
\tag{SR5}
$$

Only the three displayed square-root factors use principal branches.
Their arguments have positive real part:

$$
\begin{aligned}
\operatorname{Re}(2\pi e^{2z}-3)&>5/4,\\
\operatorname{Re}(1+R(z))&>5/6,\\
\operatorname{Re}\cosh(z/2)&=\cosh(\operatorname{Re}z/2)
                                  \cos(\operatorname{Im}z/2)>0.
\end{aligned}
$$

So $s_R$ is holomorphic and squares to $\Phi(z)/(2\cosh(z/2))$.
For real $z$ it is positive. Define $s_L(z)=s_R(-z)$ on
$U_L=\{\operatorname{Re}z<1/8,\ |\operatorname{Im}z|<1/6\}$.
The branches square to the same even function and agree on the real
overlap. The identity theorem makes them agree on the whole connected
overlap. They glue to an even holomorphic $s$ on the full strip, with
$s(\bar z)=\overline{s(z)}$ and the prescribed positive root on $\mathbb R$.

The rapidly winding exponential stays outside the square roots. For
fixed $0<|y|\le1/8$, (SR1) gives

$$
\frac{\Phi(x+iy)}{2\cosh((x+iy)/2)}
\sim4\pi^2e^{4(x+iy)-\pi e^{2(x+iy)}}\qquad(x\to+\infty).
$$

Its continuous argument is $4y-\pi e^{2x}\sin(2y)+o(1)$ and is unbounded.
Taking a pointwise principal square root of this full value would cross
its branch cut repeatedly. The reflected callback uses $z\mapsto-z$,
including the imaginary part; $x+iy\mapsto|x|+iy$ is not that analytic
reflection. Every input box must lie entirely in a branch domain and
enclose the principal-root factors away from their cuts. A box that
cannot be certified must be subdivided or rejected. Ordinary callback
calls reject such boxes with a diagnostic; an `acb.integral` analytic
probe receives a nonfinite ball, as required by that integration API.

## Explicit horizontal-line bounds

For $0\le\delta\le1/8$ define

$$
a_\delta=\pi\cos(2\delta),\qquad
C_\delta=\frac{2\pi(7/6)}{\cos(\delta/2)}.
$$

For $u=e^{2|x|}$, evenness, $|1+R|\le7/6$, and
$|2\cosh((x+iy)/2)|\ge e^{|x|/2}\cos(\delta/2)$ give

$$
|s(x+iy)|^2\le C_\delta u(2\pi u+3)e^{-a_\delta u},
\qquad |y|\le\delta. \tag{SR6}
$$

Since $a_\delta>2$, both $u e^{-a_\delta u}$ and
$u^2e^{-a_\delta u}$ decrease for $u\ge1$. Hence

$$
\begin{aligned}
\sup_{|\operatorname{Im}z|\le\delta}|s(z)|&\le A_\delta,\\
A_\delta^2&=C_\delta(2\pi+3)e^{-a_\delta},\\
\sup_{|y|\le\delta}\|s(\cdot+iy)\|_2&\le B_\delta,\\
B_\delta^2&=C_\delta e^{-a_\delta}
 \left[2\pi\left(a_\delta^{-1}+a_\delta^{-2}\right)
                         +3a_\delta^{-1}\right].
\end{aligned} \tag{SR7}
$$

The line integral uses $dx=du/(2u)$ on both half-lines.
For the exact ground vector $v_0(z)=2\cosh(z/2)s(z)$,

$$
\begin{aligned}
\sup_{|y|\le\delta}\|v_0(\cdot+iy)\|_2&\le V_\delta,\\
V_\delta^2&=4\pi(7/6)e^{-a_\delta}
 \left[2\pi(a_\delta^{-1}+2a_\delta^{-2}+2a_\delta^{-3})
                     +3(a_\delta^{-1}+a_\delta^{-2})\right].
\end{aligned} \tag{SR8}
$$

Indeed $|v_0(x+iy)|^2\le4\pi(7/6)u^{3/2}(2\pi u+3)e^{-a_\delta u}$;
after substitution use $u^{1/2}\le u$. These are explicit conservative
envelopes, not measured line norms.

## Exact sharp projections and the same retained high family

Use the unitary angular-frequency convention
$\widehat f(\xi)=(2\pi)^{-1/2}\int f(x)e^{-ix\xi}\,dx$. The contour
transport in [Tao's Proposition 3](../../../Library/Analytic/tao2021stripfourier.md)
uses cycles rather than angular frequency; changing normalization gives

$$
\widehat{f(\cdot+iy)}(\xi)=e^{-y\xi}\widehat f(\xi). \tag{SR9}
$$

The theorem requires uniform integrable decay on smaller closed strips,
in addition to holomorphy. It applies here to $s$ and its products with
the band-limited or high-family functions below: (SR6), an unused strip
margin, and Cauchy–Schwarz supply this decay. For the latter functions
the weighted $L^2$ formulation also follows directly from Fourier
inversion. An interior strip with unused margin gives pointwise bounds
by Cauchy–Schwarz against $e^{-\varepsilon|\xi|}$.
The same envelope calculation is valid on the wider closed strip
$|y|\le7/48<1/6$, since $a_{7/48}>2$. This provides an explicit unused
margin beyond the numerical contour $\delta=1/8$.

For $\mathcal L_\delta(f)^2=\|f(\cdot+i\delta)\|_2^2+
\|f(\cdot-i\delta)\|_2^2$, Plancherel gives

$$
\mathcal L_\delta(f)^2
=\int2\cosh(2\delta\xi)|\widehat f(\xi)|^2d\xi,
\qquad
\|\mathbf1_{|\xi|>\Omega}\widehat f\|_2
\le e^{-\delta\Omega}\mathcal L_\delta(f). \tag{SR10}
$$

The exact continuous $P=\mathbf1_{|\mathsf D|<64}$ and $Q=I-P$
commute with this Fourier weighting and contract both horizontal-line
norms. They need not preserve rapid spatial decay. For $p\in PL^2$,
$\|p(\cdot+iy)\|_2\le e^{64|y|}\|p\|_2$, and therefore

$$
\mathcal L_\delta(sp)\le\sqrt2A_\delta e^{64\delta}\|p\|_2.
\tag{SR11}
$$

Keep $M_{1024}=2\sum_{k=0}^{1023}(2k+1/2)^{-1}$,
$W_{64}=\sum_{2\le n\le64}\Lambda(n)/\sqrt n$ and $c=3/8$.
The [retained whole-line operator](forward-action.md) has bounded Gamma
symbol $m_{1024}$, $|c_\Gamma|<8$, both prime-shift directions and the
exact mean. Multiplication by $s$ costs $A_\delta$, real translation is
an isometry on each horizontal line, and $m_{1024}(\mathsf D)$ commutes
with line transport. Since $\|v_0\|_2=1$,

$$
\begin{aligned}
D_\delta&=A_\delta^2(M_{1024}+8+2W_{64})e^{64\delta}
                  +cV_\delta,\\
\sup_{|y|\le\delta}\|(H_{1024,64}p)(\cdot+iy)\|_2
 &\le D_\delta\|p\|_2.
\end{aligned} \tag{SR12}
$$

The exact mean coefficient is bounded at the real line before its
$v_0$ output is transported. It is not a new mean formed on each contour.
For $F_B\ge\|B\|$ from the saved exact dyadics, set
$\mathcal Z=(g,Z):\mathbb C^5\to QL^2$ and

$$
U_\delta=\sqrt{V_\delta^2+D_\delta^2F_B^2}.
$$

Sharp-$Q$ contraction gives, on the same five coefficients,

$$
\sup_{|y|\le\delta}\|\mathcal Za(\cdot+iy)\|_2
\le U_\delta\|a\|,\qquad
\mathcal L_\delta(s\mathcal Za)
\le\sqrt2A_\delta U_\delta\|a\|. \tag{SR13}
$$

No separate scalar maxima are assumed to be attained simultaneously.
The $e^{64\delta}$ bandwidth cost and the full $F_B$ are retained.

## Full Gamma action beyond a finite frequency band

The [existing Gamma symbol](../../../Library/Weil/fukushima2011dirichlet.md)
and [DLMF 5.7.6](https://dlmf.nist.gov/5.7.E6) give

$$
m(\xi)=\operatorname{Re}\psi(1/4+i\xi/2)-\psi(1/4)
=2\sum_{k\ge0}\frac{\xi^2}{a_k(a_k^2+\xi^2)},\quad a_k=2k+1/2.
$$

For $t\ge0$, the summand decreases in $a_k$. The spacing-two integral
comparison supplies

$$
0\le m(t)\le\frac{4t^2}{t^2+1/4}
 +\tfrac12\log(1+4t^2)\le G(t):=4+\tfrac12\log(1+4t^2).
\tag{SR14}
$$

For $t>0$, $G'(t)/G(t)\le1/(4t)$. Thus for $\delta>0$ and
$\Omega\ge1/(4\delta)$, $G(t)e^{-\delta t}$ decreases for
$t\ge\Omega$. On the original real line,

$$
\|M_s m(\mathsf D)\mathbf1_{|\mathsf D|>\Omega}f\|_2
\le A_0G(\Omega)e^{-\delta\Omega}\mathcal L_\delta(f).
\tag{SR15}
$$

Apply this to $f=sp$ using (SR11), or to $f=s\mathcal Za$ using
(SR13). For a Gamma form entry, weighted Cauchy–Schwarz also gives

$$
\left|\int_{|\xi|>\Omega}m(\xi)
 \overline{\widehat f_i(\xi)}\widehat f_j(\xi)d\xi\right|
\le G(\Omega)e^{-2\delta\Omega}
       \mathcal L_\delta(f_i)\mathcal L_\delta(f_j). \tag{SR16}
$$

On $[-\Omega,\Omega]$, the retained full action still uses the full
digamma symbol. Its meromorphic continuation for complex quadrature is

$$
\widetilde m(\zeta)=\tfrac12\left[
\psi(1/4+i\zeta/2)+\psi(1/4-i\zeta/2)\right]-\psi(1/4).
$$

The poles are $\zeta=\pm i(2k+1/2)$, separately from the physical-strip
constraint on $s$. A callback for a Hermitian form uses Schwarz
polarization rather than a complex modulus square.

## Numerical supplier and remaining obligations

The [directed program](strip_root_bounds.py) evaluates the displayed
coefficient envelopes using python-flint, reads the saved finite-symbol,
prime-weight and exact-dyadic norm bounds, and records their hashes.
It includes a coherent root callback with (SR4), bounded overlap and
reflection checks, and rejection of uncertified whole boxes. These
checks exercise the callback; the all-strip assertions are supplied by
the paper argument above, not by point sampling.

At $\delta=1/8$, the result records full omitted-frequency Gamma-action
bounds for the low-band unit ball and the same five-generator high
family, at $\Omega=128,256,512$. They are alternatives to summing a
sufficient $262144$ Gamma indices; no retained matrix integrals or
cost comparison are claimed to have been evaluated.

Rounded outward from the exact upper dyadics:

| $\Omega$ | Low-band Gamma-action tail | Common high-family Gamma-action tail |
|---|---|---|
| 128 | $<0.014$ | $<3552$ |
| 256 | $<1.69\cdot10^{-9}$ | $<4.29\cdot10^{-4}$ |
| 512 | $<2.285\cdot10^{-23}$ | $<5.80\cdot10^{-18}$ |

Physical/input truncation, directed finite-frequency integrals, exact
continuous projection, coefficient and ground normalization transport,
common residual Gram and the final matrix sign remain separate tasks.
The fixed-$c$ input does not supply cofinal $c\uparrow1/2$ positivity,
the full Robin inequality or RH. No Lean build or digestion/freeze
delivery accompanies these paper-model inputs.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/strip_root_bounds.py
```

The program is project-authored. No third-party implementation code is
copied; dependency licensing and directed arithmetic come from
python-flint/FLINT.
