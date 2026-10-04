# Exact continuous projection by a physical sinc lattice

This model application reuses [Tao's Poisson summation and strip
transport](../../../Library/Analytic/tao2021stripfourier.md), Fourier
inversion, and the [original-root line envelopes](strip-root.md).
The method is classical. The coefficients below concern the same
whole-line family $H=H_{1024,64}EB$ in [high-trials.md](high-trials.md),
before its exact sharp projection. No new general theorem, retained
Gram, matrix sign or Lean certification is claimed.

## Preserve the actual cutoff

For the unitary angular-frequency convention, the continuous projection
$P=\mathbf1_{|\mathsf D|<N}$, $N=64$, has kernel

$$
k_N(t)=\frac{\sin Nt}{\pi t},\qquad k_N(0)=N/\pi,
\qquad PH(x)=\int_{\mathbb R}H(y)k_N(x-y)\,dy. \tag{CP1}
$$

The value $64$ is not a native frequency of a period-$128$ DFT. A
discrete frequency mask therefore substitutes another projection.
Instead, for $h=1/256$ approximate the integral by

$$
P_hH(x)=h\sum_{j\in\mathbb Z}H(jh)k_N(x-jh). \tag{CP2}
$$

This uses the actual continuous $N$ in the kernel, including when $N$
does not fall on a DFT frequency. For the localized $H$ here the series
is absolutely convergent.

## Infinite-lattice quadrature

Fix $\delta=1/8$ and $F=2\pi/h$. Let $D_\delta$ be (SR12), and let
$F_B$ be the saved Frobenius upper bound on $B$. For every coefficient
vector $a\in\mathbb C^4$,

$$
\sup_{|y|\le\delta}\|Ha(\cdot+iy)\|_2
\le D_\delta F_B\|a\|.
$$

Plancherel applied to (CP1) gives, for any real $x$,

$$
\|k_N(x-\cdot-iy)\|_2^2
=\frac{\sinh(2N|y|)}{2\pi|y|},\qquad
K_\delta=\sqrt{\frac{\sinh(2N\delta)}{2\pi\delta}}. \tag{CP3}
$$

At $y=0$ the limiting squared norm is $N/\pi$; the displayed expression
increases with $|y|$. Thus Cauchy–Schwarz bounds the horizontal-line
$L^1$ norm of $Ha(z)k_N(x-z)$ by
$D_\delta F_BK_\delta\|a\|$, uniformly in real $x$. The product is
holomorphic on a larger strip: $H$ has the original-root unused strip
margin, and $k_N$ is entire. On smaller closed strips the outer $s$
and $v_0$ in $H$ provide rapid integrable decay; the finite multiplier
and real translations preserve the required bounds. Consequently the
contour and Poisson hypotheses in the cited source hold for this
product. Contour shift in its nonunitary transform gives
$|\int Ha(y)k_N(x-y)e^{-i\xi y}dy|
\le D_\delta F_BK_\delta e^{-\delta|\xi|}\|a\|$.
Summing the nonzero Poisson frequencies yields

$$
|(P_h-P)Ha(x)|
\le q_h\|a\|,\qquad
q_h=2D_\delta F_BK_\delta
       \frac{e^{-\delta F}}{1-e^{-\delta F}}. \tag{CP4}
$$

This is a uniform pointwise error. Integrating a constant over the whole
real line does not turn it into a whole-line $L^2$ error. On a specified
finite interval of length $T$ it gives the bound $\sqrt Tq_h$.

## Finite physical input tail

Write $u=e^{2|x|}$, $b=\pi/2$ and
$C_s=\sqrt{2\pi(7/6)(2\pi+3)}$. The real (SR6) envelope implies

$$
|s(x)|\le C_su e^{-bu},\qquad
|v_0(x)|\le2C_su^2e^{-bu}. \tag{CP5}
$$

The finite multiplier has the convolution representation

$$
m_J(\mathsf D)f=M_Jf-\sum_{k=0}^{J-1}
 e^{-a_k|\cdot|}*f,\qquad
a_k=2k+1/2,\quad M_J=2\sum_{k<J}a_k^{-1}.
$$

Each convolution kernel has $L^1$ norm $2/a_k$. Hence its full
$L^\infty$ action costs at most $2M_J$. Band limitation gives
$\|EBa\|_\infty\le\sqrt{N/\pi}F_B\|a\|$; use the saved
$A_0\ge\|s\|_\infty$, $|c_\Gamma|<8$, both prime directions with
weight sum $W_{64}$, and
$|\langle v_0,EBa\rangle|\le F_B\|a\|$. Therefore

$$
\begin{aligned}
|Ha(x)|&\le C_Hu^2e^{-bu}\|a\|,\\
C_H&=C_sF_B\left[A_0\sqrt{N/\pi}
                    (2M_{1024}+8+2W_{64})+2c\right],\quad c=3/8.
\end{aligned} \tag{CP6}
$$

No sharp-$Q$ spatial decay is asserted here: the localized vector is
$H$, while $Z=QH$ can have sinc tails. For $X=4$ let $U_X=e^{2X}$ and

$$
J_X=C_He^{-bU_X}\left(\frac{U_X}{b}+\frac1{b^2}\right).
\tag{CP7}
$$

Substitution $dx=du/(2u)$ on the two half-lines gives
$\|\mathbf1_{|x|>X}Ha\|_1\le J_X\|a\|$. Since
$u^2e^{-bu}$ decreases for $u\ge2/b$ and $X/h$ is an integer, the
right-endpoint integral comparison also gives

$$
h\sum_{|jh|>X}|Ha(jh)|\le J_X\|a\|. \tag{CP8}
$$

Using $|k_N(t)|\le N/\pi$ on the real line, omission of these lattice
samples adds at most $(N/\pi)J_X\|a\|$. The finite sinc sum therefore
differs from the exact continuous $PHa(x)$ by at most
$[q_h+(N/\pi)J_X]\|a\|$, before numerical sample and kernel errors.
The continuous physical input-tail allowance has the same bound.

## Paid versus unpaid sampling

If directed approximations $\widetilde H_j$ satisfy
$|\widetilde H_ja-H(jh)a|\le\varepsilon_j\|a\|$, their contribution
to the projection error is at most

$$
\frac N\pi h\sum_{|jh|\le X}\varepsilon_j\|a\|. \tag{CP9}
$$

Kernel evaluation and arithmetic need their own directed enclosures.
The coefficient program does not supply $\varepsilon_j$ for actual
operator samples, and $QH$ additionally needs the error of $H(x)$ at
the output point. A finite-array roundtrip alone pays neither error.

For a length-$32768$ DFT of period $128$, place the retained samples
at signed indices and tabulate $k_N(jh)$ for signed differences in
$[-64,64)$. At lattice outputs $x=kh$, if $|x|\le33/4$ and $|jh|\le4$, every used difference
has absolute value at most $49/4<64$. Circular convolution therefore
has no wrap on this output interval. The unscaled forward DFT and the
$1/32768$-scaled inverse compute this finite convolution after a final
factor $h$. This is an exact finite-sum identity, separate from (CP4),
(CP8) and the actual sample errors. The local prime shifts lie within
the same geometric range, since $4+\log64<33/4$, but generally fall
off the lattice. They require the finite sinc sum, shifted-kernel
evaluation or separately certified interpolation; the unshifted DFT
does not already evaluate them. The bounds (CP2)–(CP9) hold at arbitrary
real outputs.

## Reused Fourier alias coefficients

For $f=su$, the same strip argument gives
$|\widehat f(\xi)|\le B_\delta U_\delta
e^{-\delta|\xi|}/\sqrt{2\pi}$. Use $U_\delta=e^{64\delta}$ for
the unit low-band ball, or (SR13) for the same five-generator high
family. Define the unitary-normalized infinite sample transform by
$\widehat f_h(\xi)=h(2\pi)^{-1/2}\sum_j f(jh)e^{-i\xi jh}$.
On $|\xi|\le\Omega=512<F/2$, its difference from $\widehat f(\xi)$,
the infinite sample-lattice alias, is bounded on the coefficient unit
ball by

$$
\frac{B_\delta U_\delta}{\sqrt{2\pi}}
\frac{2e^{-\delta(F-\Omega)}}{1-e^{-\delta F}}. \tag{CP10}
$$

For an arbitrary high-family coefficient vector, multiply this bound
by $\|a\|$. Multiplication by $\sqrt{2\Omega}A_0G(\Omega)$ bounds its Gamma action
on this retained frequency band. This pays infinite-lattice aliases;
it does not pay finite physical sample truncation, sample evaluation,
frequency quadrature, the omitted frequency band, or a common Gram.

The [directed coefficient program](continuous_projection_bounds.py)
reads the existing saved dyadics and records their hashes in
[continuous-projection-result.json](continuous-projection-result.json).
All displayed estimates are model applications, not original general
Poisson or sampling theorems. Complete common Grams, the actual
projected-ground direction, the restricted sign, cofinal positivity,
Robin and RH remain unresolved.

Rounded outward, the pointwise sinc quadrature allowance is less than
$1.722\cdot10^{-75}$, and its finite physical lattice-tail allowance is
less than $6.402\cdot10^{-2023}$. The retained-band Gamma alias-action
allowances are less than $4.863\cdot10^{-54}$ on the unit low-band ball
and $1.234\cdot10^{-48}$ on the same high-family coefficient unit ball.
These small allowances do not bound the still-uncomputed sample errors.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/continuous_projection_bounds.py
```

The program is project-authored. It uses python-flint/FLINT directed
arithmetic and copies no third-party implementation code.
