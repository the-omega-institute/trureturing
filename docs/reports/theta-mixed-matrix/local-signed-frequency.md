# A local frequency allowance for the same signed arithmetic operator

The [original low-row allowance](signed-low-row.md) bounds the entire
$N=64$ low unit ball, but its band-supremum step spends the same row
cap at every frequency. This note instead applies the classical
[Schur criterion](../../../Library/Fourier/teschl2009mathematical.md#schur-criterion-for-the-local-frequency-kernel)
to the actual convolution kernel. It reuses the saved theta $H^1$
bounds, the same signed prime head and the complete arithmetic tail.
No theta action, matrix, old head integral or generic theorem is redone.
The mathematical interface is a paper application, without a new
Lean certification or priority claim.

## Apply the source criterion to the actual low space

Keep $p=sv$, $s=\sqrt{\Phi/(2\cosh(x/2))}$,
$v\in P_NL^2$, and the unnormalized angular Fourier transform $F$.
For the same finite signed measure $\mu_A$ in (SD6), write
$\sigma_A=F\mu_A$. The Fourier kernel of $C_{\mu_A}M_sP_N$,
acting from $[-N,N]$ to the whole line, is

$$
K(\xi,\eta)=\frac{\sigma_A(\xi)F_s(\xi-\eta)}{2\pi}.
\tag{LF1}
$$

For $q>0$ put

$$
g_q(u)=\frac{q^2}{q^2+u^2},\qquad
J_q=\int_{\mathbb R}\frac{|F_s(u)|^2}{g_q(u)}du
\le2\pi(a_0^2+a_1^2/q^2).
\tag{LF2}
$$

Here $a_j^2\ge\|s^{(j)}\|_2^2$ are the existing
[directed derivative suppliers](derivative-bandwidth-result.json).
The inequality is their Plancherel application, not a new quadrature.
In Teschl's Lemma 0.32, take $p=q_{\rm source}=2$ and

$$
K_1(\xi,\eta)=\frac{|F_s(\xi-\eta)|}{\sqrt{2\pi g_q(\xi-\eta)}},\qquad
K_2(\xi,\eta)=\frac{|\sigma_A(\xi)|\sqrt{g_q(\xi-\eta)}}{\sqrt{2\pi}}.
$$

The source's two squared constants are at most $J_q/(2\pi)$ and
$\sup_{|\eta|\le N}\int g_q(\xi-\eta)|\sigma_A(\xi)|^2d\xi/(2\pi)$.
Its criterion, followed by the same output multiplier bound
$\|M_s\|\le S_0$, therefore gives

$$
\|M_sC_{\mu_A}M_sP_N\|^2
\le\frac{S_0^2(a_0^2+a_1^2/q^2)}{2\pi}
\sup_{|\eta|\le N}\int_{\mathbb R}
g_q(\xi-\eta)|\sigma_A(\xi)|^2d\xi.
\tag{LF3}
$$

This holds on the whole low unit ball and hence on its even or centered
subspaces. It preserves the primitive row $p=sv$, which is noncompact.
The integral covers every frequency; there is no separate frequency
cutoff or row-count factor. It remains an upper allowance, not a
one-sided comparison with the Gamma symbol.

## Evaluate the local energy without cutting its frequency tail

The classical Lorentzian transform, with this normalization, is

$$
\int_{\mathbb R}g_q(\xi-\eta)e^{-i\xi(t-u)}d\xi
=\pi q e^{-q|t-u|}e^{-i\eta(t-u)}.
$$

The retained source locates this transform through its free resolvent
kernel (7.47). The finite total variation of $\mu_A$ and $g_q\in L^1$
justify Fubini. Since the measure is real, swapping $t,u$ removes the
imaginary part. Define

$$
D_{A,q}(\eta)=\iint e^{-q|t-u|}\cos(\eta(t-u))d\mu_A(t)d\mu_A(u)
=\frac1{\pi q}\int g_q(\xi-\eta)|\sigma_A(\xi)|^2d\xi\ge0.
\tag{LF4}
$$

Thus the local energy still contains the common prime--prime,
prime--continuum and continuum--continuum terms. Their signs are
retained inside one square before a common interval is evaluated.
From (LF3), the complete allowance is

$$
\|M_sC_\mu M_sP_N\|
\le S_0\left\{\frac{qa_0^2+a_1^2/q}{2}
\sup_{|\eta|\le N}D_{A,q}(\eta)\right\}^{1/2}+E_A,
\tag{LF5}
$$

using the unchanged complete arithmetic tail $E_A$ from (LR5)--(LR7).
The full weighted operator is the same operator-norm limit used there;
the global unweighted discrepancy is not assigned a finite total variation.

For a fixed $A$, (LF4) also gives $D_{A,q}(\eta)\le V_A^2$
at every frequency. Hence this particular local allowance is bounded
as $N$ grows with fixed $A,q$. This does not assert a strict gain in
that limit, or any control when the arithmetic cutoff also grows.
The fixed-head Wiener obstruction to (LR4)'s global band cap does not
force growth of (LF5).

## Elementary common-measure calculation

Write the positive atoms as $t_i=\log n_i$, $c_i=\Lambda(n_i)/\sqrt{n_i}$,
put $z=q+i\eta$, and take $q\ne1/2$ for the following primitives.
Set

$$
j_0(z)=\frac{1-e^{-(z-1/2)A}}{z-1/2},\qquad
j(z,t)=e^{-zt}j_0(z)+\frac{e^{t/2}-e^{-zt}}{z+1/2}
+\frac{e^{t/2}-e^{zt-(z-1/2)A}}{z-1/2}.
$$

Splitting each continuum integral at $0$ and $t$ gives
$j(z,t)=\int_{-A}^A e^{-z|t-u|}e^{|u|/2}du$ for $0\le t\le A$.
The same two half-lines give

$$
\begin{aligned}
P_P(z)&=2\sum_i c_i^2+4\sum_{i>j}c_ic_je^{-z(t_i-t_j)}
       +2\left(\sum_i c_ie^{-zt_i}\right)^2,\\
P_C(z)&=2\sum_i c_i j(z,t_i),\\
C_C(z)&=\frac{4(e^A-1-j_0(z))}{z+1/2}+2j_0(z)^2,\\
D_{A,q}(\eta)&=\Re\{P_P(z)-2P_C(z)+C_C(z)\}.
\end{aligned}
\tag{LF6}
$$

These are finite-measure parameter identities using elementary
exponential integrals. They do not introduce another primality test or
recompute the saved Gallagher/tent integral.

## Directed fixed-band result

The [producer](local_signed_frequency.py) fixes $q=2$, $N=64$,
$X=e^A=289/2$ and cell width $1/8$. It imports the saved metadata for
all 47 positive prime-power atoms, their reflected partners, the
original theta derivative caps and the unchanged complete arithmetic
tail. Its [192-bit data](local-signed-frequency-result.json) encloses
(LF6) on 512 closed cells covering $[0,64]$. Evenness covers $[-64,0]$.
This is a whole-cell upper enclosure, not a sample maximum or an
enclosure of the true supremum from both sides.

The outward complete upper allowance is $[5.45645801,5.45645802]$.
For the same original operator and arithmetic tail:

| Comparison reference | Ratio of the new complete upper allowance |
|---|---:|
| Retained $T=128$ complete allowance from (LR7) | $[0.37104223,0.37104225]$ |
| Same weighted head total variation plus the same tail | $[0.10162394,0.10162396]$ |

The saved complete arithmetic tail remains below $1.803\cdot10^{-44}$.
The smaller allowance is not a measured reduction of the actual norm.
It is still too large to supply the missing low sign or a small Schur
residual certificate. The actual common cofinal low/coupling/high
comparison, RH and full Robin remain unresolved.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/local_signed_frequency.py
```

This project-authored program uses python-flint/FLINT. It rejects
insufficient precision, incompatible saved supplier identities,
inconsistent common-head metadata or endpoints, singular primitive
denominators, nonfinite local energies, and an uncertified complete
allowance improvement. The program reads saved derivative,
forward-supremum, sharp-center and signed-low-row data; it reruns no
theta action, signed-head integral or matrix calculation.
