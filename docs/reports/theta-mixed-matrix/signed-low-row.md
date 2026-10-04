# Complete signed-discrepancy allowances on the original low unit ball

The [signed-head calculation](signed-discrepancy-window.md) supplies a
band allowance. To use it with the actual $N=64$ low space, the source
row and its Fourier tail must also be paid. This note reuses the saved
theta derivatives, the existing Young/Plancherel mechanism (WF5), the
complete prime tail, and the same signed-head integrator. The new
calculation changes the smoothing width and bands; it repeats no theta
action, matrix solve or derivative quadrature.

These are paper-level parameter applications and directed numerical
allowances. They give neither the low-block sign nor the common cofinal
comparison, and carry no new general theorem, Lean or priority claim.

## Preserve the actual row and its metric

Keep $s=\sqrt{\Phi/\ell}$, $\ell=2\cosh(x/2)$ and $w=1/s^2$.
Under the original unitary map $v=\sqrt{\Phi\ell}\,h$, the primitive
row is

$$
p=\Phi h=sv,\qquad \|p\|_w=\|v\|_2. \tag{LR1}
$$

The pole constraint is $v\perp v_0$, $v_0=s\ell$.
Let $P_N=\mathbf1_{|\mathsf D|<N}$ and take $v\in P_NL^2$.
The bounds below hold on this whole low unit ball, so restricting to
the actual even or centered family preserves them. The inherited
[95-column source](high-trials.md) is a subspace of this band, not a
collection of independent extrema to be summed.

The row $sv$ has no compact support. The compact-row argument (SD5)
is therefore not assigned to it. For the finite signed measure $\mu_A$
of (SD6), weighted pairing with $q=sz$ instead transports to

$$
\langle\mu_A*p,q\rangle
=\langle M_sC_{\mu_A}M_sv,z\rangle,\qquad
C_{\mu_A}p=\mu_A*p. \tag{LR2}
$$

This operator estimate does not extend a compact-core identity for
the entire Weil form to a new domain. It only bounds this bounded
arithmetic operator in the original norm.

## Reuse Fourier leakage on the same unit ball

Use the unnormalized angular transform $F_p(\xi)=\int p(x)e^{-i\xi x}dx$.
Write $a_j^2\ge\|s^{(j)}\|_2^2$ for the
[saved derivative bounds](derivative-bandwidth-result.json), and
$S_0\ge\|s\|_\infty$ for the
[saved $H^1$ transport](forward-action-result.json).
Cauchy--Schwarz gives $\|F_{sv}\|_\infty\le a_0\|v\|_2$.

For $T>N$, put $h=T-N$. In
$F_{sv}=(2\pi)^{-1}F_s*F_v$, a frequency outside $[-T,T]$ uses
only $|\omega|>h$ of $F_s$. The same Young and inverse-square
Cauchy--Schwarz mechanism as
[(WF5)](../../../Library/Weil/fukushima2011dirichlet.md#high-frequency-coercivity-and-the-scalar-deficit)
gives, with the stated angular normalization,

$$
\int_{|\xi|>T}|F_{sv}(\xi)|^2d\xi
\le\frac{2a_2^2}{3(T-N)^3}\|v\|_2^2. \tag{LR3}
$$

Indeed $\int_{|\omega|>h}\omega^{-4}d\omega=2/(3h^3)$ and
$\|\omega^2F_s\|_2=\sqrt{2\pi}\|s''\|_2$.
The convolution factor $1/(2\pi)$ and
$\|F_v\|_2=\sqrt{2\pi}\|v\|_2$ give exactly (LR3).
No number-of-rows factor occurs.

The signed-head supplier gives $\int_{-T}^T|\sigma_A|^2\le U_A(T)$.
Since $|\sigma_A|\le V_A=\|\mu_A\|_{\rm TV}$ and
$\|M_s\|\le S_0$, (SD7) now yields

$$
\|M_sC_{\mu_A}M_sP_N\|
\le H_{A,N,T}:=
\left\{\frac{S_0^2}{2\pi}
\left[a_0^2U_A(T)+
\frac{2V_A^2a_2^2}{3(T-N)^3}\right]\right\}^{1/2}. \tag{LR4}
$$

Both expenses use the same row $sv$ and the same signed measure.
The comparison allowance from total variation alone is $S_0^2V_A$.
A smaller value in (LR4) improves this allowance; it is not an
enclosure of the actual operator norm from both sides.

## Retain the full arithmetic tail without a compact-row substitution

Reuse $|s(x)|\le K_0e^{-b e^{2|x|}}$, $b=3/8$, from
[the original theta supplier](../../../Library/Analytic/romik2021orthogonal.md#weighted-fourier-coefficient-suppliers).
For $t\ge0$, $e^{2|x|}+e^{2|x+t|}\ge2e^t$.
The [existing two-direction prime allowance](forward-action.md#every-omitted-prime-power-and-both-directions)
therefore applies with $L=\lfloor X\rfloor$, $A=\log X$, and
$r=e^{-2b}$:

$$
E_{p,L}=2K_0^2\frac{r^{L+1}((L+1)-Lr)}{(1-r)^2}. \tag{LR5}
$$

For the continuous main term, both directions cost at most
$2K_0^2\int_A^\infty e^{t/2}e^{-2be^t}dt$.
Substitute $n=e^t$ and use $n^{-1/2}\le X^{-1/2}$ to get

$$
E_{c,X}=\frac{2K_0^2e^{-2bX}}{2b\sqrt X},\qquad
E_A=E_{p,L}+E_{c,X}. \tag{LR6}
$$

These tails converge in operator norm and retain all prime powers and
the continuous component of the same discrepancy. Its complete
transported operator obeys

$$
\|M_sC_\mu M_sP_N\|\le H_{A,N,T}+E_A. \tag{LR7}
$$

The corresponding reference allowance is $S_0^2V_A+E_A$.
The tail is bounded absolutely after the signed head is retained;
no cancellation claim is attached to that tail bound.

## Directed fixed-band results and their limit

The [producer](signed_low_row.py) reuses three hash-bound saved
suppliers and the head integrator in [signed_head.py](signed_head.py).
It keeps $X=289/2$, with all 47 positive prime-power atoms, and uses
the new width $\delta=1/64$, $N=64$, $T=128,192$.
Both bands satisfy $T>N$ and $0<\delta T<2\pi$.
The [192-bit saved data](signed-low-row-result.json) gives outward
enclosures:

| $T$ | Complete upper allowance $H_{A,N,T}+E_A$ | Ratio to $S_0^2V_A+E_A$ |
|---|---:|---:|
| 128 | $[14.70575975,14.70575977]$ | $[0.27388781,0.27388783]$ |
| 192 | $[23.54251712,23.54251714]$ | $[0.43846823,0.43846825]$ |

The complete arithmetic tail allowance is below $1.803\cdot10^{-44}$.
Both comparisons are strict and include the Fourier-tail expense.
The $T=192$ allowance is larger; enlarging a band is not by itself
a monotone improvement of the combined budget.

## Fixed-head band expansion has a classical obstruction

There is a source-level reason to stop simply expanding the band at a
fixed arithmetic head. The retained
[Teschl source](../../../Library/Fourier/teschl2009mathematical.md#finite-measure-fourier-mean-squares),
Theorem 5.4, equations (5.8)–(5.9), already gives Wiener's finite-measure
mean-square limit. For the same real even $\mu_A$, with fixed
$A\ge\log2$, its exact parameter application is

$$
\lim_{T\to\infty}\frac1{2T}\int_{-T}^T|\sigma_A(\xi)|^2d\xi
=2\sum_{\log n\le A}\frac{\Lambda(n)^2}{n}>0. \tag{LR8}
$$

Every prime power contributes at two distinct atoms. The continuous
main term contributes no atom; evenness changes the source's one-sided
average into the displayed symmetric average. This is reuse of the
classical theorem, without another proof or numerical experiment.

Since $U_A(T)$ bounds that actual band integral and the Fourier-tail
expense in (LR4) is nonnegative, fixed positive caps $S_0,a_0$ give,
for any $N(T)<T$,

$$
\liminf_{T\to\infty}\frac{H_{A,N(T),T}^2}{T}
\ge\frac{2S_0^2a_0^2}{\pi}
\sum_{\log n\le A}\frac{\Lambda(n)^2}{n}>0. \tag{LR9}
$$

Thus the scalar allowance in (LR4) diverges on a fixed-head
$N\to\infty$, $T>N$ route, for any valid smoothing widths.
The actual weighted head operator still has the fixed upper bound
$S_0^2V_A$. This identifies loss in the band-supremum scalar estimate;
eventually it cannot improve even that total-variation reference.
The conclusion concerns fixed $A$ and this particular allowance.
It does not settle a growing-$A$ schedule or a localized joint estimate.

For the cofinal problem, the needed next interface should preserve
theta localization and the actual same-row frequency information,
rather than assign its band supremum to every frequency separately.

The [local frequency application](local-signed-frequency.md) reuses
Schur's criterion to retain a Lorentzian energy around each input
frequency. At the same $N=64$ and arithmetic cutoff, it supplies a
smaller complete upper allowance without replaying these computations.
It supplies neither the low sign nor a growing-cutoff comparison.

## The remaining signed comparison

These values are not a small residual certificate for the existing
low Schur center. They are not compared to the saved full-theta
action or matrix estimates, which concern different operators.
In particular, a norm bound on $\mathcal R$ does not supply the
one-sided signed comparison $\mathcal R(f)\le\mathcal H(f)+
\varepsilon\|f\|_w^2$. Its main multiplier is negative at zero.
The same-sequence low sign, couplings and high comparison still have
to be combined as $\varepsilon\downarrow0$. Fixed $N=64$ does not
pay those other bands. RH and full Robin remain unresolved.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/signed_low_row.py
```

The project-authored program uses python-flint/FLINT. It rejects low
precision, incompatible supplier identities or bandwidths, invalid
directed endpoints, a band that does not contain the source band, and
an uncertified full allowance comparison.
