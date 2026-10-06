# Ground normalization and common residual action tails

The exact lift in [high-trials.md](high-trials.md) divides by
$\|p_0\|^2$, where $p_0=Pv_0$. This supplier pays that normalization and
transports the two complete action-tail allowances to the common
residual on $p_0^\perp$. It reuses the saved original-theta norms,
(WC2) and standard Plancherel/triangle inequalities. It does not supply
the retained residual Gram or a new residual-comparison theorem.

## Quantitative ground projection

Let $a_j$ denote the saved upper bound for $\|s^{(j)}\|_2$, let $R=3$,
$b=3/8$, $u_R=e^{2R}$ and write

$$
\tau_R=\left(\frac{u_R^{-1/2}e^{-2bu_R}}{2b}\right)^{1/2}.
$$

The two exterior tails of
$e^{|x|/2}e^{-b e^{2|x|}}$ have squared integral at most $\tau_R^2$:
substitute $u=e^{2|x|}$ and bound $u^{-1/2}$ by $u_R^{-1/2}$.
Put $h=\cosh(R/2)$, $t=\sinh(R/2)$. From
$v_0=2\cosh(x/2)s$ and the full-line (WC2) envelopes,

$$
\begin{aligned}
I_1&=2ha_1+ta_0,& O_1&=2(K_1+K_0/2)\tau_R,\\
I_2&=2ha_2+2ta_1+ha_0/2,& O_2&=2(K_2+K_1+K_0/4)\tau_R.
\end{aligned}
$$

The interior and exterior supports are disjoint, so
$\|v_0^{(j)}\|_2\le V_j=(I_j^2+O_j^2)^{1/2}$ for $j=1,2$.
The saved $a_j$ bound the entire line, and hence also each interior
norm; using them here does not discard any exterior contribution.

For the exact $N=64$ Fourier cutoff, Plancherel gives

$$
\|Qv_0\|_2\le V_2/N^2=:\eta,
\qquad \|p_0\|_2\ge(1-\eta^2)^{1/2}=:\kappa>0.
$$

The [directed coefficient result](ground-residual-result.json) gives
$V_1<6.882782636152797$, $V_2<36.01840092585700$ and

$$
\eta<0.008793554913539307,
\qquad\kappa>0.9999613359485368,
\qquad\|p_0\|^{-2}<1.000077332587885.
$$

Thus the exact ground correction
$Y_0=-|Qv_0\rangle\langle p_0|/\|p_0\|^2$ has
$\|Y_0\|\le\eta/\kappa<0.008794$.
This supplies a normalization bound; it does not replace the exact
vector $p_0$ by its numerical polynomial approximation.

## One residual map on the exact ground complement

Keep the fixed $Z,A,E,Y$ from (HT1)–(HT2). Write
$J_\ell=1024$, $J_h=262144$ and $L=64$, and define

$$
\widehat K=QT_{J_\ell,L}P,\qquad
\widehat{CZ}=QT_{J_h,L}Z.
$$

All terms in these definitions are whole-line actions with the exact
mean and multiplication. The retained convolutions are not evaluated
by this coefficient supplier. On $PL^2\cap p_0^\perp$ set

$$
\widehat r=\widehat K-\widehat{CZ}\,A E^*,\qquad r=K-CY.
$$

Since $Y_0p=0$ and $(I-\Pi_0)p=p$ on this complement, the two previous
suppliers give, with the same trial coefficients,

$$
\|(r-\widehat r)p\|_2
\le (\varepsilon_\ell+F_A\varepsilon_h)\|p\|_2
<0.000661388285493508\,\|p\|_2<0.000662\,\|p\|_2,
$$

where $F_A\ge\|A\|$ is the dyadic Frobenius bound,
$\varepsilon_\ell$ is the complete low-band action tail and
$\varepsilon_h$ is the separate common high-family action tail.
The latter is restricted to the $Z$ columns; its original five-column
bound also includes $Qv_0$ and therefore remains a valid upper bound.
The known exact $Cg=-Kp_0$ supplies the ground residual directly.

This is the error between an exact residual map and its specified
retained-action map. It is not a bound for $\|r\|$, and it pays none of
the retained quadrature, projection, Gram or rounding errors. Such errors
must still be added before a residual Gram or Loewner sign can be
certified. No $T$ action on an arbitrary residual, $C^2$ action, retained
positivity, cofinal conclusion, Lean, Robin or RH certificate is claimed.

## Reproduce

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/ground_residual.py
```

This project-authored coefficient program reads the saved derivative
and action data, loads only the original coefficient setup and records
source hashes. It does not repeat an integration grid. Output upper and
lower endpoints are saved as exact dyadics. Directed arithmetic and
dependency licensing are supplied by python-flint/FLINT.
