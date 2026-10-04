# Complete low-band forward-action error

This supplier applies the existing positive Gamma symbol series (WF3) in
the [actual transformed form](../../../Library/Weil/fukushima2011dirichlet.md)
to the common matrix inputs in the [sharp-center interface](sharp-center.md).
It reuses the saved original-theta derivative norms and complete prime
majorant. It supplies an operator-action truncation error, rather than a
new inverse-residual theorem or a retained matrix sign.

## Same operator and whole-line inputs

Keep $c=3/8$, $N=64$, $P=\mathbf1_{|\mathsf D|<N}$ on the even space,
$Q=I-P$, $\alpha=1/8$ and the exact $v_0=\sqrt\rho$ with unit norm.
Write the full operator on its domain as

$$
Tp=\alpha p+s\,m(\mathsf D)(sp)+c_\Gamma s^2p-Bp
       +c\langle v_0,p\rangle v_0.
$$

Let $T_{J,L}$ replace only the Gamma symbol by its first $J$ positive
terms and $B$ by both shifted directions for every prime power $n\le L$.
The multiplication and mean terms remain exact. There is no physical
interval cutoff or periodic convolution in this definition.

The [saved derivative bounds](derivative-bandwidth-result.json) and the
standard one-dimensional $H^1$ inequality give

$$
S_j:=\bigl(\|s^{(j)}\|_2\|s^{(j+1)}\|_2\bigr)^{1/2}
\ge\|s^{(j)}\|_\infty,\qquad j=0,1,2.
$$

For every unit low-band input, Plancherel and Leibniz give

$$
\|(sp)''\|_2\le A_N:=S_2+2NS_1+N^2S_0.
$$

These bounds use the full real line. Rounded outward,
$S_0<0.7872471368510453$, $S_1<2.815063079726962$,
$S_2<32.69045442369057$ and $A_{64}<3617.582801170624$.

## Every omitted Gamma term

Put $a_k=2k+1/2$ and

$$
m_J(\xi)=2\sum_{k=0}^{J-1}
\frac{\xi^2}{a_k(a_k^2+\xi^2)},\qquad
\sigma_J=\frac1{2a_{J-1}^2}.
$$

The decreasing inverse-cubic integral gives
$0\le m(\xi)-m_J(\xi)\le\sigma_J\xi^2$ for every real $\xi$.
Consequently

$$
\|M_s(m-m_J)(\mathsf D)M_sP\|
\le S_0\sigma_J A_N.
$$

Each retained term acts by an actual whole-line exponential convolution:

$$
\frac{2\mathsf D^2}{a(a^2+\mathsf D^2)}f
=\frac2a f-\int_{\mathbb R}e^{-a|t|}f(\,\cdot-t)\,dt.
$$

This formula supplies a forward action on $L^2$; it assumes neither an
inverse kernel for $C=QTQ$ nor domains of successive powers of $C$.

## Every omitted prime power and both directions

Use $b=3/8$, $r=e^{-2b}$ and the existing
$|s(x)|\le K_0e^{-b e^{2|x|}}$. For $t_n=\log n$,
$e^{2|x|}+e^{2|x\pm t_n|}\ge2n$. Thus each shifted coefficient has
supremum at most $K_0^2w_ne^{-2bn}$, where
$w_n=\Lambda(n)/\sqrt n\le n$. Summing over all integers beyond $L$
and paying both directions gives

$$
\|B-B_L\|\le
2K_0^2\frac{r^{L+1}((L+1)-Lr)}{(1-r)^2}=:E_{p,L}.
$$

No omitted prime power is removed by its absence from the retained list.
This is an operator-norm bound, independent of input parity or bandwidth.

At $J=1024$, $L=64$, $a_{J-1}=4093/2$, the
[directed coefficient result](forward-action-result.json) gives

$$
\begin{aligned}
E_{\Gamma,1024}&<0.000339997776177744450,\\
E_{p,64}&<9.291673916671230\cdot10^{-19},\\
\|(T-T_{1024,64})P\|&<0.000339997776177745379<1/1000.
\end{aligned}
$$

Contraction by $P$ or $Q$ preserves this forward error. It bounds the
common low-band ball, not merely separately selected scalar inputs.

For a high trial $q$, the analogous Gamma allowance is
$S_0\sigma_J\|(sq)''\|_2$ when $sq\in H^2$. The bound $A_{64}\|q\|_2$
cannot be substituted: high trials and arbitrary residuals are not
low-band inputs. Their weighted derivative inputs, complete retained
integrals, residual Gram and matrix sign remain separate obligations.
This result supplies no Lean, full Robin or RH certificate.

## Reproduce

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/forward_action.py
```

The program reads the canonical saved derivative and sharp-center data,
records their SHA-256 hashes and writes the result beside itself. It runs
128-bit ball coefficient arithmetic without repeating the derivative,
deficit or scalar integration grids. The program is project-authored;
python-flint/FLINT supplies directed arithmetic and its dependency
licensing. It rejects mismatched input parameters, nonfinite endpoints
or failure of the declared $1/1000$ error target.
