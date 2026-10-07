# Complete low-band forward-action error

This supplier applies the existing positive Gamma symbol series (WF3) in
the [actual transformed form](../../../Library/Weil/fukushima2011dirichlet.md)
to the common matrix inputs in the [sharp-center interface](sharp-center.md).
It reuses the saved original-theta derivative norms and complete prime
majorant. It supplies an operator-action truncation error, rather than a
new inverse-residual theorem or a retained matrix sign.

Complex pairings and rank-one operators follow the
[first-slot-linear matrix convention](README.md#complex-inner-products-for-matrix-reports).

## Same operator and whole-line inputs

Keep $c=3/8$, $N=64$, $P=\mathbf1_{|\mathsf D|<N}$ on the even space,
$Q=I-P$, $\alpha=1/8$ and the exact $v_0=\sqrt\rho$ with unit norm.
Write the full operator on its domain as

$$
Tp=\alpha p+s\,m(\mathsf D)(sp)+c_\Gamma s^2p-Bp
       +c\langle p,v_0\rangle v_0.
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


## Weighted omitted actions before the sharp high projection

This section uses every subcritical parameter and admissible bandwidth
of [WH1--WH2](../../../Library/Weil/fukushima2011dirichlet.md#spatially-weighted-high-inverse-at-every-subcritical-parameter),
rather than the saved fixed-band data above. Keep its
$\varepsilon,c,\delta,a_N,V,w,P,Q,T_c$ and put
$H_c=T_c-\varepsilon I$. Let $H_{c,J,L}$ omit only Gamma terms
with index at least $J$ and prime powers above $L$, keeping both shifted
adjoints, multiplication and the exact mean. For integers $J,L\ge1$, reuse the
complete positive symbol tail and the (WC2) envelope above. With any
supremum bound $S_0\ge\|s\|_\infty$, set

$$
\kappa_w=\frac{S_0}{\sqrt{\delta+a_NS_0^2}},\qquad
b_\Gamma=\kappa_w\sigma_J,\qquad
\sigma_J=\frac1{2(2J-3/2)^2}.
\tag{WA1}
$$

Indeed $\sqrt w\,s\le\kappa_w$, since
$t/\sqrt{\delta+a_Nt^2}$ is increasing for $t\ge0$.
Thus for each actual whole-line source $u$ with $su\in H^2$,

$$
\|\sqrt w\,M_s(m-m_J)(\mathsf D)M_su\|_2
\le b_\Gamma\|(su)''\|_2.
\tag{WA2}
$$

For every prime power $n$ and either shifted direction, its weighted
coefficient has supremum at most

$$
w_n\min\{\kappa_wS_0,\ \delta^{-1/2}K_0^2e^{-2bn}\},
\qquad w_n=\Lambda(n)/\sqrt n,\quad b=3/8.
$$

The first cap uses the output factor $\sqrt w\,s$ and the other
factor $s$; the second uses the original paired envelope and
$\sqrt w\le\delta^{-1/2}$. Both adjoint directions have these caps.
For any integer $M\ge L$, put $\varrho=e^{-2b}$ and

$$
\begin{aligned}
b_{\rm p}(L,M)=2\bigg[&\sum_{L<n\le M}w_n
 \min\{\kappa_wS_0,\delta^{-1/2}K_0^2\varrho^n\}\\
&+\delta^{-1/2}K_0^2
 \frac{\varrho^{M+1}((M+1)-M\varrho)}{(1-\varrho)^2}\bigg].
\end{aligned}
\tag{WA3}
$$

The finite sum includes every prime power in its range. Bounding every
remaining $w_n$ by $n$ gives the displayed geometric tail. Translation
is unitary, so the complete common action error satisfies

$$
\|\sqrt w(H_c-H_{c,J,L})u\|_2
\le b_\Gamma\|(su)''\|_2+b_{\rm p}(L,M)\|u\|_2.
\tag{WA4}
$$

These are applications of the existing symbol and prime envelopes,
not new generic estimates. At $M=L$ the prime budget is the old
complete prime allowance multiplied by $\delta^{-1/2}$;
$b_\Gamma\le\delta^{-1/2}S_0\sigma_J$. No old numerical constants
are supplied for another parameter or bandwidth. The weight applies
before $Q$: it cannot be assigned to $Q(H_c-H_{c,J,L})u$ by
commutation. The [common dual-source consumer](sharp-center.md#pay-weighted-action-errors-with-one-common-dual-source)
uses exactly this unprojected error. High trials require their own
$\|(su)''\|_2$ inputs. No assumption $H_cu/s\in L^2$ is made.
Only omitted actions are paid; retained whole-line quadrature, input
and Gram errors, actual signs and cofinal control remain outstanding.
