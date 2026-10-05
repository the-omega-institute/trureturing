# A target-dependent correction at c=0.45 and c=0.46

The [actual coupling comparison](actual-coupling.md) transports the
base form with a fixed correction. A new correction chosen for a new
target reduces its high residual. This note reuses the saved actions,
Grams and exact ground moments, and evaluates only the new correction
and its comparisons. Schur monotonicity, residual identities and the
three-block lift are existing methods; no general-method or priority
claim is made.

All statements concern the same paper operator, exact unit ground,
minimal form domain and analytic/numerical supplier premises. The
directed calculations are not Lean certification.

## Preserve the actual ground while selecting a simpler comparison

Use $c_0=3/8$, $\alpha_0=1/8$, $P=P_{64}$, $Q=I-P$ and the accepted
isometry $E:\mathbb C^{95}\to PL^2_{\rm even}$. Put $\Pi=EE^*$,
$D_t=P-\Pi$, $e=E^*v_0$, $p_0=Pv_0$, $q_0=Qv_0$.
For $g=c-c_0>0$ the unchanged model gives

$$
T_c=T_0-gI+g|v_0\rangle\langle v_0|,\quad
H_c=H_0+g|v_0\rangle\langle v_0|,\quad
\alpha_c=\alpha_0-g. \tag{TC1}
$$

The actual ground still satisfies $T_cv_0=0$. The simpler comparison
$\bar T_c=T_0-gI\preceq T_c$ has

$$
\bar C_c=C_0-gI\succeq\delta_c I,\quad\delta_c=\delta_0-g,
\qquad C_c=\bar C_c+gq_0q_0^*,\quad K_c=K_0+gq_0p_0^*. \tag{TC2}
$$

Here the [sharper exterior](sharper-exterior.md) supplies
$\delta_0>0.0916471696633458$. Both high blocks are positive when
$\delta_c>0$. Minimizing over the same high form domain gives the
actual low Schur comparison $S_c\succeq\bar S_c$.

The saved [ground moments](low-common-action.md) and norm enclosure
give a lower bound $n_-\le\|e\|$. Orthogonality of $\Pi,D_t,Q$ yields

$$
\|e\|^2+\|D_tv_0\|^2+\|q_0\|^2=1,\qquad
r_0=\sqrt{1-n_-^2},\qquad \|D_tv_0\|,\|q_0\|\le r_0. \tag{TC3}
$$

No ground-moment integral is repeated. The directed bound is
$r_0<7.291\cdot10^{-20}$. With the saved complete caps
$\|H_0D_t\|\le\epsilon_0$, $\|K_0\|\le k_0$, use

$$
\epsilon_c=\epsilon_0+gr_0,\quad k_c=k_0+gr_0,\quad
 d_c=\epsilon_c(1+k_c/\delta_c),\quad
\gamma_c=\alpha_c-d_c,\quad\beta_c=d_c^2/\gamma_c. \tag{TC4}
$$

For $\gamma_c>0$ these bound the actual complementary low square
and its second-Schur subtraction. The actual second center has null
direction $e$. The comparison center is not assigned that null relation.

## Reuse actions and pay the new correction's residual

Keep the finite-$J_{1024}$ definition of $Z$. Its saved actions use
full Gamma and the same retained prime family. Write $G_Z=Z^*Z$,
$ZC_0=Z^*C_{0,64}Z$, $CC_0=(C_{0,64}Z)^*(C_{0,64}Z)$,
$J=(K_{0,64}E)^*Z$, $M_0=(K_{0,64}E)^*C_{0,64}Z$ and
$KK=(K_{0,64}E)^*K_{0,64}E$ for those enclosed retained blocks.
Their target shifts are exactly

$$
ZC_c=ZC_0-gG_Z,\quad
CC_c=CC_0-g(ZC_0+ZC_0^*)+g^2G_Z,\quad M_c=M_0-gJ. \tag{TC5}
$$

Choose $A_c\in\mathbb R^{4\times95}$ by rounding the midpoints of
$CC_c^{-1}M_c^*$ to exact dyadics of exponent $-40$. This is a
selection rule, not positivity evidence. Every subsequent comparison
uses that exact saved $A_c$ and interval input blocks. With
$TLL_0=E^*T_{0,64}E$ the retained trial form and residual Gram are

$$
\begin{aligned}
F_c&=TLL_0-gI-JA_c-A_c^*J^*+A_c^*ZC_cA_c,\\
G_{R,c}&=KK-M_cA_c-A_c^*M_c^*+A_c^*CC_cA_c. \tag{TC6}
\end{aligned}
$$

Let $\rho_c$ bound this new retained residual norm, and use
$z_a\ge\|ZA_c\|$, $r_s=\sqrt{1+z_a^2}$. The inherited whole-$L^2$
omitted-prime operator allowance $E_p$ pays all omitted prime powers:

$$
\epsilon_R=E_pr_s,\qquad
\eta_p=E_pr_s^2+(2\rho_c\epsilon_R+\epsilon_R^2)/\delta_c.
$$

The positive inverse-residual identity and Schur monotonicity give
the finite compression

$$
E^*S_cE\succeq E^*\bar S_cE
\succeq F_c-G_{R,c}/\delta_c-\eta_pI_{95}. \tag{TC7}
$$

This $95\times95$ inequality is not itself a comparison on all of
$PL^2$. Its exact-$e^\perp$ restriction is checked above
$\beta_c+a$, with $a=1/100$, using the accepted ground-uncertainty
and Householder transport. The complementary low bound in (TC4)
then gives the actual second-center margin $a$.

## Lift the finite comparison to the whole form

The actual residual differs from the comparison residual by

$$
R_{\rm act}=R_{\rm bar}+gq_0e^*-gq_0q_0^*ZA_c.
$$

Thus valid caps for $L_c=C_c^{-1}K_c$ are

$$
l_E=z_a+\frac{\rho_c+\epsilon_R+gr_0(1+r_0z_a)}{\delta_c},
\qquad l_t=\epsilon_c/\delta_c. \tag{TC8}
$$

The same-domain two square completions and exact ground relations
used in [the joint comparison](actual-coupling.md#preserve-all-three-blocks-in-the-norm-comparison)
give, for every $x\perp v_0$, a nonnegative vector $y$ with

$$
\|x\|^2\le\|M y\|^2,\qquad T_c[x]\ge y^*\mathcal D y,
\quad M=\begin{pmatrix}
1&0&0\\
d_c/\gamma_c&1&0\\
l_E+l_td_c/\gamma_c&l_t&1
\end{pmatrix},\quad
\mathcal D=\operatorname{diag}(a,\gamma_c,\delta_c). \tag{TC9}
$$

The bounded parameter change preserves the minimal form domain.
For the requested gap $\tau=1/1000$, check
$W=\mathcal D-\tau M^*M\succ0$ by interval LDL. If this passes,
inverse row-norm bounds $r_W\ge\|W^{-1}\|$ and
$r_M\ge\|M\|^2$ give

$$
T_c|_{v_0^\perp}\succeq
\left(\tau+\frac1{r_Wr_M}\right)I. \tag{TC10}
$$

LDL pivots are not eigenvalues. This implication controls the whole
ground-orthogonal form, rather than selected Galerkin vectors alone.

### Reuse the positive blocks when a requested gap test fails

The requested test at $\tau=1/1000$ is sufficient, not necessary for
positivity. Once the finite restriction supplies $a>0$ and the same
comparison has $\gamma_c,\delta_c>0$, (TC9) already gives the standard
norm bound

$$
T_c[x]\ge
\frac{\min\{a,\gamma_c,\delta_c\}}{\|M\|_F^2}\|x\|^2,
\qquad x\perp v_0. \tag{TC11}
$$

Indeed, $\|x\|^2\le\|My\|^2\le\|M\|_F^2\|y\|^2$, while
$y^*\mathcal D y\ge\min\{a,\gamma_c,\delta_c\}\|y\|^2$.
This reuses the existing three-block lift and the ordinary Frobenius
norm estimate; it is not a new lifting theorem or sign mechanism.

For the [saved $c=23/50$ result](target-correction-c23-50-result.json),
all 94 restricted pivot lower endpoints are positive. Its serialized
dyadic endpoints imply the exact rational comparisons

$$
\begin{gathered}
a=\frac1{100},\qquad
\delta_c>\frac{33}{5000},\qquad
\gamma_c>\frac{39}{1000},\\
\frac{d_c}{\gamma_c}<\frac{21}{10000},\qquad
l_t<\frac3{10000},\qquad
l_E+l_t\frac{d_c}{\gamma_c}<\frac{61}{20}.
\end{gathered}
$$

All entries of the lifting cap are nonnegative, so these bounds give

$$
\|M\|_F^2<
3+\left(\frac{21}{10000}\right)^2
 +\left(\frac3{10000}\right)^2
 +\left(\frac{61}{20}\right)^2
=\frac{24605009}{2000000}<\frac{25}{2}.
$$

Consequently (TC11) gives a whole-form ground-orthogonal gap greater
than $33/62500>1/2000$ at $c=23/50$. Transport through the same original
unitary identification and variance term yields

$$
 D(h)\ge\frac{921}{2000}\operatorname{Var}_\nu(h)
 =0.4605\operatorname{Var}_\nu(h)
 \qquad(h\in\mathcal F_{\min,\mathrm{even}}). \tag{TC12}
$$

This is a conditional paper corollary of the existing saved comparison,
with every analytic, numerical-supplier, ground and domain premise
retained. The rational endpoint comparisons acquire no new actions,
Grams, moments or numerical target, and do not rerun the failed
$1/1000$ test. They do not establish a cofinal estimate or Lean
certification.

## Directed results and the cofinal boundary

The [producer](target_correction.py) uses 192-bit ball arithmetic.
The two results retain exact correction coefficients, input data hashes,
new residual/restriction intervals and positive or failed pivots.
Rounded bounds below are outward, and retain the paper premises above.

| Quantity | $c=9/20$ | $c=23/50$ |
|---|---:|---:|
| High floor $\delta_c$ | $>0.01664716966$ | $>0.00664716966$ |
| Second-Schur allowance $\beta_c$ | $<2.274\cdot10^{-8}$ | $<1.678\cdot10^{-7}$ |
| Retained residual norm $\rho_c$ | $<0.00955554$ | $<0.01130434$ |
| Actual inverse coupling $l_E$ | $<1.766086$ | $<3.043432$ |
| Restricted test above $\beta_c+1/100$ | 94 positive pivots | 94 positive pivots |
| Joint test at $\tau=1/1000$ | 3 positive pivots | first pivot negative |
| Certified paper-model gap from (TC10) | $>0.00186736$ | not supplied by this test |

See [the passing result](target-correction-c9-20-result.json) and
[the failed requested joint test](target-correction-c23-50-result.json).
The latter retains its failed $1/1000$ test; the smaller positive gap in
(TC11)--(TC12) follows from its already accepted component bounds.
It does not establish operator negativity or an RH counterexample.
No old action solve, numerical integration or fixed-target matrix is
replayed by this producer.

The present exterior allowance requires $g<\delta_0<1/8$.
It cannot reach cofinal $c\uparrow1/2$ at fixed $N=64$ by the
lower bound $\delta_0-g$ alone. Losing this allowance is not losing
actual positivity. Further numerical targets do not replace the
joint estimates needed for the endpoint. The existing
[high-frequency supplier](../../../Library/Weil/fukushima2011dirichlet.md#high-frequency-coercivity-and-the-scalar-deficit),
(WF6), already supplies $N_0(\varepsilon)$: for $0<\varepsilon\le1/2$,
$c=1/2-\varepsilon$ and $N\ge N_0(\varepsilon)$, the same complete
high restriction of $T_c$ is at least $\varepsilon I/4$.
This paper supplier is reused, not a new result of the target computation.
What remains unpaid is the low Schur center and its couplings on that
same bandwidth sequence. The saved $N=64$ blocks are not data for those
other bands. The [relative window estimate](weighted-window-metric.md#the-estimate-that-would-reach-one-half)
is another sufficient route, and remains unproved. RH, the full Robin
inequality and whole-form cofinal positivity remain unresolved.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/target_correction.py
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/target_correction.py --target-c 23/50
```

The program is project-authored and uses python-flint/FLINT.
Incompatible suppliers, invalid finite endpoints or uncertified matrix
operations reject. Failure of a sufficient positivity test is recorded
with its stage and pivot, separately from execution failure.
