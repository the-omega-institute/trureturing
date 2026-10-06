# Actual coupling norms and a joint gap at c=0.42

The [two-Schur transport](threshold-transport.md) controls the whole low
space by a single shear bound. The saved
[common low Gram](low-common-action.md) allows a smaller coupling norm,
and the [actual Z Gram](local-z-gram.md) bounds the composition $ZA$
directly. Keeping the polynomial center, low tail and high remainder
separate gives a stronger joint comparison for the same operator.
These are applications of existing Gram, Schur, quotient-distance and
interval LDL methods. No action, integration grid, coefficient-selection
solve or previous restricted matrix is recomputed.

## Replace the analytic coupling majorant by its saved actual Gram

Use $\Pi=EE^*$ and $D_t=I-\Pi$ on $PL^2$. The same full operator
has $K=QHP$ and the supplied analytic tail obeys
$\|HD_t\|\le\epsilon_{94}$. If $G_{K,64}$ is the saved Gram of
the retained $K_{64}E$ and $E_p$ is the complete omitted-prime
operator error, then

$$
\begin{aligned}
k_E&=\sqrt{\max_i\sum_j|(G_{K,64})_{ij}|}+E_p,\\
\|KE\|&\le k_E,\qquad
\|K\|\le k=\sqrt{k_E^2+\epsilon_{94}^2}. \tag{AC1}
\end{aligned}
$$

The last step applies uniform bounds to orthogonal components of one
actual input, using Cauchy--Schwarz. It does not require separate
maximizers to occur together. All prime powers remain included.

With the [stronger high gap](sharper-exterior.md) $C\ge\delta I$,
the unchanged Schur operator $S=\alpha I+PHP-K^*C^{-1}K$ satisfies

$$
\|(S-\alpha I)D_t\|\le d=
\epsilon_{94}(1+k/\delta),\quad
\gamma=\alpha-d,\quad \beta=d^2/\gamma. \tag{AC2}
$$

Here $\alpha=1/8$. The exact finite second Schur center $R_l$ is
unchanged; only its estimated tail allowance improves. The
[accepted comparison on the true ground complement](restricted-schur.md)
gives $V^*F_{\rm lower}V>(\beta_{\rm old}+1/10)I$ and
$F_{\rm lower}\preceq E^*SE$. Paying the smaller allowance yields

$$
R_l|_{e^\perp}\succeq aI,\qquad
a=1/10+\beta_{\rm old}-\beta. \tag{AC3}
$$

$\beta_{\rm old}$ is the exact constant used in that checked comparison,
not an unknown true tail norm. The actual $R_l e=0$ relation is retained.

## Bound the actual composition ZA

For the same exact dyadic $A$ and positive $G_Z=Z^*Z$, the directed
four-dimensional comparisons give

$$
G_Z\succ0,\qquad
\frac{49}{100}G_Z^{-1}-AA^*\succ0. \tag{AC4}
$$

Congruence by $G_Z^{1/2}$ therefore bounds $\|ZA\|\le7/10$.
This uses the actual Gram of the unchanged finite-$J_{1024}$ family.
It does not replace any old conservative full-prime or residual error.
With $L=C^{-1}K$, retain those errors to obtain

$$
\|LE\|\le l_E=7/10+(\rho+\epsilon_R)/\delta,
\qquad \|LD_t\|\le l_t=\epsilon_{94}/\delta. \tag{AC5}
$$

## Preserve all three blocks in the norm comparison

The two exact square completions and ground relations used in (TT3)
and (TT8) give

$$
x=t v_0+(Eu,w,z_h-L(Eu+w)),\qquad
w=z_l-D_l^{-1}B_lu,\qquad u\perp e. \tag{AC6}
$$

For $x\perp v_0$, distance to the exact ground line is $\|x\|$,
bounded by the norm of the displayed representative. Define the
nonnegative scalar vector $y=(\|u\|,\|z_l\|,\|z_h\|)^T$ and

$$
M=\begin{pmatrix}
1&0&0\\
b&1&0\\
l_E+l_tb&l_t&1
\end{pmatrix},\quad b=d/\gamma,\qquad
\mathcal D=\operatorname{diag}(a,\gamma,\delta). \tag{AC7}
$$

The same maps in (AC6), together with their uniform bounds, give

$$
\|x\|^2\le\|My\|^2,\qquad
T(c_0)[x]\ge y^*\mathcal D y. \tag{AC8}
$$

Thus a positive comparison $\mathcal D-gM^*M\succ0$ controls the
whole original ground-orthogonal form, not just three selected trial
vectors. The inherited bounded inverse couplings preserve the minimal
form domains as in (TT8)--(TT9).

For $g=9/200$, all three interval LDL pivots are positive. To quantify
the excess let

$$
r_C=\max_i\sum_j|[(\mathcal D-gM^*M)^{-1}]_{ij}|,
\quad r_M=\max_i\sum_j|(M^*M)_{ij}|,\quad
\varepsilon=1/(r_Cr_M). \tag{AC9}
$$

Positive Hermitian inverse and row-norm bounds imply
$\mathcal D-gM^*M\succeq r_C^{-1}I$ and $\|M\|^2\le r_M$.
Combining them in (AC8), and using the exact same-ground parameter
dependence, gives

$$
T(c_0)|_{v_0^\perp}\succeq(g+\varepsilon)I,\qquad
T(21/50)|_{v_0^\perp}\succeq\varepsilon I. \tag{AC10}
$$

## Directed result and its limits

The [program](actual_coupling.py) consumes existing saved inputs.
Its [result](actual-coupling-result.json) gives

| Quantity | Directed bound |
|---|---:|
| Complete $\|K\|$ | $<0.311006$ |
| Low-tail allowance $d$ | $<7.524\cdot10^{-6}$ |
| Second-Schur allowance $\beta$ | $<4.529\cdot10^{-10}$ |
| Finite-center margin $a$ | $>0.1046608667$ |
| $\|LE\|$ | $<0.787925$ |
| Global gap at $c_0=3/8$ | $>0.04612575$ |
| Ground-orthogonal gap at $c=0.42$ | $>0.00112575$ |

These implications require the same paper operator, exact ground,
minimal form domain, analytic suppliers and correctly enclosed saved
Grams. The inverse tests operate on the actual four-column Gram; the
three-dimensional norm comparison has the whole-form lifting (AC8).
LDL pivots are not eigenvalues. This remains a bounded parameter range,
without a cofinal $c\uparrow1/2$, RH, full Robin or Lean certificate.
No new general method or literature priority is claimed.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/actual_coupling.py
```

The program is project-authored and uses python-flint/FLINT. Incompatible
suppliers or uncertified positive inverse caps reject. If a different
target fails the final sufficient comparison, the output records the
failed pivot and makes no operator-negativity or RH-counterexample claim.
