# Common residual and exact-ground restricted comparison

This directed paper-model comparison joins the
[actual low/mixed blocks](low-common-action.md),
[saved high blocks](high-full-action.md) and
[stable projected-ground application](stable-ground.md) at $c=3/8$.
Classical inverse-residual estimates, Householder transport and symmetric
LDL elimination are reused methods. There is no new general theorem,
Lean certification or novelty claim about those methods.

Keep $C=QTQ\ge\delta I$, $\delta=0.0383682545007734$, the exact95-column
isometry $E$, the fixed finite-$J=1024$ high columns $Z$ and the exact
saved4-by95 dyadic matrix $A$. On $u\perp e=E^*p_0$, the original
exact-ground lift simplifies to $YEu=ZAu$. All operators, vectors and
matrix entries below refer to this one common realization.

## Form the retained residual without another solve

Use the (LA4)--(LA5) retained low blocks and reconstruct the retained
high blocks from their saved $ZZ,Z^*H_Z,(QH_Z)^*(QH_Z)$:

$$
ZC_{64}=\alpha ZZ+Z^*H_Z, \tag{RS1}
$$

$$
CC_{64}=\alpha^2ZZ+\alpha[Z^*H_Z+(Z^*H_Z)^*]
 +(QH_Z)^*(QH_Z). \tag{RS2}
$$

These use the retained entries, rather than the entries already enlarged
for complete omitted primes. For $U=E-ZA$ and
$R_{64}=K_{64}-C_{64}ZA$, compute

$$
F_{64}=T_{LL}^{64}-JA-A^*J^*+A^*ZC_{64}A, \tag{RS3}
$$

$$
G_{64}=R_{64}^*R_{64}
=KK-MA-A^*M^*+A^*CC_{64}A. \tag{RS4}
$$

The finite integral intervals and their whole-line allowances enclose
the actual matrices. Symmetrization preserves the exact Hermitian
target. A maximum absolute row sum of the enclosed $G_{64}$ gives

$$
\|R_{64}\|\le\rho<0.00805805. \tag{RS5}
$$

This is an operator bound from the common residual Gram, not a sum of
independently optimized residual estimates.

## Transport all omitted primes jointly

Let $E_p$ be the saved whole-$L^2$ bound for $T-T_{64}$. Since $E$ is
low and $Z$ is high,

$$
\|U\|\le r_s=\sqrt{1+\|Z\|^2\|A\|^2}. \tag{RS6}
$$

The program bounds $\|A\|$ by its exact-dyadic Frobenius norm. The
full residual $R=QTP E-CZA$ has difference
$R-R_{64}=Q(T-T_{64})U$, so

$$
\|R-R_{64}\|\le\epsilon_R=E_pr_s,\qquad
\|R^*R-G_{64}\|\le2\rho\epsilon_R+\epsilon_R^2. \tag{RS7}
$$

Likewise $F=U^*TU$ gives $\|F-F_{64}\|\le E_pr_s^2$. The inverse-residual
identity and $C^{-1}\le\delta^{-1}I$ imply

$$
E^*SE\succeq F_{64}-\delta^{-1}G_{64}-\eta_p I=:F_{\rm lower}, \tag{RS8}
$$

$$
\eta_p=E_pr_s^2+\delta^{-1}(2\rho\epsilon_R+\epsilon_R^2)
<1.897\cdot10^{-18}. \tag{RS9}
$$

The gap belongs to the full $C$. No positivity assumption on $C_{64}$
is needed for this lower comparison. Prime omissions remain separate
from local sample errors. The comparison of (RS8) with the actual lifted
center is used only on $e^\perp$.

## Transport the exact direction into the comparison

Let $e$ range over its saved95 component intervals. Set

$$
v=e+\|e\|e_0,\qquad H_e=I-2vv^*/\|v\|^2. \tag{RS10}
$$

The denominator is bounded away from zero. For the true direction,
$H_e e=-\|e\|e_0$ and $H_e$ is orthogonal. Its columns1 through94 form
an exact isometry $V$ onto $e^\perp$. Every component uncertainty enters
the interval evaluation of $V^*F_{\rm lower}V$.

Let $\beta$ be the saved upper bound for $d^2/(\alpha-d)$ from the
stable-ground supplier. The [matrix program](restricted_schur.py) checks
the stronger comparison

$$
V^*F_{\rm lower}V-(\beta+1/10)I\succ0. \tag{RS11}
$$

All94 pivots of its interval LDL elimination have positive lower
endpoints; the smallest is greater than0.020339. These pivots are not
eigenvalues. Interval multiplication is used for squares of coefficients
whose balls can cross zero. The factorization encloses the exact real
symmetric matrix even though its interval entries have shared sources.
The saved [result](restricted-schur-result.json) contains both common
residual and restricted lower entry intervals, all pivot intervals,
exact direction/norm enclosures and separate full-prime allowances.

Thus the directed computation checks a restricted margin greater than
the required $\beta$, under the stated paper operator and analytic
supplier premises. The stable-ground Schur argument then supplies the
fixed-$c=3/8$ positivity implication for that same model. This conditional
paper-model implication is not a Lean-certified theorem. Positivity
cofinally as $c\uparrow1/2$, RH and the full Robin inequality remain
unresolved.

The [quantified two-Schur transport](threshold-transport.md) consumes this
same comparison to check a conditional positive parameter margin at
$c=0.39$ without another action solve. Its bounded range supplies no
cofinality, Lean, Robin or RH certification.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/restricted_schur.py
```

The project-authored program uses python-flint/FLINT. It reads the saved
actual actions without repeating their generation or the coefficient
selection solve. Source hashes and semantic parameter guards identify
the common realization. Valid supplier estimates remain premises; their
truth is not established by a successful JSON parse or LDL computation.

The [finite-core weighted residual gain](weighted-residual-core.md)
reuses $R_{64}$, its whole-line Gram and this exact ground frame. It
integrates only the nonnegative core correction to the scalar residual
allowance, preserving the baseline and trial-form prime errors. All
restricted cross entries and new integration/input errors are retained.
The existing LDL and global comparison are not rerun or superseded.
