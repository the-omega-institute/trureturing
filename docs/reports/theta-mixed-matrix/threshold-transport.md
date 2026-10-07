# Quantified Schur gaps and parameter transport

This paper-model application consumes the
[checked exact-ground comparison](restricted-schur.md) and existing
[polynomial tail supplier](sharp-center.md). It quantifies the two
Schur completions to transport the same model from $c_0=3/8$ to
$c=39/100$. Operator-norm shear bounds and bounded self-adjoint
perturbation are existing methods. No new action grid, coefficient solve,
general theorem or Lean certification is supplied.

## Convert the finite comparison into a whole-low-space gap

Use the [stable-ground decomposition](stable-ground.md), with
$\Pi=EE^*$, $D_l=(I-\Pi)S(I-\Pi)$, $B_l=(I-\Pi)SE$ and its exact
finite Schur center $R_l$. The supplied bounds are

$$
D_l\ge\gamma I,\quad \gamma=\alpha-d>0,\quad
\|B_l\|\le d,\quad R_l e=0,\quad
R_l|_{e^\perp}\ge aI,\quad a=1/10. \tag{TT1}
$$

The last bound follows from the restricted lower comparison and its
paid second-Schur allowance. It is a bound on the actual finite center,
not on an approximate near-null direction.

For $b\ge0$ put

$$
\tau(b)=\frac{\sqrt{4+b^2}+b}{2}. \tag{TT2}
$$

This bounds the norm of the two-block shear with off-diagonal norm at
most $b$. Write the coefficient of a low vector as $te+u_\perp$ and
put $z=w+D_l^{-1}B_l(te+u_\perp)$. The exact ground relation gives

$$
p=tp_0+(Eu_\perp,z-D_l^{-1}B_lu_\perp). \tag{TT3}
$$

Here the last pair uses the orthogonal polynomial/tail decomposition.
For $p\perp p_0$, its distance to the ground line equals $\|p\|$ and
is at most the norm of the displayed representative. Completing the
low square therefore gives

$$
S|_{p_0^\perp}\ge g_S I,\qquad
g_S=\frac{\min(a,\gamma)}{\tau(d/\gamma)^2}. \tag{TT4}
$$

## Bound the common inverse coupling

Let $L=C^{-1}K$ on the whole low space. The common residual gives
$LE=ZA+C^{-1}R$, hence

$$
\|LE\|\le l_E=\|Z\|\|A\|+
\delta^{-1}(\rho+\epsilon_R). \tag{TT5}
$$

On the polynomial complement, (SC12) supplies

$$
\|HP(I-\Pi)\|\le\varepsilon_{94}
=32M_{\varrho}(2/3)^{94},\qquad \varrho=3/2, \tag{TT6}
$$

so $\|L(I-\Pi)\|\le l_t=\varepsilon_{94}/\delta$. Compute (TT6)
directly from the saved upper bound for $M_{\varrho}$; dividing two
rounded upper bounds for the Schur remainder and center norm would
not justify an upper bound for $\varepsilon_{94}$.

The input components are orthogonal. Applying the two uniform bounds
to the same actual $L$ and Cauchy--Schwarz gives

$$
\|L\|\le l=\sqrt{l_E^2+l_t^2}. \tag{TT7}
$$

This uses simultaneous bounds, without asserting that separate
maximizers are jointly attained.

## Complete the high square and move the parameter

For $x\perp v_0$, write $p=tp_0+p_\perp$ and $z=q+Lp$. The exact
high ground relation gives

$$
x=tv_0+(p_\perp,z-Lp_\perp). \tag{TT8}
$$

Distance to the unit ground line and the high square imply

$$
T(c_0)|_{v_0^\perp}\ge gI,\qquad
g=\frac{\min(g_S,\delta)}{\tau(l)^2}. \tag{TT9}
$$

These completions take place on the inherited minimal form domain.
The bounded inverse coupling sends low vectors into $D(C)$, so the
high shear preserves its form domain. No extra application of an
unbounded operator to an arbitrary residual is used.

The exact parameter dependence of (SC1), with the same unit ground
and operator family, is

$$
T(c)=T(c_0)-(c-c_0)(I-|v_0\rangle\langle v_0|). \tag{TT10}
$$

Consequently the supplied comparison transports by

$$
T(c)|_{v_0^\perp}\ge[g-(c-c_0)]I. \tag{TT11}
$$

The [directed scalar program](threshold_transport.py) reads the existing
dyadic bounds only. Its [result](threshold-transport-result.json) gives

| Quantity | Directed bound |
|---|---|
| $g_S$ | $>0.08087697$ |
| $\varepsilon_{94}$ | $<1.712476\cdot10^{-6}$ |
| $\|C^{-1}K\|$ | $<0.933132$ |
| $g$ at $c_0=3/8$ | $>0.01556480$ |
| Ground-orthogonal gap at $c=39/100$ | $>0.00056480$ |

Under the stated paper operator, tail, ground and numerical supplier
premises, this verifies a positive parameter-transport margin through
$c=0.39$. The zero ground direction remains exact. This bounded
parameter interval is not cofinal as $c\uparrow1/2$; RH and the full
Robin inequality remain unresolved. No Lean certification is claimed.

The [sharper exterior supplier](sharper-exterior.md) improves the high
coercivity input for this same operator. The optional
`--high-gap-supplier` argument transports with that explicitly supplied
bound while retaining the existing conservative low and residual
allowances. It does not change the default $c=0.39$ calculation.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/threshold_transport.py
```

The program is project-authored and uses python-flint/FLINT. Valid saved
suppliers can be reused directly. A failed scalar transport check for
another parameter would show insufficiency of this bound, not a
negative direction or a counterexample to the original criterion.
