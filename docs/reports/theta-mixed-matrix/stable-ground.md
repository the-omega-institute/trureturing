# Stable projected-ground application

This paper-model application reuses the one-sided polynomial tail in
[sharp-center.md](sharp-center.md), the exact kernel relation and the
[ground norm supplier](ground-residual.md). Classical Schur elimination
is the method; no new general theorem or Lean certification is claimed.

Use the canonical sharp-center definitions, SC2, SC7 and SC12, with
$\alpha=1/8$, $P=\mathbf1_{|\xi|<64}$ and $\dim E=95$. Inside
the exact low-band Hilbert space let $S=\alpha I+L$ be bounded and
self-adjoint, $Sp_0=0$, and let $\Pi=EE^*$ be the degree-94 polynomial
projection. The existing column proof gives
$\|L(I-\Pi)\|\le d=e_{94}/2<\alpha$, not just the ground-augmented
two-sided remainder. Self-adjointness gives
$\|(I-\Pi)L\|\le d$.

Consequently the exact ground relation, together with the operator tail,
supplies

$$
\|(I-\Pi)p_0\|
=\alpha^{-1}\|(I-\Pi)Lp_0\|
\le(d/\alpha)\|p_0\|.
$$

Orthogonality yields

$$
\|E^*p_0\|=\|\Pi p_0\|
\ge\sqrt{1-(d/\alpha)^2}\,\|p_0\|>0.
$$

This uses a joint exact operator/kernel relation. The norm of $p_0$
alone does not imply a nonzero polynomial projection. The existing
ground-residual lower bound for $\|p_0\|$ can now be transported to an
explicit lower bound for $e=E^*p_0$, without estimating additional
Fourier ground moments.

On the complementary low-band subspace define
$D=(I-\Pi)S(I-\Pi)$. Its bounded self-adjoint restriction obeys
$D\ge(\alpha-d)I>0$. The off-diagonal
$(I-\Pi)SE=(I-\Pi)LE$ has norm at most $d$. Reuse the same positive
block elimination from SC2. Its 95-dimensional center is

$$
R=E^*SE-E^*S(I-\Pi)D^{-1}(I-\Pi)SE.
$$

The complementary ground equation gives
$(I-\Pi)p_0=-D^{-1}(I-\Pi)SEe$, hence $Re=0$ exactly.
This does not say $E^*SEe=0$.

For $u\perp e$,

$$
\langle Ru,u\rangle
\ge\langle E^*SEu,u\rangle
-\frac{d^2}{\alpha-d}\|u\|^2.
$$

Thus a certified lower bound on $E^*SE$ restricted to $e^\perp$
strictly greater than $d^2/(\alpha-d)$ would certify positivity of
$R$ away from its exact nullvector. Completing the complementary
square would give $S\succeq0$. This is an application of classical
Schur elimination, not a new inverse-residual theorem.

At $\alpha=1/8$ and the saved $e_{94}$, the allowance is about
$0.00466$. It is not $0.000466$. Its value and the projected-ground
lower bound are computed from the already supplied exact dyadic
endpoints. The [actual low/mixed computation](low-common-action.md) encloses
the exact direction and retained entries; the
[restricted comparison](restricted-schur.md) transports them into the
joint matrix check under its paper supplier premises.
Floating Householder deflation or a numerical near-zero eigenvalue does
not provide that certificate.


The [directed coefficient program](stable_ground_coefficients.py) reads
the saved exact dyadic endpoints, preserves their input hashes, and
produces [stable-ground-result.json](stable-ground-result.json). Rounded
outward, its model coefficients are

| Quantity | Directed bound |
|---|---|
| $\|e\|$ | $>0.9844676120552339$ |
| $\|e\|^{-1}$ | $<1.015777449409778$ |
| $\alpha-d$ | $>0.1030809116118886$ |
| $d^2/(\alpha-d)$ | $<0.004660867160108$ |

A certified restricted matrix lower bound strictly greater than the last
upper bound is sufficient. The actual projected-ground direction and
the common restricted matrix remain uncomputed by this program. On
$u\perp e$, the exact lift (HT2) simplifies to $YEu=ZAu$, because
$\langle p_0,Eu\rangle=\langle e,u\rangle=0$. This identifies the
consumer of the four saved correctors without certifying their Gram.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/stable_ground_coefficients.py
```

The program is project-authored and uses python-flint/FLINT for directed
arithmetic. It evaluates these coefficients, not the retained integrals,
the full Robin inequality, RH or cofinal $c\uparrow1/2$ positivity.
