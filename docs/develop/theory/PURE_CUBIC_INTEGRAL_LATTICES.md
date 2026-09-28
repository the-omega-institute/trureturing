# Integral lattices in pure cubic fields

This volume records an integral lattice calculation used in Section 11 of
`GOLDEN_CUBIC_BLOCK_PRIME_PERIODS.md`. The displayed discriminants belong to
the specified lattices; identifying the full ring of integers requires an
additional maximality argument.

## 1. The cubic lattice calculation

**Theorem 1.1 (integral cubic lattices).** Let $m,n,c$ be positive integers,
let $a,k$ be integers, and let $v\in\{-1,1\}$ satisfy

$$
c^3mn^2=1+9a,\qquad c^2n=v+3k.
$$

Suppose $X^3-mn^2$ is irreducible over $\mathbb Q$. In
$K=\mathbb Q(\alpha)$, with $\alpha^3=mn^2$, put

$$
\beta=\frac{\alpha^2}{n},\qquad
\gamma=\frac{1+c\alpha+v\beta}{3}.
$$

Then $\alpha$, $\beta$, and $\gamma$ are algebraic integers. Both
$(1,\alpha,\beta)$ and $(1,\alpha,\gamma)$ are rational bases of $K$,
with trace-form discriminants

$$
\operatorname{disc}(1,\alpha,\beta)=-27(mn)^2,\qquad
\operatorname{disc}(1,\alpha,\gamma)=-3(mn)^2.
$$

Proof. The equations $\alpha^3=mn^2$ and $\beta^3=m^2n$ make
$\alpha$ and $\beta$ integral. Write $\theta=c\alpha$ and
$\eta=(1+\theta+\theta^2)/3$. Since $\theta^3=1+9a$, direct reduction
shows that $\eta$ satisfies the monic polynomial
$T^3-T^2-3aT-3a^2$, so it is integral. The relation
$c^2n=v+3k$ gives $\gamma=\eta-k\beta$, hence $\gamma$ is integral.
The power basis $(1,\alpha,\alpha^2)$ has discriminant
$-27(mn^2)^2$. The changes from this basis to
$(1,\alpha,\beta)$ and then to $(1,\alpha,\gamma)$ have determinants
$1/n$ and $v/3$ respectively. Both are nonzero, and the two
discriminants follow from the square-of-determinant rule and $v^2=1$.

## 2. Boundary and source

Theorem 1.1 does not assert that either lattice is the full ring of
integers. The primes dividing its residual index, and the normalization
index of the order in Section 11, require separate local arguments.
The trace-form change-of-basis rule and the power-basis discriminant
formula are the pinned Mathlib results
`Algebra.discr_of_matrix_vecMul` and `Algebra.discr_powerBasis_eq_norm`.

## 追加锚（本行以下为增补区）
