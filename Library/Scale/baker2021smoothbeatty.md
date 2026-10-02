---
bibkey: baker2021smoothbeatty
authors: Roger Baker
year: 2021
title: Smooth numbers in Beatty sequences
doi: 10.4064/aa210322-22-6
url: https://arxiv.org/abs/2102.00303v1
claim: "Theorem 1 counts smooth Beatty values above a log-power-three smoothness threshold; complete CA layer support prevents fixed primorial peeling from reaching that range, while a classical Dirichlet application diagnoses weaker sampling conditions."
strata_touched: []
license: citation-only
triage: anchor
---

# Smooth Beatty suppliers at the actual CA scale

Roger Baker, *Smooth numbers in Beatty sequences*, Acta Arithmetica
200 (2021), 429–438,
[DOI:10.4064/aa210322-22-6](https://doi.org/10.4064/aa210322-22-6).
The publisher record and the primary text
[arXiv:2102.00303v1](https://arxiv.org/html/2102.00303v1), §1,
Theorem 1 and equation (1.1), were inspected. The full analytic proof
was not independently verified. The following applications reuse that
statement and classical inputs; they introduce no new smooth-number
theorem, originality claim or Lean verification.

## The published range and the exact unit-bit population

For fixed finite-type irrational $\theta>1$ and fixed $\beta\ge0$, set

$$
\mathcal B_{\theta,\beta}(X)
=\{\lfloor\theta k+\beta\rfloor:1\le k\le X\}.
$$

For every fixed $\varepsilon>0$, Theorem 1 gives

$$
\#\{m\in\mathcal B_{\theta,\beta}(X):P^+(m)\le y\}
=\theta^{-1}\Psi(\theta X,y)(1+o(1))
$$

as $X\to\infty$, uniformly for
$(\log X)^{3+\varepsilon}\le y\le X$. Here $\Psi(T,y)$ counts
positive $y$-smooth integers at most $T$. The theorem fixes the slope;
it is a counting asymptotic, not a pointwise bound for an optimizing integer.

The existing
[canonical FIB unit-bit interface](../ArithSums/guloglunevans2008beatty.md)
identifies $h(n)=1$ with $n=\lfloor k\varphi^2-1\rfloor$, $k\ge1$.
Its negative offset must not be inserted directly into Baker's
nonnegative-offset statement. Instead, for $k\ge2$, put $j=k-1$:

$$
\lfloor k\varphi^2-1\rfloor
=\lfloor j\varphi^2+\varphi\rfloor,\qquad j\ge1.
$$

Thus $(\theta,\beta)=(\varphi^2,\varphi)$ gives the same unit-bit
population except for its first value, 1. This is an exact parameter
map to the published counting theorem. For an actual CA candidate
$n\asymp X$, however, the existing support asymptotic is
$P^+(n)\sim\log n\asymp\log X$. Its smoothness scale is outside the
stated range. Enlarging $y$ to meet that range counts a larger
population and supplies no restriction back to the actual CA test set.

## Peeling complete layers does not repair the smoothness scale

Use the classical CA exponents, including every intermediate tied
maximizer, and write $n=\prod_{p\le P}p^{e_p}$ with $P=P^+(n)$.
For a fixed nonnegative integer $j$, remove the first $j$ complete
exponent layers and retain the exact quotient

$$
v_j=\prod_{p\le P}p^{\max(e_p-j,0)}.
$$

By the existing nonincreasing-exponent property, its nonempty support
is the complete prime prefix through $y_j=P^+(v_j)$. Hence

$$
y_j\#\mid v_j,\qquad\vartheta(y_j)\le\log v_j,
\qquad y_j\le(1+o(1))\log v_j
$$

when $y_j\to\infty$, using ordinary PNT. For actual CA
sequences with $n\to\infty$ and fixed $j$, the classical fixed-layer threshold gives
$y_j\to\infty$; see the existing (T11) application in the
[CA mask note](pollack2017nonresidues.md). At a natural new population
scale $X_j\asymp v_j$, every fixed $C>1$ therefore has

$$
y_j<(\log X_j)^C
$$

eventually. In particular, removing any fixed number of complete
layers still does not enter Baker's $C=3+\varepsilon$ range.
No assertion that $v_j$ itself is CA is needed or made.

For one removed layer, $R=P\#$ and $v=n/R$ also give a same-source
incidence map. In the actual $h=1$ branch, for an eligible $p\ne2,5$
with even $e_p>0$, put $d_p=p^{e_p/2}$. Then $d_p\mid v$ and the
existing lift $c=2\lfloor n\varphi\rfloor-n-1$ gives

$$
p^{e_p/2}\mid c
\iff
\left\{\frac{v}{d_p}(R\varphi)\right\}\in I_{d_p},\qquad
I_d=\left(\frac{d+1+2a}{2d},\frac{d+1+4a}{2d}\right),
\quad a=2-\varphi.
$$

Indeed, $d_p\mid n$ is odd and at least three. Writing
$n=d_pt$, $x=\{t\varphi\}$ and $k=\lfloor d_px\rfloor$ gives
$c\equiv2k-1\pmod {d_p}$; the unique possible value is
$k=(d_p+1)/2$. Intersect with the existing unit window
$a<\{n\varphi\}<2a$. The empty-product value $d=1$ is excluded,
and prime five retains its separate rule. These are the actual
same-integer depth tests, without an independence assumption.
The new slope $R\varphi$ also varies with $P$, so Baker's fixed-slope
statement cannot silently provide its uniform error.

## A controlled comparator diagnoses weaker sampling hypotheses

Complete support and the correct size scale alone do not force
rotation equidistribution. The classical finite Dirichlet theorem
supplies, for every real $\alpha$ and integer $Q\ge1$, an integer
$1\le t\le Q$ with $\|t\alpha\|\le1/(Q+1)$; no new approximation
proof is needed. A matching upstream statement is
`Real.exists_nat_abs_mul_sub_round_le` in
[the pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/DiophantineApproximation/Basic.lean#L135).
It was inspected, not compiled here.

Take a sequence of actual CA integers $C_i\to\infty$, so that
$P_i=P^+(C_i)\to\infty$. Put $Q_i=\lfloor\log P_i\rfloor$ and
discard the finite initial range with $Q_i<1$. Apply the classical
input to $\alpha=C_i\varphi$. The resulting $N_i=t_iC_i$ satisfy

$$
\begin{gathered}
\operatorname{rad}(N_i)=\operatorname{rad}(C_i)=P_i\#,
\qquad P^+(N_i)=P_i,\\
\log N_i=\log C_i+O(\log\log P_i)\sim P_i,\\
v_p(N_i)=v_p(C_i)\quad(p>Q_i),\qquad
\|N_i\varphi\|\le1/(Q_i+1)\longrightarrow0.
\end{gathered}
$$

Every prime factor of $t_i\le Q_i<P_i$ already belongs to $C_i$.
Thus this enlarged population retains initial support, size scale and
all exponents above $\log P_i$, while the chosen phases concentrate
at zero on the circle. The $N_i$ are not asserted to be CA or to have
nonincreasing exponents. In fact their unit bits are eventually zero:
a shrinking circular neighborhood of zero misses the fixed interval
$(a,2a)$ for unit bit one. This is a counterexample to the stated
weaker sampling premise, not to a hypothesis restricted to $h=1$ CA
integers or to Robin.

The comparator also preserves the Robin response to a finer scale
than the existing square-root margin. Choose an optimizing CA price
$\epsilon_i$ for $C_i$. Comparison with $C_i/P_i$ bounds it by

$$
0<\epsilon_i\le\frac{\log(1+1/P_i)}{\log P_i}
=O\!\left(\frac1{P_i\log P_i}\right):
$$

the removed last local factor has ratio at most the first gain
$1+1/P_i$. This price bound also holds at tied choices; the existing
[Nicolas source note](../ArithSums/nicolas2025comparison.md) records
the classical optimizing objective. Monotonicity of each finite Euler
factor under divisibility gives $Z(N_i)\ge Z(C_i)$.
Optimality and $t_i\le Q_i$ then imply

$$
0\le\operatorname{Ben}_{C_i,\epsilon_i}(N_i)
\le\epsilon_i\log t_i,\qquad
0\le\log\frac{Z(N_i)}{Z(C_i)}\le\epsilon_i\log t_i.
$$

Set $\mathcal R(m)=Z(m)/(e^\gamma\log\log m)$. Since the derivative
of $\log\log L$ is $1/(L\log L)$, the same comparison gives

$$
\left|\log\mathcal R(N_i)-\log\mathcal R(C_i)\right|
=O\!\left(\frac{\log\log P_i}{P_i\log P_i}\right)
=o\!\left(\frac1{\sqrt{P_i}\log P_i}\right).
$$

These are two coupled integers, possibly equal, linked by the
proved divisibility and price comparison. The construction does not assign a sign to
either Robin margin, produce a Robin violation, or replace the need
to estimate the actual CA candidate. If the starting $C_i$ have $h=1$, their comparators eventually have
$h=0$; no infinite such CA subsequence is asserted. Thus a small-benefit
relaxation of an $h=1$ optimizing condition requires its own phase
transfer instead of assuming that the unit window is preserved.
Neither this diagnostic nor layer removal supplies the missing
[same-source signed prime-error estimate](../ArithSums/nicolas2025comparison.md).
